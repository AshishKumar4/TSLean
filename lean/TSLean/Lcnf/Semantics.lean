import Lean.Compiler.LCNF.Basic
import Std.Data.HashMap

/-!
# Big-step semantics of mono-phase LCNF

The source side of the LCNF → TypeScript lowering. It is written directly over Lean's own
`Lean.Compiler.LCNF.Code .pure`, so the object being compiled and the object being given a meaning
are the same datatype (plan, *Measured facts*; prototype `/tmp/lcnf-advisory/p15_bigstep.lean`).

* **Total.** Every function is structurally recursive on a fuel counter. Fuel bounds the height of
  the derivation (each `let`, `jmp`, `cases`, call and application consumes one unit).
* **Three outcomes.** A run ends in a value, in `Stop.exhausted` (fuel ran out, the resource bound
  the refinement statement carries as a typed outcome) or in `Stop.fault` (the program reached
  `unreach`, a missing alternative, or a form outside the supported set).
* **Untyped values.** No mono type is consulted. Constructor values keep every field after the
  inductive parameters, relevant or not; representation decisions belong to the lowering.
* **Application follows Lean's `pap` semantics.** A constant or closure applied to fewer arguments
  than its arity is a closure; exactly its arity runs it; more runs it on the first `arity`
  arguments and applies the result to the rest.
-/

namespace TSLean.Lcnf.Semantics

open Lean Lean.Compiler.LCNF

/-- Runtime values of the semantics. -/
inductive V where
  | nat (n : Nat)
  | str (s : String)
  | ctor (name : Name) (fields : Array V)
  | erased
  /-- A closure: a constant (code declaration, constructor or primitive) and the arguments it has
  received so far. Its arity is the constant's arity, looked up in the program. -/
  | clo (f : Name) (args : Array V)
  deriving Inhabited, Repr, BEq

/-- Why a run stopped without a value. -/
inductive Stop where
  | exhausted
  | fault (msg : String)
  deriving Inhabited, Repr, BEq

abbrev Result := Except Stop V

/-- What a constant name denotes to the semantics. -/
inductive Const where
  /-- A code declaration: its parameters and body. -/
  | code (params : Array (Param .pure)) (body : Code .pure)
  /-- A constructor: inductive parameters, then fields. -/
  | ctor (numParams numFields : Nat)
  /-- An `@[extern]` leaf with a primitive in `prim`. -/
  | prim (arity : Nat)

def Const.arity : Const → Nat
  | .code ps _ => ps.size
  | .ctor p f => p + f
  | .prim a => a

/-- The program: every constant the run may reach. -/
structure Program where
  consts : Std.HashMap Name Const := {}

def boolV (b : Bool) : V := .ctor (if b then ``Bool.true else ``Bool.false) #[]

/-- The primitives of the vertical slice, each Lean's own definition of the `@[extern]` leaf.
`Nat.sub` truncates, as `Nat.sub` does. -/
def primArity : Name → Option Nat
  | ``Nat.add | ``Nat.sub | ``Nat.mul | ``Nat.decEq | ``Nat.decLt => some 2
  | _ => none

def prim (n : Name) (xs : Array V) : Result :=
  match n, xs with
  | ``Nat.add, #[.nat a, .nat b] => pure (.nat (a + b))
  | ``Nat.sub, #[.nat a, .nat b] => pure (.nat (a - b))
  | ``Nat.mul, #[.nat a, .nat b] => pure (.nat (a * b))
  | ``Nat.decEq, #[.nat a, .nat b] => pure (boolV (a == b))
  | ``Nat.decLt, #[.nat a, .nat b] => pure (boolV (decide (a < b)))
  | _, _ => throw (.fault s!"primitive {n} applied to {xs.size} unsupported arguments")

/-- Local environment: values of free variables, and the join points in scope. -/
structure Env where
  vals : Std.HashMap FVarId V := {}
  jps : Std.HashMap FVarId (FunDecl .pure) := {}

def arg (env : Env) : Arg .pure → Result
  | .erased | .type .. => pure .erased
  | .fvar x => match env.vals[x]? with
    | some v => pure v
    | none => throw (.fault s!"unbound variable {x.name}")

def args (env : Env) (as : Array (Arg .pure)) : Except Stop (Array V) := as.mapM (arg env)

def var (env : Env) (x : FVarId) : Result := arg env (.fvar x)

def bind (vals : Std.HashMap FVarId V) (ps : Array (Param .pure)) (vs : Array V) :
    Std.HashMap FVarId V :=
  (ps.zip vs).foldl (fun m (p, v) => m.insert p.fvarId v) vals

def findAlt (alts : Array (Alt .pure)) (ctor : Name) : Option (Alt .pure) :=
  match alts.find? (fun a => match a with | .alt n _ _ _ => n == ctor | _ => false) with
  | some a => some a
  | none => alts.find? (fun a => a matches .default _)

mutual
/-- Evaluate a code block. -/
def evalCode (P : Program) : Nat → Env → Code .pure → Result
  | 0, _, _ => throw .exhausted
  | fuel + 1, env, c =>
    match c with
    | .return x => var env x
    | .unreach _ => throw (.fault "unreachable code reached")
    | .jp d k => evalCode P fuel { env with jps := env.jps.insert d.fvarId d } k
    | .jmp j as => do
      let some d := env.jps[j]? | throw (.fault s!"unknown join point {j.name}")
      let vs ← args env as
      if vs.size != d.params.size then throw (.fault "join point arity mismatch")
      evalCode P fuel { env with vals := bind env.vals d.params vs } d.value
    | .cases cs => do
      match ← var env cs.discr with
      | .ctor name fields =>
        match findAlt cs.alts name with
        | some (.alt _ ps k _) =>
          if ps.size != fields.size then throw (.fault s!"alternative {name} binds {ps.size} of {fields.size} fields")
          evalCode P fuel { env with vals := bind env.vals ps fields } k
        | some (.default k) => evalCode P fuel env k
        | _ => throw (.fault s!"no alternative for {name}")
      | _ => throw (.fault s!"cases on a non-constructor value ({cs.typeName})")
    | .let d k => do
      let v ← match d.value with
        | .lit (.nat n) => pure (.nat n)
        | .lit (.str s) => pure (.str s)
        | .lit _ => throw (.fault "scalar literal outside the slice's primitive set")
        | .erased => pure .erased
        | .proj .. => throw (.fault "proj is not a mono form")
        | .fvar f #[] => var env f
        | .fvar f as => do applyV P fuel (← var env f) (← args env as)
        | .const n _ as => do callConst P fuel n (← args env as)
      evalCode P fuel { env with vals := env.vals.insert d.fvarId v } k
    | .fun .. => throw (.fault "local function is not a mono form")
    | _ => throw (.fault "impure-only construct")
/-- Apply a constant to arguments, following `pap` semantics. -/
def callConst (P : Program) : Nat → Name → Array V → Result
  | 0, _, _ => throw .exhausted
  | fuel + 1, n, xs =>
    match P.consts[n]? with
    | none => throw (.fault s!"unknown constant {n}")
    | some c =>
      let a := c.arity
      if xs.size < a then pure (.clo n xs)
      else if xs.size == a then enter P fuel n c xs
      else do
        let f ← enter P fuel n c (xs.extract 0 a)
        applyV P fuel f (xs.extract a xs.size)
/-- Run a constant on exactly its arity. -/
def enter (P : Program) : Nat → Name → Const → Array V → Result
  | 0, _, _, _ => throw .exhausted
  | fuel + 1, n, c, xs =>
    match c with
    | .ctor p _ => pure (.ctor n (xs.extract p xs.size))
    | .prim _ => prim n xs
    | .code ps body => evalCode P fuel { vals := bind {} ps xs } body
/-- Apply a value to arguments. -/
def applyV (P : Program) : Nat → V → Array V → Result
  | 0, _, _ => throw .exhausted
  | fuel + 1, .clo f captured, xs => callConst P fuel f (captured ++ xs)
  | _ + 1, _, _ => throw (.fault "application of a non-closure")
end

/-- Run constant `n` on `xs` with `fuel`. -/
def run (P : Program) (fuel : Nat) (n : Name) (xs : Array V) : Result :=
  callConst P fuel n xs

end TSLean.Lcnf.Semantics
