import Lean.Compiler.LCNF.Basic
import Lean.Compiler.LCNF.PhaseExt
import Lean.Compiler.LCNF.ToImpureType
import Std.Data.HashMap
import Std.Data.HashSet
import TSLean.Lcnf.Target

/-!
# Lowering mono LCNF to the JavaScript subset

`lower : Info → Array (Decl .pure) → Except String Target.Program` is a pure, total function. The
environment is consulted once, beforehand, by `gatherInfo`, which reads Lean's own representation
decisions (`getCtorLayout`, `nameToImpureType`) into an `Info` table.

## Representation (plan, *Runtime representation*)

* `Nat` is `bigint`; `Bool` (and `Decidable`, which mono has erased to `Bool`) is `boolean`.
* An inductive whose constructors all have zero relevant fields is a `number`, the constructor index.
* Every other inductive is a tagged object `{ tag, fields }` whose `fields` hold the **relevant**
  fields only, in declaration order, as Lean's `getCtorLayout` classifies them.
* A structure with exactly one relevant field is that field. Mono has already applied this rule
  (`ToMono.trivialStructToMono`), so the lowering never sees such a constructor.
* Erased values (`◾`, type arguments, irrelevant fields) are `undefined`.
* A closure is `rt.Closure`: a function, its arity and the arguments received so far.

## Control (plan, *Lowering decisions*)

Each strongly connected component of the call graph is lowered in one of three modes, chosen by
its saturated intra-component calls:

* **plain** — none: one JS function per declaration.
* **loop** — every such call is a tail call. The component becomes one function whose body is
  `$main: while (true)`; a tail call assigns the argument slots `$a0 …` (and `$tag`, the member
  index, when the component has more than one member) and `continue`s. Each member's parameters
  are bound from the slots at the top of its case.
* **stack** — some call is not a tail call. The component becomes one function over a heap stack
  (see *Explicit stack* below).

A join point `jp j ps := body; k` becomes `let ps; $jp_j: { k } body`: the continuation runs in
the labeled block, a `jmp j as` assigns `ps := as` and `break`s out of it, and control falls into
the body. A tail call inside a join point is still a tail call of the function.

## Explicit stack

For a component in stack mode, with members `f₀ … fₘ₋₁` and slots `$a0 … $a(A-1)` (`A` the largest
arity):

```
function $scc_f0($tag: number, $a0, …): rt.Value {
  const $ks: number[] = [];      // continuation labels
  const $vs: rt.Value[] = [];    // saved live variables
  let $ret: rt.Value = undefined;
  $main: while (true) {
    $body: {
      switch ($tag) {
        case i: { const p = $a0; …; <body of fᵢ> }            // entry of member i
        case R: { const vₖ = $vs.pop(); …; const x = $ret; <resumption R> }
        default: { throw rt.badTag(); }
      }
    }
    const $k = $ks.pop();
    if ($k === undefined) { return $ret; } else { $tag = $k; }
  }
}
```

* Every **non-tail** call site `let x := g as; k` to a member is given a resumption label `R ≥ m`.
  Its continuation is defunctionalized: the frame is the label plus the values of the variables
  live in the continuation. The call pushes the live variables onto `$vs` and `R` onto `$ks`,
  assigns the slots, sets `$tag` to `g`'s index and `continue`s. Case `R` pops the live variables
  back under their own names, binds `x` to `$ret`, and runs `k`.
* The continuation `k` may `jmp` to join points declared around the call. Case `R` re-declares the
  join points `k` reaches (transitively), outermost first, so the resumption is a closed LCNF term:
  `jp j₁ …; … jp jₙ …; k`. Its free variables, minus `x`, are exactly the live set.
* A **tail** call to a member assigns the slots, sets `$tag` and `continue`s without pushing: the
  callee returns to the caller's continuation.
* A `return x` sets `$ret` and leaves `$body`; the loop then pops a label and resumes, or returns
  `$ret` when the stack is empty.
* `rt.pushFrame` bounds the stack depth and raises the typed `rt.ResourceExhausted`, the backstop
  the plan requires in place of a V8 `RangeError`.

Labels are assigned per syntactic call site (its result variable), so a join point re-declared in
several resumptions reuses the same labels. Each member is exported through a wrapper
`fᵢ(ps) = $scc_f0(i, ps)`, so closures and outside callers see an ordinary function.

## Refusals

A form outside the slice is refused by name, never lowered to a substitute: `proj`, `fun`, scalar
literals, constants with no code, constructor or primitive, and partial or over-application of a
constructor (partial constructor applications occur in mono only for builtin-represented types such
as `Int.ofNat`, which belong to the primitive table). Over-application of a declaration or primitive is valid Lean: it is lowered as a call
at the declared arity whose result `rt.apply` applies to the remaining arguments, the same `pap`
path as every other closure application. (An over-applied member of a recursive component is an
ordinary JS call to its wrapper, on the JS stack.)
-/

namespace TSLean.Lcnf.Lower

open Lean Lean.Compiler.LCNF
open TSLean.Lcnf.Target (Ty Stmt Fn Program)

abbrev TExpr := TSLean.Lcnf.Target.Expr

/-! ## The information the lowering reads from the environment -/

/-- Runtime representation of an inductive type. -/
inductive Rep where
  | bool
  | enum
  | obj
  deriving Inhabited, Repr, BEq

structure TypeRep where
  rep : Rep
  numCtors : Nat
  deriving Inhabited, Repr

structure CtorRep where
  typeName : Name
  cidx : Nat
  numParams : Nat
  numFields : Nat
  /-- Per field: is it kept in the object? -/
  relevant : Array Bool
  rep : Rep
  deriving Inhabited, Repr

/-- A primitive: the `@[extern]` leaf's runtime function and arity. -/
structure Prim where
  rtName : String
  arity : Nat
  deriving Inhabited, Repr

/-- The primitive table of the vertical slice. -/
def primTable : List (Name × Prim) :=
  [(``Nat.add, ⟨"natAdd", 2⟩), (``Nat.sub, ⟨"natSub", 2⟩), (``Nat.mul, ⟨"natMul", 2⟩),
   (``Nat.decEq, ⟨"natDecEq", 2⟩), (``Nat.decLt, ⟨"natDecLt", 2⟩)]

structure Info where
  types : Std.HashMap Name TypeRep := {}
  ctors : Std.HashMap Name CtorRep := {}
  prims : Std.HashMap Name Prim := {}
  deriving Inhabited

/-! ## Traversals over `Code` -/

mutual
/-- Constants a code block references in `let` values, and the types its `cases` inspect. -/
def refs : Code .pure → Array Name × Array Name → Array Name × Array Name
  | .let d k, acc =>
    let acc := match d.value with
      | .const n _ _ => if acc.1.contains n then acc else (acc.1.push n, acc.2)
      | _ => acc
    refs k acc
  | .fun (.mk _ _ _ _ v) k _, acc => refs k (refs v acc)
  | .jp (.mk _ _ _ _ v) k, acc => refs k (refs v acc)
  | .cases (.mk t _ _ ⟨alts⟩), acc =>
    refsAlts alts (if acc.2.contains t then acc else (acc.1, acc.2.push t))
  | _, acc => acc
def refsAlts : List (Alt .pure) → Array Name × Array Name → Array Name × Array Name
  | [], acc => acc
  | .alt _ _ k _ :: as, acc => refsAlts as (refs k acc)
  | .default k :: as, acc => refsAlts as (refs k acc)
  | .ctorAlt _ k _ :: as, acc => refsAlts as (refs k acc)
end

def argFVar : Arg .pure → Option FVarId
  | .fvar x => some x
  | _ => none

def pushNew (acc : Array FVarId) (bound : Std.HashSet FVarId) (x : FVarId) : Array FVarId :=
  if bound.contains x || acc.contains x then acc else acc.push x

def pushArgs (acc : Array FVarId) (bound : Std.HashSet FVarId) (as : Array (Arg .pure)) :
    Array FVarId :=
  as.foldl (fun acc a => match argFVar a with | some x => pushNew acc bound x | none => acc) acc

def bindParams (bound : Std.HashSet FVarId) (ps : Array (Param .pure)) : Std.HashSet FVarId :=
  ps.foldl (fun b p => b.insert p.fvarId) bound

mutual
/-- Free variables of a code block, in order of first occurrence. Join point names are not
variables; a `jmp` contributes its arguments. -/
def freeVars : Code .pure → Std.HashSet FVarId → Array FVarId → Array FVarId
  | .let d k, bound, acc =>
    let acc := match d.value with
      | .fvar f as => pushArgs (pushNew acc bound f) bound as
      | .const _ _ as => pushArgs acc bound as
      | .proj _ _ x => pushNew acc bound x
      | _ => acc
    freeVars k (bound.insert d.fvarId) acc
  | .fun (.mk f _ ps _ v) k _, bound, acc =>
    freeVars k (bound.insert f) (freeVars v (bindParams bound ps) acc)
  | .jp (.mk f _ ps _ v) k, bound, acc =>
    freeVars k (bound.insert f) (freeVars v (bindParams bound ps) acc)
  | .jmp _ as, bound, acc => pushArgs acc bound as
  | .cases (.mk _ _ x ⟨alts⟩), bound, acc => freeVarsAlts alts bound (pushNew acc bound x)
  | .return x, bound, acc => pushNew acc bound x
  | _, _, acc => acc
def freeVarsAlts : List (Alt .pure) → Std.HashSet FVarId → Array FVarId → Array FVarId
  | [], _, acc => acc
  | .alt _ ps k _ :: as, bound, acc => freeVarsAlts as bound (freeVars k (bindParams bound ps) acc)
  | .default k :: as, bound, acc => freeVarsAlts as bound (freeVars k bound acc)
  | .ctorAlt _ k _ :: as, bound, acc => freeVarsAlts as bound (freeVars k bound acc)
end

mutual
/-- Join points a code block jumps to. -/
def jmpTargets : Code .pure → Array FVarId → Array FVarId
  | .let _ k, acc => jmpTargets k acc
  | .fun (.mk _ _ _ _ v) k _, acc => jmpTargets k (jmpTargets v acc)
  | .jp (.mk _ _ _ _ v) k, acc => jmpTargets k (jmpTargets v acc)
  | .jmp j _, acc => if acc.contains j then acc else acc.push j
  | .cases (.mk _ _ _ ⟨alts⟩), acc => jmpTargetsAlts alts acc
  | _, acc => acc
def jmpTargetsAlts : List (Alt .pure) → Array FVarId → Array FVarId
  | [], acc => acc
  | .alt _ _ k _ :: as, acc => jmpTargetsAlts as (jmpTargets k acc)
  | .default k :: as, acc => jmpTargetsAlts as (jmpTargets k acc)
  | .ctorAlt _ k _ :: as, acc => jmpTargetsAlts as (jmpTargets k acc)
end

/-- A saturated call to a member of the component being lowered. -/
structure Site where
  /-- The member whose body contains the call. -/
  member : Name := .anonymous
  /-- The call's result variable; it names the site. -/
  result : FVarId
  callee : Name
  args : Array (Arg .pure)
  /-- `let result := callee args; k` with `k = return result`. -/
  tail : Bool
  /-- For a non-tail site: its continuation closed over the join points it reaches. -/
  resume : Code .pure
  deriving Inhabited

/-- Close `k` over the join points in scope (`jps`, outermost first) that it reaches. -/
def closeOverJps (jps : Array (FunDecl .pure)) (k : Code .pure) : Code .pure :=
  let needed := jps.foldr (init := jmpTargets k #[]) fun d needed =>
    if needed.contains d.fvarId then jmpTargets d.value needed else needed
  jps.foldr (init := k) fun d c => if needed.contains d.fvarId then .jp d c else c

mutual
/-- Saturated calls to members of `arity` (the component), with their join-point context. -/
def sites (arity : Std.HashMap Name Nat) :
    Array (FunDecl .pure) → Code .pure → Array Site → Array Site
  | jps, .let d k, acc =>
    let acc := match d.value with
      | .const n _ as =>
        match arity[n]? with
        | some a =>
          if as.size != a then acc
          else
            let tail := match k with | .return r => r == d.fvarId | _ => false
            acc.push { result := d.fvarId, callee := n, args := as, tail,
                       resume := if tail then .return d.fvarId else closeOverJps jps k }
        | none => acc
      | _ => acc
    sites arity jps k acc
  | jps, .fun (.mk _ _ _ _ v) k _, acc => sites arity jps k (sites arity jps v acc)
  | jps, .jp d@(.mk _ _ _ _ v) k, acc => sites arity (jps.push d) k (sites arity jps v acc)
  | jps, .cases (.mk _ _ _ ⟨alts⟩), acc => sitesAlts arity jps alts acc
  | _, _, acc => acc
def sitesAlts (arity : Std.HashMap Name Nat) :
    Array (FunDecl .pure) → List (Alt .pure) → Array Site → Array Site
  | _, [], acc => acc
  | jps, .alt _ _ k _ :: as, acc => sitesAlts arity jps as (sites arity jps k acc)
  | jps, .default k :: as, acc => sitesAlts arity jps as (sites arity jps k acc)
  | jps, .ctorAlt _ k _ :: as, acc => sitesAlts arity jps as (sites arity jps k acc)
end

/-! ## The call graph and its components -/

/-- Nodes reachable from `s` in one or more steps. -/
def reachable (adj : Array (Array Nat)) (s : Nat) : Array Bool := Id.run do
  let n := adj.size
  let mut seen := Array.replicate n false
  let mut stack : Array Nat := #[]
  for j in adj.getD s #[] do
    if !seen.getD j true then
      seen := seen.set! j true
      stack := stack.push j
  for _ in [0:n] do
    match stack.back? with
    | none => break
    | some i =>
      stack := stack.pop
      for j in adj.getD i #[] do
        if !seen.getD j true then
          seen := seen.set! j true
          stack := stack.push j
  return seen

/-- Strongly connected components, each sorted by index, in order of their least member. -/
def components (adj : Array (Array Nat)) : Array (Array Nat) := Id.run do
  let n := adj.size
  let reach := (Array.range n).map (reachable adj)
  let mut done := Array.replicate n false
  let mut out : Array (Array Nat) := #[]
  for i in [0:n] do
    if done.getD i true then continue
    let mut comp : Array Nat := #[i]
    done := done.set! i true
    for j in [i+1:n] do
      if !done.getD j true && (reach.getD i #[]).getD j false && (reach.getD j #[]).getD i false then
        comp := comp.push j
        done := done.set! j true
    out := out.push comp
  return out

/-! ## Names -/

def reserved : List String :=
  ["break", "case", "catch", "class", "const", "continue", "debugger", "default", "delete", "do",
   "else", "enum", "export", "extends", "false", "finally", "for", "function", "if", "import", "in",
   "instanceof", "new", "null", "return", "super", "switch", "this", "throw", "true", "try",
   "typeof", "var", "void", "while", "with", "yield", "let", "static", "implements", "interface",
   "package", "private", "protected", "public", "await", "arguments", "eval", "undefined", "NaN",
   "Infinity", "rt", "async", "of", "as", "type", "any", "unknown", "never", "object", "string",
   "number", "boolean", "bigint", "symbol", "declare", "namespace", "module", "readonly"]

/-- An identifier from a Lean name: ASCII letters, digits and `_` survive, everything else is `_`.
Never contains `$`, which the lowering reserves for its own names and for disambiguation. -/
def sanitize (n : Name) : String :=
  let s := String.ofList <| (n.toString (escape := false)).toList.map fun c =>
    if c.isAlphanum && c.toNat < 128 || c == '_' then c else '_'
  let s := if s.isEmpty || (s.front.isDigit) then "_" ++ s else s
  if reserved.contains s then s ++ "_" else s

/-- `base`, or `base$2`, `base$3`, … : the first not in `used`. -/
def fresh (used : Std.HashSet String) (base : String) : String := Id.run do
  if !used.contains base then return base
  for i in [2:used.size + 2] do
    let c := base ++ "$" ++ toString i
    if !used.contains c then return c
  return base ++ "$" ++ toString (used.size + 2)

/-! ## Lowering code -/

inductive Mode where
  | plain
  /-- Tail calls only. `tagged` when the component has more than one member. -/
  | loop (tagged : Bool)
  | stack
  deriving Inhabited, BEq

structure Ctx where
  info : Info
  /-- Public JS name and arity of every code declaration. -/
  fns : Std.HashMap Name (String × Nat)
  /-- The declaration being lowered, for diagnostics. -/
  self : Name
  mode : Mode
  /-- Members of the component: index. -/
  members : Std.HashMap Name Nat
  /-- Non-tail call sites: resumption label and live variables. -/
  resumes : Std.HashMap (Name × FVarId) (Nat × Array FVarId)
  /-- Join points in scope, outermost first. -/
  jps : Array (FunDecl .pure) := #[]

structure St where
  /-- The declaration whose variables are being named. Free-variable ids are unique within a
  declaration only (canonical declarations renumber them from zero), so names are per member. -/
  member : Name := .anonymous
  names : Std.HashMap (Name × FVarId) String := {}
  labels : Std.HashMap (Name × FVarId) String := {}
  used : Std.HashSet String
  usedLabels : Std.HashSet String := {}
  objs : Nat := 0

abbrev M := StateT St (Except String)

def refuse (ctx : Ctx) (msg : String) : M α := throw s!"{ctx.self}: {msg}"

def slot (j : Nat) : String := "$a" ++ toString j

/-- The JS name of a variable, allocated on first sight. -/
def nameOf (x : FVarId) (hint : Name) : M String := do
  let s ← get
  match s.names[(s.member, x)]? with
  | some i => pure i
  | none =>
    let i := fresh s.used (sanitize hint)
    set { s with names := s.names.insert (s.member, x) i, used := s.used.insert i }
    pure i

def labelOf (j : FunDecl .pure) : M String := do
  let s ← get
  match s.labels[(s.member, j.fvarId)]? with
  | some l => pure l
  | none =>
    let l := fresh s.usedLabels ("$jp_" ++ sanitize j.binderName)
    set { s with labels := s.labels.insert (s.member, j.fvarId) l, usedLabels := s.usedLabels.insert l }
    pure l

def ref (ctx : Ctx) (x : FVarId) : M TExpr := do
  let s ← get
  match s.names[(s.member, x)]? with
  | some i => pure (.var i)
  | none => refuse ctx s!"variable {x.name} used before it is bound"

def argE (ctx : Ctx) : Arg .pure → M TExpr
  | .erased | .type .. => pure .undef
  | .fvar x => ref ctx x

def argsE (ctx : Ctx) (as : Array (Arg .pure)) : M (List TExpr) := as.toList.mapM (argE ctx)

def rtCall (f : String) (as : List TExpr) : TExpr := .call (.rt f) as

def valueTy : Ty := .value

/-- The value of constructor `c`, given the expression of each field. -/
def ctorExpr (c : CtorRep) (field : Nat → TExpr) : TExpr :=
  match c.rep with
  | .bool => .bool (c.cidx == 1)
  | .enum => .num c.cidx
  | .obj =>
    let fs := (List.range c.numFields).filterMap fun i =>
      if c.relevant.getD i false then some (field i) else none
    .obj [("tag", .num c.cidx), ("fields", .arr fs)]

/-- Build the value of constructor `c` from the arguments of its application. -/
def ctorValue (ctx : Ctx) (c : CtorRep) (as : Array (Arg .pure)) : M TExpr := do
  let args ← argsE ctx as
  pure (ctorExpr c fun i => args.getD (c.numParams + i) .undef)

/-- The value of `n as` when it is not an intra-component call. -/
def constValue (ctx : Ctx) (n : Name) (as : Array (Arg .pure)) : M TExpr := do
  let args ← argsE ctx as
  if let some c := ctx.info.ctors[n]? then
    let arity := c.numParams + c.numFields
    if as.size == arity then ctorValue ctx c as
    else if as.size < arity then
      -- Observed in mono only for builtin-represented types (`Int.ofNat`, `UInt32.ofBitVec`),
      -- whose constructors belong to the primitive table (M3).
      refuse ctx s!"partial application of constructor {n}"
    else refuse ctx s!"over-application of constructor {n}"
  else
    let (fn, arity) ← match ctx.info.prims[n]?, ctx.fns[n]? with
      | some p, _ => pure (TSLean.Lcnf.Target.Expr.rt p.rtName, p.arity)
      | none, some (f, a) => pure (TSLean.Lcnf.Target.Expr.var f, a)
      | none, none => refuse ctx s!"constant {n} has no code declaration, constructor or primitive"
    if as.size < arity then
      pure (rtCall "pap" [fn, .num arity, .arr args])
    else if as.size == arity then
      pure (.call fn args)
    else
      -- Over-application: a call at the declared arity, then the result applied to the rest.
      pure (rtCall "apply" [.call fn (args.take arity), .arr (args.drop arity)])

/-- Assign the argument slots and dispatch to member `callee`. -/
def jumpTo (ctx : Ctx) (callee : Name) (as : Array (Arg .pure)) : M (List Stmt) := do
  let some idx := ctx.members[callee]? | refuse ctx s!"{callee} is not a member of the component"
  let args ← argsE ctx as
  let assigns := (args.zipIdx).map fun (e, j) => Stmt.assign (slot j) e
  let tag := match ctx.mode with
    | .loop false => []
    | _ => [Stmt.assign "$tag" (.num idx)]
  pure (assigns ++ tag ++ [.continue "$main"])

/-- Bind the parameters of a `cases` alternative from the checked object `o`. -/
def bindFields (c : CtorRep) (o : Option String) (ps : Array (Param .pure)) : M (List Stmt) := do
  let mut out : List Stmt := []
  let mut pos := 0
  for i in [0:ps.size] do
    let p := ps[i]!
    let x ← nameOf p.fvarId p.binderName
    if c.relevant.getD i false then
      match o with
      | some o => out := out ++ [.const x valueTy (.index (.prop (.var o) "fields") pos)]
      | none => out := out ++ [.const x valueTy .undef]
      pos := pos + 1
    else
      out := out ++ [.const x valueTy .undef]
  pure out

mutual
def lowerCode (ctx : Ctx) : Code .pure → M (List Stmt)
  | .let d k => do
    let x ← nameOf d.fvarId d.binderName
    match d.value with
    | .const n _ as =>
      match ctx.mode, ctx.members[n]?, ctx.fns[n]? with
      | .plain, _, _ => do
        let v ← constValue ctx n as
        pure ([.const x valueTy v] ++ (← lowerCode ctx k))
      | _, some _, some (_, arity) =>
        if as.size != arity then do
          let v ← constValue ctx n as
          pure ([.const x valueTy v] ++ (← lowerCode ctx k))
        else
          match k with
          | .return r =>
            if r == d.fvarId then jumpTo ctx n as
            else nonTail ctx x d.fvarId n as
          | _ => nonTail ctx x d.fvarId n as
      | _, _, _ => do
        let v ← constValue ctx n as
        pure ([.const x valueTy v] ++ (← lowerCode ctx k))
    | v => do
      let e ← match v with
        | .lit (.nat n) => pure (TSLean.Lcnf.Target.Expr.bigint n)
        | .lit (.str s) => pure (TSLean.Lcnf.Target.Expr.str s)
        | .lit _ => refuse ctx "scalar literal (primitive table, M3)"
        | .erased => pure TSLean.Lcnf.Target.Expr.undef
        | .proj .. => refuse ctx "proj is not a mono form"
        | .fvar f as =>
          if as.isEmpty then ref ctx f
          else do pure (rtCall "apply" [← ref ctx f, .arr (← argsE ctx as)])
        | _ => refuse ctx "impure let value"
      pure ([.const x valueTy e] ++ (← lowerCode ctx k))
  | .jp d@(.mk _ _ ps _ v) k => do
    let lets ← ps.toList.mapM fun p => do
      pure (Stmt.let (← nameOf p.fvarId p.binderName) valueTy .undef)
    let l ← labelOf d
    let kS ← lowerCode { ctx with jps := ctx.jps.push d } k
    let bodyS ← lowerCode ctx v
    pure (lets ++ [.block l kS] ++ bodyS)
  | .jmp j as => do
    let some d := ctx.jps.find? (·.fvarId == j) | refuse ctx s!"jump to unknown join point {j.name}"
    let l ← labelOf d
    let args ← argsE ctx as
    let ps ← d.params.toList.mapM fun p => nameOf p.fvarId p.binderName
    pure ((ps.zip args).map (fun (p, e) => Stmt.assign p e) ++ [.break l])
  | .cases (.mk t _ discr ⟨alts⟩) => do
    let some tr := ctx.info.types[t]? | refuse ctx s!"cases on {t}, which has no representation"
    let dE ← ref ctx discr
    match tr.rep with
    | .bool => do
      let (cs, dflt) ← lowerAlts ctx none alts
      let pick (cidx : Nat) : List Stmt := match cs.find? (·.1 == cidx) with
        | some (_, b) => b
        | none => dflt
      pure [.ite (rtCall "bool" [dE]) (pick 1) (pick 0)]
    | .enum => do
      let (cs, dflt) ← lowerAlts ctx none alts
      pure [.switch (rtCall "enumTag" [dE]) cs dflt]
    | .obj => do
      let s ← get
      let o := "$o" ++ toString s.objs
      set { s with objs := s.objs + 1 }
      let (cs, dflt) ← lowerAlts ctx (some o) alts
      let head := Stmt.const o .obj (rtCall "obj" [dE])
      match cs, alts with
      | [(_, body)], [.alt _ _ _ _] =>
        if tr.numCtors == 1 then pure [head, .block ("$case" ++ toString s.objs) body]
        else pure [head, .switch (.prop (.var o) "tag") cs dflt]
      | _, _ => pure [head, .switch (.prop (.var o) "tag") cs dflt]
  | .return x => do
    let e ← ref ctx x
    match ctx.mode with
    | .stack => pure [.assign "$ret" e, .break "$body"]
    | _ => pure [.ret e]
  | .unreach _ => pure [.throw (rtCall "unreachable" [])]
  | .fun .. => refuse ctx "local function is not a mono form"
  | _ => refuse ctx "impure-only construct"
/-- A non-tail call to a member: save the live variables and the resumption label, then enter. -/
def nonTail (ctx : Ctx) (_x : String) (result : FVarId) (callee : Name) (as : Array (Arg .pure)) :
    M (List Stmt) := do
  let some (label, live) := ctx.resumes[(ctx.self, result)]?
    | refuse ctx s!"non-tail call to {callee} outside stack mode"
  let liveE ← live.toList.mapM (ref ctx)
  let save := if liveE.isEmpty then [] else [Stmt.expr (.method (.var "$vs") "push" liveE)]
  pure (save ++ [.expr (rtCall "pushFrame" [.var "$ks", .num label])] ++ (← jumpTo ctx callee as))
def lowerAlts (ctx : Ctx) (o : Option String) :
    List (Alt .pure) → M (List (Nat × List Stmt) × List Stmt)
  | [] => pure ([], [.throw (rtCall "noAlt" [])])
  | .alt n ps k _ :: as => do
    let some c := ctx.info.ctors[n]? | refuse ctx s!"constructor {n} has no representation"
    let binds ← bindFields c o ps
    let body ← lowerCode ctx k
    let (cs, dflt) ← lowerAlts ctx o as
    pure ((c.cidx, binds ++ body) :: cs, dflt)
  | .default k :: as => do
    let body ← lowerCode ctx k
    let (cs, _) ← lowerAlts ctx o as
    pure (cs, body)
  | .ctorAlt .. :: _ => refuse ctx "impure alternative"
end

/-! ## Components -/

def paramNames (ps : Array (Param .pure)) : M (List String) :=
  ps.toList.mapM fun p => nameOf p.fvarId p.binderName

def valueParams (xs : List String) : List (String × Ty) := xs.map (·, Ty.value)

def slots (n : Nat) : List String := (List.range n).map slot

/-- Bind a member's parameters from the argument slots. -/
def fromSlots (ps : Array (Param .pure)) : M (List Stmt) := do
  let xs ← paramNames ps
  pure (xs.zipIdx.map fun (x, j) => Stmt.const x valueTy (.var (slot j)))

def lowerPlain (ctx : Ctx) (used : Std.HashSet String) (d : Decl .pure) (body : Code .pure) :
    Except String Fn := do
  let ctx := { ctx with self := d.name }
  let (fn, _) ← (do
      let xs ← paramNames d.params
      let b ← lowerCode ctx body
      pure { name := (ctx.fns.getD d.name ("", 0)).1, params := valueParams xs, ret := .value,
             body := b : Fn }).run { used, member := d.name }
  pure fn

/-- Lower one component. `used` holds the module's function names. -/
def lowerComponent (info : Info) (fns : Std.HashMap Name (String × Nat)) (used : Std.HashSet String)
    (members : Array (Decl .pure × Code .pure)) : Except String (List Fn) := do
  let arity : Std.HashMap Name Nat :=
    members.foldl (fun m (d, _) => m.insert d.name d.params.size) {}
  let idx : Std.HashMap Name Nat :=
    (members.zipIdx).foldl (fun m ((d, _), i) => m.insert d.name i) {}
  let allSites := members.foldl (init := #[]) fun acc (d, body) =>
    acc ++ (sites arity #[] body #[]).map ({ · with member := d.name })
  let first := members[0]!.1
  let base : Ctx := { info, fns, self := first.name, mode := .plain, members := idx, resumes := {} }
  if allSites.isEmpty then
    return ← members.toList.mapM fun (d, body) => lowerPlain base used d body
  let width := members.foldl (fun w (d, _) => max w d.params.size) 0
  let publicName (d : Decl .pure) := (fns.getD d.name ("", 0)).1
  let wrappers (inner : String) : List Fn := members.toList.zipIdx.map fun ((d, _), i) =>
    let xs := slots d.params.size
    { name := publicName d, params := valueParams xs, ret := .value,
      body := [.ret (.call (.var inner)
        (.num i :: xs.map TSLean.Lcnf.Target.Expr.var ++ (List.replicate (width - d.params.size) TSLean.Lcnf.Target.Expr.undef)))] }
  let inner := "$scc_" ++ publicName first
  if allSites.all (·.tail) then
    if members.size == 1 then
      let (d, body) := members[0]!
      let ctx := { base with mode := .loop false, self := d.name }
      let (b, _) ← (do
          let bind ← fromSlots d.params
          pure (bind ++ (← lowerCode ctx body))).run { used, member := d.name }
      return [{ name := publicName d, params := valueParams (slots d.params.size), ret := .value,
                body := [.loop "$main" b] }]
    let lowerMember (ctx : Ctx) (m : (Decl .pure × Code .pure) × Nat) : M (Nat × List Stmt) := do
      let ((d, body), i) := m
      modify ({ · with member := d.name })
      let bind ← fromSlots d.params
      let b ← lowerCode { ctx with self := d.name } body
      pure (i, bind ++ b)
    let (cases, _) ← (members.toList.zipIdx.mapM (lowerMember { base with mode := .loop true })).run { used }
    return { name := inner, params := ("$tag", .number) :: valueParams (slots width), ret := .value,
             body := [.loop "$main" [.switch (.var "$tag") cases [.throw (rtCall "badTag" [])]]] }
      :: wrappers inner
  -- Stack mode.
  let nonTailSites := allSites.filter (!·.tail)
  let resumes : Std.HashMap (Name × FVarId) (Nat × Array FVarId) :=
    (nonTailSites.zipIdx).foldl (init := {}) fun m (s, i) =>
      let live := freeVars s.resume (({} : Std.HashSet FVarId).insert s.result) #[]
      m.insert (s.member, s.result) (members.size + i, live)
  let ctx := { base with mode := .stack, resumes }
  let lowerMember (m : (Decl .pure × Code .pure) × Nat) : M (Nat × List Stmt) := do
    let ((d, body), i) := m
    modify ({ · with member := d.name })
    let bind ← fromSlots d.params
    let b ← lowerCode { ctx with self := d.name } body
    pure (i, bind ++ b)
  let lowerResume (s : Site) : M (Nat × List Stmt) := do
    let some (label, live) := resumes[(s.member, s.result)]? | throw "resumption label missing"
    modify ({ · with member := s.member })
    let restore ← live.toList.reverse.mapM fun y => do
      let some i := (← get).names[(s.member, y)]? | throw s!"{s.member}: live variable {y.name} unnamed"
      pure (Stmt.const i valueTy (.method (.var "$vs") "pop" []))
    let some x := (← get).names[(s.member, s.result)]? | throw s!"{s.member}: call result unnamed"
    let b ← lowerCode { ctx with self := s.member } s.resume
    pure (label, restore ++ [.const x valueTy (.var "$ret")] ++ b)
  let all : M (List (Nat × List Stmt)) := do
    let entries ← members.toList.zipIdx.mapM lowerMember
    let resumptions ← nonTailSites.toList.mapM lowerResume
    pure (entries ++ resumptions)
  let (cases, _) ← all.run { used }
  let body : List Stmt := [
    .const "$ks" .numbers (.arr []),
    .const "$vs" .values (.arr []),
    .let "$ret" .value .undef,
    .loop "$main" [
      .block "$body" [.switch (.var "$tag") cases [.throw (rtCall "badTag" [])]],
      .const "$k" .numberOrNone (.method (.var "$ks") "pop" []),
      .ite (.strictEq (.var "$k") .undef) [.ret (.var "$ret")] [.assign "$tag" (.var "$k")]]]
  return { name := inner, params := ("$tag", .number) :: valueParams (slots width), ret := .value,
           body } :: wrappers inner

/-- The exported JS name and the arity of every code declaration, and the set of names taken.
Names are allocated in declaration order, so the roots, listed first, get the plainest names. -/
def publicNames (decls : Array (Decl .pure)) : Std.HashMap Name (String × Nat) × Std.HashSet String :=
  decls.foldl (init := ({}, {})) fun (fns, used) d =>
    match d.value with
    | .code _ =>
      let n := fresh used (sanitize d.name)
      (fns.insert d.name (n, d.params.size), used.insert n)
    | .extern _ => (fns, used)

/-- Lower a closure of mono declarations to one module. `decls` lists the code declarations; the
first ones get the plainest names, so list the roots first. -/
def lower (info : Info) (runtime : String) (decls : Array (Decl .pure)) : Except String Program := do
  let code ← decls.filterMapM fun d => match d.value with
    | .code c => pure (some (d, c))
    | .extern _ => pure none
  let (fns, used) := publicNames decls
  let index : Std.HashMap Name Nat := (code.zipIdx).foldl (fun m ((d, _), i) => m.insert d.name i) {}
  let adj := code.map fun (_, c) => (refs c (#[], #[])).1.filterMap (index[·]?)
  let mut out : List Fn := []
  for comp in components adj do
    out := out ++ (← lowerComponent info fns used (comp.filterMap (code[·]?)))
  return { runtime, fns := out }

/-! ## Reading Lean's representation decisions -/

def typeRep (t : Name) : CoreM (Except String TypeRep) := do
  if t == ``Bool then return .ok ⟨.bool, 2⟩
  if (builtinImpureTypeName t) then
    return .error s!"{t} is a builtin runtime type (primitive table, M3)"
  let some (.inductInfo iv) := (← getEnv).find? t | return .error s!"{t} is not an inductive type"
  let it ← nameToImpureType t
  let enum := it == ImpureType.uint8 || it == ImpureType.uint16 || it == ImpureType.uint32 ||
    it == ImpureType.tagged
  return .ok ⟨if enum then .enum else .obj, iv.ctors.length⟩
where
  builtinImpureTypeName (t : Name) : Bool :=
    [``Nat, ``Int, ``UInt8, ``UInt16, ``UInt32, ``UInt64, ``USize, ``Float, ``Float32, ``String,
     ``Array, ``ByteArray, ``FloatArray, ``Thunk, ``Task].contains t

def ctorRep (n : Name) (ci : ConstructorVal) : CoreM (Except String CtorRep) := do
  match ← typeRep ci.induct with
  | .error e => return .error e
  | .ok tr =>
    let layout ← try getCtorLayout n catch e => return .error s!"{n}: {← e.toMessageData.toString}"
    let relevant := layout.fieldInfo.map fun
      | .erased | .void => false
      | _ => true
    return .ok { typeName := ci.induct, cidx := ci.cidx, numParams := ci.numParams,
                 numFields := ci.numFields, relevant, rep := tr.rep }

/-- Read the representation of every constructor, type and primitive the declarations reach. -/
def gatherInfo (decls : Array (Decl .pure)) : CoreM (Except String Info) := do
  let (consts, types) := decls.foldl (init := (#[], #[])) fun acc d =>
    match d.value with
    | .code c => refs c acc
    | .extern _ => acc
  let codeNames := decls.map (·.name)
  let mut info : Info := {}
  for t in types do
    match ← typeRep t with
    | .ok r => info := { info with types := info.types.insert t r }
    | .error e => return .error s!"cases: {e}"
  for n in consts do
    if codeNames.contains n then continue
    if let some (_, p) := primTable.find? (·.1 == n) then
      info := { info with prims := info.prims.insert n p }
      continue
    match (← getEnv).find? n with
    | some (.ctorInfo ci) =>
      match ← ctorRep n ci with
      | .ok c =>
        info := { info with ctors := info.ctors.insert n c }
        -- A `cases` needs every constructor of its type, not only the ones built.
        if !info.types.contains ci.induct then
          match ← typeRep ci.induct with
          | .ok r => info := { info with types := info.types.insert ci.induct r }
          | .error e => return .error e
      | .error e => return .error e
    | _ => return .error s!"constant {n} has no code declaration, constructor or primitive"
  -- Constructors matched on by `cases`.
  for t in types do
    let some (.inductInfo iv) := (← getEnv).find? t | continue
    for c in iv.ctors do
      if info.ctors.contains c then continue
      let some (.ctorInfo ci) := (← getEnv).find? c | continue
      match ← ctorRep c ci with
      | .ok r => info := { info with ctors := info.ctors.insert c r }
      | .error e => return .error e
  return .ok info

end TSLean.Lcnf.Lower
