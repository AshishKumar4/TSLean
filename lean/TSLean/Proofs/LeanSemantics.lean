-- TSLean.Proofs.LeanSemantics
-- Big-step operational semantics for the Lean-side output of the transpiler.
-- The generated Lean code uses the same value domain and operator semantics.
-- The LExpr type models the structure of generated Lean expressions.
-- The key insight: since both sides share the same BinOp semantics,
-- the preservation proof reduces to structural correspondence.

import TSLean.Proofs.Semantics

namespace TSLean.Proofs.LeanSemantics

open TSLean.Proofs.Semantics

/-! ## Lean Expression AST

The transpiler generates Lean 4 code. LExpr models what the generated code
looks like at the expression level. It uses the same BinOp type since the
operator semantics are identical — only the printed names differ.
-/

inductive LExpr where
  | litNum  : Float → LExpr
  | litBool : Bool → LExpr
  | litStr  : String → LExpr
  | litUnit : LExpr
  | var     : String → LExpr
  | binOp   : BinOp → LExpr → LExpr → LExpr
  | letE    : String → LExpr → LExpr → LExpr
  | ite     : LExpr → LExpr → LExpr → LExpr
  | seq     : List LExpr → LExpr
  | pureE   : LExpr → LExpr
  deriving Repr, BEq

/-! ## Fuel-based evaluator for Lean expressions -/

def leval (fuel : Nat) (env : Env) : LExpr → Option Val
  | .litNum n  => some (Val.num n)
  | .litBool b => some (Val.bool b)
  | .litStr s  => some (Val.str s)
  | .litUnit   => some Val.unit
  | .var x     => Env.lookup env x
  | .pureE e   => leval fuel env e
  | .binOp op l r =>
    match fuel with
    | 0 => none
    | n + 1 =>
      match leval n env l, leval n env r with
      | some vl, some vr => evalBinOp op vl vr
      | _, _ => none
  | .letE x init body =>
    match fuel with
    | 0 => none
    | n + 1 =>
      match leval n env init with
      | some vi => leval n (Env.extend env x vi) body
      | none => none
  | .ite cond th el =>
    match fuel with
    | 0 => none
    | n + 1 =>
      match leval n env cond with
      | some (Val.bool true)  => leval n env th
      | some (Val.bool false) => leval n env el
      | _ => none
  | .seq stmts => levalSeq fuel env stmts
where
  levalSeq (fuel : Nat) (env : Env) : List LExpr → Option Val
    | []      => some Val.unit
    | [e]     => leval fuel env e
    | e :: rest =>
      match fuel with
      | 0 => none
      | n + 1 =>
        match leval n env e with
        | some _ => levalSeq n env rest
        | none   => none

/-! ## Determinism -/

theorem leval_deterministic (fuel : Nat) (env : Env) (e : LExpr) (v1 v2 : Val) :
    leval fuel env e = some v1 → leval fuel env e = some v2 → v1 = v2 := by
  intro h1 h2; rw [h1] at h2; exact Option.some.inj h2

/-! ## Literal evaluation (fuel-independent) -/

@[simp] theorem leval_litNum (fuel : Nat) (env : Env) (n : Float) :
    leval fuel env (.litNum n) = some (Val.num n) := rfl

@[simp] theorem leval_litBool (fuel : Nat) (env : Env) (b : Bool) :
    leval fuel env (.litBool b) = some (Val.bool b) := rfl

@[simp] theorem leval_litStr (fuel : Nat) (env : Env) (s : String) :
    leval fuel env (.litStr s) = some (Val.str s) := rfl

@[simp] theorem leval_litUnit (fuel : Nat) (env : Env) :
    leval fuel env .litUnit = some Val.unit := rfl

@[simp] theorem leval_var (fuel : Nat) (env : Env) (x : String) :
    leval fuel env (.var x) = Env.lookup env x := rfl

@[simp] theorem leval_pureE (fuel : Nat) (env : Env) (e : LExpr) :
    leval fuel env (.pureE e) = leval fuel env e := rfl

/-! ## Compound expression reduction -/

theorem leval_binOp_succ (n : Nat) (env : Env) (op : BinOp) (l r : LExpr) :
    leval (n + 1) env (.binOp op l r) =
    match leval n env l, leval n env r with
    | some vl, some vr => evalBinOp op vl vr
    | _, _ => none := rfl

theorem leval_letE_succ (n : Nat) (env : Env) (x : String) (init body : LExpr) :
    leval (n + 1) env (.letE x init body) =
    match leval n env init with
    | some vi => leval n (Env.extend env x vi) body
    | none => none := rfl

theorem leval_ite_succ (n : Nat) (env : Env) (cond th el : LExpr) :
    leval (n + 1) env (.ite cond th el) =
    match leval n env cond with
    | some (Val.bool true)  => leval n env th
    | some (Val.bool false) => leval n env el
    | _ => none := rfl

/-! ## Derived reduction rules -/

theorem leval_binOp_step (n : Nat) (env : Env) (op : BinOp) (l r : LExpr)
    (vl vr vres : Val)
    (hl : leval n env l = some vl) (hr : leval n env r = some vr)
    (hop : evalBinOp op vl vr = some vres) :
    leval (n + 1) env (.binOp op l r) = some vres := by
  simp [leval, hl, hr, hop]

theorem leval_letE_step (n : Nat) (env : Env) (x : String) (init body : LExpr)
    (vi vb : Val)
    (hinit : leval n env init = some vi) (hbody : leval n (Env.extend env x vi) body = some vb) :
    leval (n + 1) env (.letE x init body) = some vb := by
  simp [leval, hinit, hbody]

theorem leval_ite_true_step (n : Nat) (env : Env) (cond th el : LExpr) (v : Val)
    (hcond : leval n env cond = some (Val.bool true)) (hth : leval n env th = some v) :
    leval (n + 1) env (.ite cond th el) = some v := by
  simp [leval, hcond, hth]

theorem leval_ite_false_step (n : Nat) (env : Env) (cond th el : LExpr) (v : Val)
    (hcond : leval n env cond = some (Val.bool false)) (hel : leval n env el = some v) :
    leval (n + 1) env (.ite cond th el) = some v := by
  simp [leval, hcond, hel]

/-! ## Seq evaluation -/

theorem leval_seq_nil (fuel : Nat) (env : Env) :
    leval fuel env (.seq []) = some Val.unit := rfl

theorem leval_seq_singleton (fuel : Nat) (env : Env) (e : LExpr) :
    leval fuel env (.seq [e]) = leval fuel env e := rfl

/-! ## Operator name mapping (for documentation / printer verification) -/

def binOpLeanName : BinOp → String
  | .add    => "HAdd.hAdd"
  | .sub    => "HSub.hSub"
  | .mul    => "HMul.hMul"
  | .eq     => "BEq.beq"
  | .ne     => "bne"
  | .lt     => "LT.lt"
  | .le     => "LE.le"
  | .gt     => "GT.gt"
  | .ge     => "GE.ge"
  | .and_   => "and"
  | .or_    => "or"
  | .concat => "HAppend.hAppend"

-- The mapping is injective (distinct TS ops produce distinct Lean names)
theorem binOpLeanName_injective (op1 op2 : BinOp)
    (h : binOpLeanName op1 = binOpLeanName op2) : op1 = op2 := by
  cases op1 <;> cases op2 <;> simp_all [binOpLeanName]

/-! ## Environment properties -/

theorem leval_var_extend_same (fuel : Nat) (env : Env) (x : String) (v : Val) :
    leval fuel (Env.extend env x v) (.var x) = some v := by
  simp [leval, Env.lookup_extend_same]

theorem leval_var_extend_diff (fuel : Nat) (env : Env) (x y : String) (v : Val) (h : x ≠ y) :
    leval fuel (Env.extend env x v) (.var y) = leval fuel env (.var y) := by
  simp [leval, Env.lookup_extend_diff env x y v h]

/-! ## Pure wrapping -/

theorem pureE_leval_identity (fuel : Nat) (env : Env) (e : LExpr) :
    leval fuel env (.pureE e) = leval fuel env e := rfl

/-! ## Structural correspondence between Expr and LExpr

The lowering from Expr to LExpr preserves structure exactly for the pure fragment.
This is defined here and proven to be semantics-preserving in ExprPreservation.lean.
-/

def exprToLExpr : Expr → LExpr
  | .litNum n      => .litNum n
  | .litBool b     => .litBool b
  | .litStr s      => .litStr s
  | .litUnit       => .litUnit
  | .var x         => .var x
  | .binOp op l r  => .binOp op (exprToLExpr l) (exprToLExpr r)
  | .letE x e b    => .letE x (exprToLExpr e) (exprToLExpr b)
  | .ite c t e     => .ite (exprToLExpr c) (exprToLExpr t) (exprToLExpr e)
  | .seq es        => .seq (es.map exprToLExpr)
  | .pureE e       => .pureE (exprToLExpr e)

end TSLean.Proofs.LeanSemantics
