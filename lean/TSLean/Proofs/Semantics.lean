-- TSLean.Proofs.Semantics
-- Big-step operational semantics for the pure TS IR expression fragment.
import TSLean.Runtime.Basic

namespace TSLean.Proofs.Semantics
open TSLean

/-! ## Binary operators -/

inductive BinOp where
  | add | sub | mul | eq | ne | lt | le | gt | ge | and_ | or_ | concat
  deriving Repr, BEq, DecidableEq

/-! ## Value domain (first-order, no closures) -/

inductive Val where
  | num  : Float → Val
  | bool : Bool → Val
  | str  : String → Val
  | unit : Val
  deriving Repr, BEq

/-! ## Expression AST (pure TS IR fragment) -/

inductive Expr where
  | litNum  : Float → Expr
  | litBool : Bool → Expr
  | litStr  : String → Expr
  | litUnit : Expr
  | var     : String → Expr
  | binOp   : BinOp → Expr → Expr → Expr
  | letE    : String → Expr → Expr → Expr
  | ite     : Expr → Expr → Expr → Expr
  | seq     : List Expr → Expr
  | pureE   : Expr → Expr
  deriving Repr, BEq

/-! ## Environments -/

def Env := List (String × Val)

instance : EmptyCollection Env := ⟨([] : List (String × Val))⟩

def Env.lookup : Env → String → Option Val
  | [], _ => none
  | (k, v) :: rest, x => if k == x then some v else Env.lookup rest x

def Env.extend (env : Env) (x : String) (v : Val) : Env := (x, v) :: env

theorem Env.lookup_extend_same (env : Env) (x : String) (v : Val) :
    Env.lookup (Env.extend env x v) x = some v := by
  simp [extend, lookup, beq_self_eq_true]

theorem Env.lookup_extend_diff (env : Env) (x y : String) (v : Val) (h : x ≠ y) :
    Env.lookup (Env.extend env x v) y = Env.lookup env y := by
  simp only [extend, lookup]
  have hne : (x == y) = false := beq_eq_false_iff_ne.mpr h
  simp [hne]

/-! ## Binary operator semantics -/

def evalBinOp (op : BinOp) (v1 v2 : Val) : Option Val :=
  match op, v1, v2 with
  | .add,    .num a,  .num b  => some (Val.num (a + b))
  | .sub,    .num a,  .num b  => some (Val.num (a - b))
  | .mul,    .num a,  .num b  => some (Val.num (a * b))
  | .eq,     .num a,  .num b  => some (Val.bool (a == b))
  | .ne,     .num a,  .num b  => some (Val.bool (a != b))
  | .lt,     .num a,  .num b  => some (Val.bool (a < b))
  | .le,     .num a,  .num b  => some (Val.bool (a ≤ b))
  | .gt,     .num a,  .num b  => some (Val.bool (a > b))
  | .ge,     .num a,  .num b  => some (Val.bool (a ≥ b))
  | .and_,   .bool a, .bool b => some (Val.bool (a && b))
  | .or_,    .bool a, .bool b => some (Val.bool (a || b))
  | .concat, .str a,  .str b  => some (Val.str (a ++ b))
  | .eq,     .str a,  .str b  => some (Val.bool (a == b))
  | .ne,     .str a,  .str b  => some (Val.bool (a != b))
  | .eq,     .bool a, .bool b => some (Val.bool (a == b))
  | .ne,     .bool a, .bool b => some (Val.bool (a != b))
  | _, _, _ => none

/-! ## Fuel-based evaluator -/

def eval (fuel : Nat) (env : Env) : Expr → Option Val
  | Expr.litNum n  => some (Val.num n)
  | Expr.litBool b => some (Val.bool b)
  | Expr.litStr s  => some (Val.str s)
  | Expr.litUnit   => some Val.unit
  | Expr.var x     => Env.lookup env x
  | Expr.pureE e   => eval fuel env e
  | Expr.binOp op l r =>
    match fuel with
    | 0 => none
    | n + 1 =>
      match eval n env l, eval n env r with
      | some vl, some vr => evalBinOp op vl vr
      | _, _ => none
  | Expr.letE x init body =>
    match fuel with
    | 0 => none
    | n + 1 =>
      match eval n env init with
      | some vi => eval n (Env.extend env x vi) body
      | none => none
  | Expr.ite cond th el =>
    match fuel with
    | 0 => none
    | n + 1 =>
      match eval n env cond with
      | some (Val.bool true)  => eval n env th
      | some (Val.bool false) => eval n env el
      | _ => none
  | Expr.seq stmts => evalSeq fuel env stmts
where
  evalSeq (fuel : Nat) (env : Env) : List Expr → Option Val
    | []      => some Val.unit
    | [e]     => eval fuel env e
    | e :: rest =>
      match fuel with
      | 0 => none
      | n + 1 =>
        match eval n env e with
        | some _ => evalSeq n env rest
        | none   => none

/-! ## Determinism (trivial: eval is a function) -/

theorem eval_deterministic (fuel : Nat) (env : Env) (e : Expr) (v1 v2 : Val) :
    eval fuel env e = some v1 → eval fuel env e = some v2 → v1 = v2 := by
  intro h1 h2; rw [h1] at h2; exact Option.some.inj h2

/-! ## Literal evaluation is fuel-independent -/

@[simp] theorem eval_litNum (fuel : Nat) (env : Env) (n : Float) :
    eval fuel env (Expr.litNum n) = some (Val.num n) := by rfl

@[simp] theorem eval_litBool (fuel : Nat) (env : Env) (b : Bool) :
    eval fuel env (Expr.litBool b) = some (Val.bool b) := by rfl

@[simp] theorem eval_litStr (fuel : Nat) (env : Env) (s : String) :
    eval fuel env (Expr.litStr s) = some (Val.str s) := by rfl

@[simp] theorem eval_litUnit (fuel : Nat) (env : Env) :
    eval fuel env Expr.litUnit = some Val.unit := by rfl

@[simp] theorem eval_var (fuel : Nat) (env : Env) (x : String) :
    eval fuel env (Expr.var x) = Env.lookup env x := by rfl

@[simp] theorem eval_pureE (fuel : Nat) (env : Env) (e : Expr) :
    eval fuel env (Expr.pureE e) = eval fuel env e := by rfl

/-! ## Compound expression reduction rules -/

theorem eval_binOp_succ (n : Nat) (env : Env) (op : BinOp) (l r : Expr) :
    eval (n + 1) env (Expr.binOp op l r) =
    match eval n env l, eval n env r with
    | some vl, some vr => evalBinOp op vl vr
    | _, _ => none := by rfl

theorem eval_letE_succ (n : Nat) (env : Env) (x : String) (init body : Expr) :
    eval (n + 1) env (Expr.letE x init body) =
    match eval n env init with
    | some vi => eval n (Env.extend env x vi) body
    | none => none := by rfl

theorem eval_ite_succ (n : Nat) (env : Env) (cond th el : Expr) :
    eval (n + 1) env (Expr.ite cond th el) =
    match eval n env cond with
    | some (Val.bool true)  => eval n env th
    | some (Val.bool false) => eval n env el
    | _ => none := by rfl

/-! ## Derived reduction rules -/

theorem eval_binOp_step (n : Nat) (env : Env) (op : BinOp) (l r : Expr)
    (vl vr : Val) (vres : Val)
    (hl : eval n env l = some vl) (hr : eval n env r = some vr)
    (hop : evalBinOp op vl vr = some vres) :
    eval (n + 1) env (Expr.binOp op l r) = some vres := by
  simp [eval, hl, hr, hop]

theorem eval_letE_step (n : Nat) (env : Env) (x : String) (init body : Expr)
    (vi vb : Val)
    (hinit : eval n env init = some vi) (hbody : eval n (Env.extend env x vi) body = some vb) :
    eval (n + 1) env (Expr.letE x init body) = some vb := by
  simp [eval, hinit, hbody]

theorem eval_ite_true_step (n : Nat) (env : Env) (cond th el : Expr) (v : Val)
    (hcond : eval n env cond = some (Val.bool true)) (hth : eval n env th = some v) :
    eval (n + 1) env (Expr.ite cond th el) = some v := by
  simp [eval, hcond, hth]

theorem eval_ite_false_step (n : Nat) (env : Env) (cond th el : Expr) (v : Val)
    (hcond : eval n env cond = some (Val.bool false)) (hel : eval n env el = some v) :
    eval (n + 1) env (Expr.ite cond th el) = some v := by
  simp [eval, hcond, hel]

/-! ## Seq evaluation properties -/

theorem eval_seq_nil (fuel : Nat) (env : Env) :
    eval fuel env (Expr.seq []) = some Val.unit := by rfl

theorem eval_seq_singleton (fuel : Nat) (env : Env) (e : Expr) :
    eval fuel env (Expr.seq [e]) = eval fuel env e := by rfl

theorem eval_seq_cons_succ (n : Nat) (env : Env) (e : Expr) (e2 : Expr) (es : List Expr)
    (v1 : Val) (he : eval n env e = some v1) :
    eval (n + 1) env (Expr.seq (e :: e2 :: es)) =
    eval.evalSeq n env (e2 :: es) := by
  simp [eval, eval.evalSeq, he]

/-! ## BinOp algebraic properties -/

theorem evalBinOp_concat_assoc (a b c : String) :
    evalBinOp .concat (Val.str (a ++ b)) (Val.str c) =
    evalBinOp .concat (Val.str a) (Val.str (b ++ c)) := by
  simp [evalBinOp, String.append_assoc]

theorem evalBinOp_and_comm (a b : Bool) :
    evalBinOp .and_ (Val.bool a) (Val.bool b) =
    evalBinOp .and_ (Val.bool b) (Val.bool a) := by
  simp [evalBinOp, Bool.and_comm]

theorem evalBinOp_or_comm (a b : Bool) :
    evalBinOp .or_ (Val.bool a) (Val.bool b) =
    evalBinOp .or_ (Val.bool b) (Val.bool a) := by
  simp [evalBinOp, Bool.or_comm]

theorem evalBinOp_eq_refl_str (s : String) :
    evalBinOp .eq (Val.str s) (Val.str s) = some (Val.bool true) := by
  simp [evalBinOp, beq_self_eq_true]

theorem evalBinOp_eq_refl_bool (b : Bool) :
    evalBinOp .eq (Val.bool b) (Val.bool b) = some (Val.bool true) := by
  cases b <;> rfl

theorem evalBinOp_concat_empty_left (s : String) :
    evalBinOp .concat (Val.str "") (Val.str s) = some (Val.str s) := by
  simp [evalBinOp]

/-! ## Environment variable resolution -/

theorem eval_var_extend_same (fuel : Nat) (env : Env) (x : String) (v : Val) :
    eval fuel (Env.extend env x v) (Expr.var x) = some v := by
  simp [eval, Env.lookup_extend_same]

theorem eval_var_extend_diff (fuel : Nat) (env : Env) (x y : String) (v : Val) (h : x ≠ y) :
    eval fuel (Env.extend env x v) (Expr.var y) = eval fuel env (Expr.var y) := by
  simp [eval, Env.lookup_extend_diff env x y v h]

/-! ## Let-as-environment-extension -/

theorem let_env_extension (n : Nat) (env : Env) (x : String) (init body : Expr) (vi : Val)
    (hinit : eval n env init = some vi) :
    eval (n + 1) env (Expr.letE x init body) = eval n (Env.extend env x vi) body := by
  simp [eval, hinit]

/-! ## Pure wrapping is identity -/

theorem pureE_identity (fuel : Nat) (env : Env) (e : Expr) :
    eval fuel env (Expr.pureE e) = eval fuel env e := rfl

/-! ## Conversion to/from TSValue -/

def Val.toTSValue : Val → TSValue
  | Val.num n  => TSValue.tsNum n
  | Val.bool b => TSValue.tsBool b
  | Val.str s  => TSValue.tsStr s
  | Val.unit   => TSValue.tsNull

def Val.ofTSValue : TSValue → Option Val
  | TSValue.tsNum n  => some (Val.num n)
  | TSValue.tsBool b => some (Val.bool b)
  | TSValue.tsStr s  => some (Val.str s)
  | TSValue.tsNull   => some Val.unit
  | _                => none

theorem Val.roundtrip_num (n : Float) : Val.ofTSValue (Val.toTSValue (Val.num n)) = some (Val.num n) := rfl
theorem Val.roundtrip_bool (b : Bool) : Val.ofTSValue (Val.toTSValue (Val.bool b)) = some (Val.bool b) := rfl
theorem Val.roundtrip_str (s : String) : Val.ofTSValue (Val.toTSValue (Val.str s)) = some (Val.str s) := rfl
theorem Val.roundtrip_unit : Val.ofTSValue (Val.toTSValue Val.unit) = some Val.unit := rfl

theorem Val.toTSValue_injective (v1 v2 : Val) (h : Val.toTSValue v1 = Val.toTSValue v2) : v1 = v2 := by
  cases v1 <;> cases v2 <;> simp_all [Val.toTSValue]

end TSLean.Proofs.Semantics
