-- TSLean.Proofs.ExprPreservation
-- THE KEY THEOREM: lowering from Expr to LExpr preserves evaluation.
-- eval fuel env e = leval fuel env (exprToLExpr e) for all fuel, env, e.

import TSLean.Proofs.LeanSemantics

namespace TSLean.Proofs.ExprPreservation

open TSLean.Proofs.Semantics
open TSLean.Proofs.LeanSemantics

/-! ## Core: simultaneous induction using Expr.rec

Expr.rec provides motives for both Expr and List Expr simultaneously,
solving the mutual recursion between expression evaluation and sequence
evaluation. We use it to prove agreement at a given fuel level,
assuming agreement at all lower fuel levels.
-/

-- Given agreement at fuel < m, prove agreement at fuel f ≤ m for all expressions AND lists.
-- Uses Expr.rec to handle the nested inductive.
private theorem agree_both (m : Nat)
    (ih_lo : ∀ (f : Nat) (e : Env) (x : Expr), f < m →
      eval f e x = leval f e (exprToLExpr x))
    (ih_lo_seq : ∀ (f : Nat) (e : Env) (xs : List Expr), f < m →
      eval.evalSeq f e xs = leval.levalSeq f e (xs.map exprToLExpr)) :
    (∀ (f : Nat) (env : Env) (e : Expr), f ≤ m →
      eval f env e = leval f env (exprToLExpr e)) ∧
    (∀ (f : Nat) (env : Env) (es : List Expr), f ≤ m →
      eval.evalSeq f env es = leval.levalSeq f env (es.map exprToLExpr)) := by
  -- We prove both by showing every Expr satisfies the expr-motive
  -- and every List Expr satisfies the list-motive.
  suffices hexpr : ∀ (e : Expr) (f : Nat) (env : Env), f ≤ m →
      eval f env e = leval f env (exprToLExpr e) by
    suffices hlist : ∀ (es : List Expr) (f : Nat) (env : Env), f ≤ m →
        eval.evalSeq f env es = leval.levalSeq f env (es.map exprToLExpr) by
      exact ⟨fun f env e hf => hexpr e f env hf, fun f env es hf => hlist es f env hf⟩
    intro es
    induction es with
    | nil => intro f env _; simp [eval.evalSeq, leval.levalSeq]
    | cons e rest ihes =>
      intro f env hf
      cases rest with
      | nil =>
        simp only [eval.evalSeq, leval.levalSeq, List.map]
        exact hexpr e f env hf
      | cons e2 rest' =>
        match hfm : f with
        | 0 => simp [eval.evalSeq, leval.levalSeq, List.map]
        | k + 1 =>
          have hk : k < m := by omega
          simp only [eval.evalSeq, leval.levalSeq, List.map, ih_lo k env e hk]
          match leval k env (exprToLExpr e) with
          | some _ => exact ih_lo_seq k env (e2 :: rest') hk
          | none => rfl
  -- Now prove hexpr by Expr.rec
  intro e
  apply @Expr.rec
    (fun e => ∀ (f : Nat) (env : Env), f ≤ m →
      eval f env e = leval f env (exprToLExpr e))
    (fun es => ∀ (f : Nat) (env : Env), f ≤ m →
      eval.evalSeq f env es = leval.levalSeq f env (es.map exprToLExpr))
  -- litNum
  · intro n f env _; simp [eval, leval, exprToLExpr]
  -- litBool
  · intro b f env _; simp [eval, leval, exprToLExpr]
  -- litStr
  · intro s f env _; simp [eval, leval, exprToLExpr]
  -- litUnit
  · intro f env _; simp [eval, leval, exprToLExpr]
  -- var
  · intro x f env _; simp [eval, leval, exprToLExpr]
  -- binOp
  · intro op l r _ _ f env hf
    match hfm : f with
    | 0 => simp [eval, leval, exprToLExpr]
    | k + 1 =>
      have hk : k < m := by omega
      show eval (k+1) env (Expr.binOp op l r) = leval (k+1) env (exprToLExpr (Expr.binOp op l r))
      simp only [eval, leval, exprToLExpr]
      have hl := ih_lo k env l hk
      have hr := ih_lo k env r hk
      rw [hl, hr]
      rfl
  -- letE
  · intro x init body _ _ f env hf
    match hfm : f with
    | 0 => simp [eval, leval, exprToLExpr]
    | k + 1 =>
      have hk : k < m := by omega
      simp only [eval, leval, exprToLExpr, ih_lo k env init hk]
      match leval k env (exprToLExpr init) with
      | some vi => exact ih_lo k (Env.extend env x vi) body hk
      | none => rfl
  -- ite
  · intro cond th el _ _ _ f env hf
    match hfm : f with
    | 0 => simp [eval, leval, exprToLExpr]
    | k + 1 =>
      have hk : k < m := by omega
      simp only [eval, leval, exprToLExpr, ih_lo k env cond hk]
      match leval k env (exprToLExpr cond) with
      | some (Val.bool true)  => exact ih_lo k env th hk
      | some (Val.bool false) => exact ih_lo k env el hk
      | some (Val.num _) | some (Val.str _) | some Val.unit | none => rfl
  -- seq
  · intro stmts ihstmts f env hf
    simp only [eval, leval, exprToLExpr]
    exact ihstmts f env hf
  -- pureE
  · intro e' ihe' f env hf
    simp only [eval, leval, exprToLExpr]
    exact ihe' f env hf
  -- List.nil
  · intro f env _; simp [eval.evalSeq, leval.levalSeq]
  -- List.cons
  · intro e es ihe ihes f env hf
    cases es with
    | nil =>
      simp only [eval.evalSeq, leval.levalSeq, List.map]
      exact ihe f env hf
    | cons e2 rest =>
      match hfm : f with
      | 0 => simp [eval.evalSeq, leval.levalSeq, List.map]
      | k + 1 =>
        have hk : k < m := by omega
        simp only [eval.evalSeq, leval.levalSeq, List.map, ih_lo k env e hk]
        match leval k env (exprToLExpr e) with
        | some _ => exact ih_lo_seq k env (e2 :: rest) hk
        | none => rfl

/-! ## Strong induction on fuel -/

private theorem fuel_induction (n : Nat) :
    (∀ (f : Nat) (env : Env) (e : Expr), f < n →
      eval f env e = leval f env (exprToLExpr e)) ∧
    (∀ (f : Nat) (env : Env) (es : List Expr), f < n →
      eval.evalSeq f env es = leval.levalSeq f env (es.map exprToLExpr)) := by
  induction n with
  | zero =>
    exact ⟨fun f _ _ hf => absurd hf (Nat.not_lt_zero _),
           fun f _ _ hf => absurd hf (Nat.not_lt_zero _)⟩
  | succ m ihm =>
    obtain ⟨ihm_e, ihm_s⟩ := ihm
    have hab := agree_both m ihm_e ihm_s
    exact ⟨fun f env e hf => hab.1 f env e (Nat.lt_succ_iff.mp hf),
           fun f env es hf => hab.2 f env es (Nat.lt_succ_iff.mp hf)⟩

/-! ## The main preservation theorem -/

theorem lower_semantic_transparency (fuel : Nat) (env : Env) (e : Expr) :
    eval fuel env e = leval fuel env (exprToLExpr e) :=
  (fuel_induction (fuel + 1)).1 fuel env e (Nat.lt_succ_of_le (Nat.le_refl _))

/-! ## Direct corollaries -/

theorem lower_preserves_eval (fuel : Nat) (env : Env) (e : Expr) (v : Val)
    (h : eval fuel env e = some v) :
    leval fuel env (exprToLExpr e) = some v := by
  rw [← lower_semantic_transparency]; exact h

theorem lower_reflects_eval (fuel : Nat) (env : Env) (e : Expr) (v : Val)
    (h : leval fuel env (exprToLExpr e) = some v) :
    eval fuel env e = some v := by
  rw [lower_semantic_transparency]; exact h

theorem lower_eval_iff (fuel : Nat) (env : Env) (e : Expr) (v : Val) :
    eval fuel env e = some v ↔ leval fuel env (exprToLExpr e) = some v :=
  ⟨lower_preserves_eval fuel env e v, lower_reflects_eval fuel env e v⟩

theorem lower_none_iff (fuel : Nat) (env : Env) (e : Expr) :
    eval fuel env e = none ↔ leval fuel env (exprToLExpr e) = none := by
  constructor
  · intro h; rw [← lower_semantic_transparency]; exact h
  · intro h; rw [lower_semantic_transparency]; exact h

end TSLean.Proofs.ExprPreservation
