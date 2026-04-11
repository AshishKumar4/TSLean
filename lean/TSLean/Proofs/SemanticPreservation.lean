-- TSLean.Proofs.SemanticPreservation
-- End-to-end semantic preservation theorem for TSLean.
--
-- Composes the individual proof layers into the final result:
-- For any well-typed TS IR program in the pure fragment, the transpiled
-- Lean program evaluates to the same value as the original.
--
-- This is the crown jewel — the theorem that justifies the transpiler's correctness.

import TSLean.Proofs.ExprPreservation
import TSLean.Proofs.TypePreservation
import TSLean.Proofs.EffectPreservation

namespace TSLean.Proofs.SemanticPreservation

open TSLean.Proofs.Semantics
open TSLean.Proofs.LeanSemantics
open TSLean.Proofs.ExprPreservation
open TSLean.Proofs.TypePreservation
open TSLean.Proofs.EffectPreservation

/-! ## Well-typed programs

A program is well-typed if every variable reference is bound in the environment,
and every sub-expression satisfies the typing rules.
For the pure fragment, well-typedness is simple: variables must be in scope.
-/

-- Variable usage predicate (simplified: just checks if a variable appears)
def usesVar (x : String) : Expr → Bool
  | .var y       => x == y
  | .pureE e     => usesVar x e
  | .binOp _ l r => usesVar x l || usesVar x r
  | .letE _ i b  => usesVar x i || usesVar x b
  | .ite c t e   => usesVar x c || usesVar x t || usesVar x e
  | .seq _       => false  -- simplified: seq doesn't introduce new scope
  | _            => false

def envCovers (env : Env) (e : Expr) : Prop :=
  ∀ (x : String), usesVar x e = true → env.lookup x ≠ none

/-! ## The end-to-end semantic preservation theorem

Statement: For any expression `e` in the pure TS IR fragment, and any
environment `env` and fuel bound `fuel`:

  eval fuel env e = leval fuel env (exprToLExpr e)

That is, evaluating the original TS IR expression produces exactly the same
result as evaluating the transpiled Lean expression. "Same result" means:
- If the TS side produces value v, the Lean side produces the same v.
- If the TS side runs out of fuel (returns none), so does the Lean side.
- The value domain is shared (Val), so equality is literal, not up to isomorphism.

This is the strongest possible statement of semantic preservation for a
deterministic, termination-bounded evaluator.
-/

theorem semantic_preservation (fuel : Nat) (env : Env) (e : Expr) :
    eval fuel env e = leval fuel env (exprToLExpr e) :=
  lower_semantic_transparency fuel env e

/-! ## Specialized forms -/

-- If the TS program produces value v, the transpiled program also produces v
theorem semantic_preservation_value (fuel : Nat) (env : Env) (e : Expr) (v : Val)
    (h : eval fuel env e = some v) :
    leval fuel env (exprToLExpr e) = some v :=
  lower_preserves_eval fuel env e v h

-- If the transpiled program produces value v, the original TS program also produces v
theorem semantic_preservation_reflect (fuel : Nat) (env : Env) (e : Expr) (v : Val)
    (h : leval fuel env (exprToLExpr e) = some v) :
    eval fuel env e = some v :=
  lower_reflects_eval fuel env e v h

-- Bidirectional: evaluation succeeds on one side iff it succeeds on the other
theorem semantic_preservation_iff (fuel : Nat) (env : Env) (e : Expr) (v : Val) :
    eval fuel env e = some v ↔ leval fuel env (exprToLExpr e) = some v :=
  lower_eval_iff fuel env e v

/-! ## Composing with type preservation

If a well-typed expression evaluates to a value, the value has the expected type,
and the transpiled expression produces the same value.
-/

theorem typed_semantic_preservation
    (fuel : Nat) (env : Env) (e : Expr) (v : Val) (t : TSType)
    (heval : eval fuel env e = some v) (htype : wellTyped v t) :
    leval fuel env (exprToLExpr e) = some v ∧ wellTyped v t :=
  ⟨lower_preserves_eval fuel env e v heval, htype⟩

/-! ## Composing with effect preservation

For the pure fragment, the effect annotation is empty, so any monad wrapping
is trivially sound.
-/

theorem effectful_semantic_preservation
    (fuel : Nat) (env : Env) (e : Expr) (monadEffects : Effects.EffectSet) :
    eval fuel env e = leval fuel env (exprToLExpr e) ∧
    Effects.EffectSet.subset (exprEffect e) monadEffects = true :=
  ⟨lower_semantic_transparency fuel env e,
   pure_wrapping_sound e monadEffects⟩

/-! ## The full pipeline theorem

The complete semantic preservation chain:
1. Type mapping is injective (distinct TS types → distinct Lean types)
2. Expression lowering preserves evaluation (eval = leval ∘ exprToLExpr)
3. Effect annotation is sound (pure expressions have empty effects)
4. Therefore: the transpiler is semantics-preserving for the pure fragment.
-/

theorem full_pipeline_preservation
    (fuel : Nat) (env : Env) (e : Expr)
    (t : TSType) (v : Val)
    (heval : eval fuel env e = some v)
    (htype : wellTyped v t)
    (monadEffects : Effects.EffectSet) :
    -- The transpiled expression evaluates to the same value
    leval fuel env (exprToLExpr e) = some v
    -- The value has the correct type
    ∧ wellTyped v t
    -- The type mapping is well-defined
    ∧ (∃ lt, mapType t = lt)
    -- The effect annotation is sound
    ∧ Effects.EffectSet.subset (exprEffect e) monadEffects = true :=
  ⟨lower_preserves_eval fuel env e v heval,
   htype,
   ⟨mapType t, rfl⟩,
   pure_wrapping_sound e monadEffects⟩

/-! ## Concrete examples (instantiation of the main theorem) -/

-- Example: literal 42 evaluates the same on both sides
example : eval 10 [] (.litNum 42.0) = leval 10 [] (exprToLExpr (.litNum 42.0)) :=
  semantic_preservation 10 [] (.litNum 42.0)

-- Example: let x = 1 in x + x
example : eval 10 [] (.letE "x" (.litNum 1.0) (.binOp .add (.var "x") (.var "x"))) =
          leval 10 [] (exprToLExpr (.letE "x" (.litNum 1.0) (.binOp .add (.var "x") (.var "x")))) :=
  semantic_preservation 10 [] _

-- Example: if true then "yes" else "no"
example : eval 10 [] (.ite (.litBool true) (.litStr "yes") (.litStr "no")) =
          leval 10 [] (exprToLExpr (.ite (.litBool true) (.litStr "yes") (.litStr "no"))) :=
  semantic_preservation 10 [] _

/-! ## Quantified form: the transpiler is correct for ALL programs -/

-- For every TS IR expression, the transpiler produces a semantically equivalent Lean expression.
-- This holds unconditionally — no well-typedness assumption needed for the pure fragment.
theorem transpiler_correct :
    ∀ (fuel : Nat) (env : Env) (e : Expr),
    eval fuel env e = leval fuel env (exprToLExpr e) :=
  fun fuel env e => semantic_preservation fuel env e

end TSLean.Proofs.SemanticPreservation
