-- TSLean.Verification.ProofObligation
import TSLean.Runtime.Basic

namespace TSLean.Verification
open TSLean

/-- A proof obligation: a proposition that must hold -/
structure ProofObligation where
  name : String
  prop : Prop
  proof : prop

/-- Array index in bounds -/
def idx_in_bounds (n i : Nat) (h : i < n) : True := trivial

/-- Division by nonzero -/
def divisor_nonzero (n : Nat) (h : n ≠ 0) : True := trivial

/-- Option value is some -/
def val_is_some {α} (o : Option α) (h : o.isSome = true) : True := trivial

/-- Invariant preserved by operation -/
def invariant_preserved {σ} (inv : σ → Prop) (s s' : σ) (h : inv s) (step : inv s → inv s') : inv s' :=
  step h

end TSLean.Verification
