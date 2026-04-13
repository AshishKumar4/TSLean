-- TSLean.Verification.ProofObligation
import TSLean.Runtime.Basic

namespace TSLean.Verification
open TSLean

/-- A proof obligation: a proposition that must hold -/
structure ProofObligation where
  name : String
  prop : Prop
  proof : prop

/-- Invariant preserved by operation -/
def invariant_preserved {σ} (inv : σ → Prop) (s s' : σ) (h : inv s) (step : inv s → inv s') : inv s' :=
  step h

end TSLean.Verification
