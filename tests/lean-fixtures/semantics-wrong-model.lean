import TSLean.LeanToTypeScript.Semantics.Opcode

/-!
Negative fixture: a wrong target model.

`bool.and` is emitted as `left && right`. This file claims that form denotes `Bool.or`. The
assumption it consumes is the real one, so the only thing that can stop it is the model itself, and
the elaborator has to refuse the proof.

`scripts/check-semantics-registry.mjs --self-test` requires this file to fail.
-/

namespace TSLean.LeanToTypeScript.Semantics.SemanticsFixture

open TSLean.JS

theorem boolAndModelsOr (runtime : Runtime)
    (holds : Assumption.Holds runtime Ir.Opcode.boolAnd.requires) :
    ∀ left right : Bool,
      Encode.bool (left || right) = runtime.boolAnd (Encode.bool left) (Encode.bool right) := by
  intro left right
  rw [holds.1.1 (Encode.bool left) (Encode.bool right)]
  cases left <;> simp [Encode.bool, Model.boolAnd, Value.toBoolean, Primitive.toBoolean]

end TSLean.LeanToTypeScript.Semantics.SemanticsFixture
