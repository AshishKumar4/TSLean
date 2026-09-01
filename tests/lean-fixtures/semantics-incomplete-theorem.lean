import TSLean.LeanToTypeScript.Semantics.Opcode

/-!
Negative fixture: an incomplete theorem type.

`boolAndAtTrue` is true, but it covers only the `left = true` half of what `bool.and` owes. Offering
it where the opcode's obligation is required has to fail, which is what keeps a weakened theorem out
of `Opcode.registry`.

`scripts/check-semantics-registry.mjs --self-test` requires this file to fail.
-/

namespace TSLean.LeanToTypeScript.Semantics.SemanticsFixture

open TSLean.JS

theorem boolAndAtTrue (runtime : Runtime)
    (holds : Assumption.Holds runtime Ir.Opcode.boolAnd.requires) :
    ∀ right : Bool,
      Encode.bool (true && right) = runtime.boolAnd (Encode.bool true) (Encode.bool right) := by
  intro right
  rw [holds.1.1 (Encode.bool true) (Encode.bool right)]
  simp [Encode.bool, Model.boolAnd, Value.toBoolean, Primitive.toBoolean]

theorem registryWithIncompleteTheorem (runtime : Runtime) :
    Ir.Opcode.boolAnd.Obligation runtime := boolAndAtTrue runtime

end TSLean.LeanToTypeScript.Semantics.SemanticsFixture
