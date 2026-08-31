import TSLean.LeanToTypeScript.Semantics.Preservation

/-!
Negative fixture: an arrow registry row naming the wrong theorem.

`Preservation.registry` is a total function on `Ir.Op`, so every operation names the theorem that
discharges it. This file offers the `lambda` theorem where the `apply` obligation is required, which
is the shape a row pointing at the wrong theorem — or at a theorem that does not exist yet — would
have. The elaborator has to refuse it.

`scripts/check-semantics-registry.mjs --self-test` requires this file to fail.
-/

namespace TSLean.LeanToTypeScript.Semantics.SemanticsFixture

theorem applyFromLambda : Preservation.Op.Preserves .apply := Preservation.lambda

end TSLean.LeanToTypeScript.Semantics.SemanticsFixture
