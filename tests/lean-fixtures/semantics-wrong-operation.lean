import TSLean.LeanToTypeScript.Semantics.Preservation

/-!
Negative fixture: a wrong operation lowering.

`and` lowers to `&&`. This file offers the `and` theorem where the `||` lowering is claimed, which is
the shape a registry entry pointing at the wrong operation would have. The elaborator has to refuse
it.

`scripts/check-semantics-registry.mjs --self-test` requires this file to fail.
-/

namespace TSLean.LeanToTypeScript.Semantics.SemanticsFixture

open Preservation

theorem boolAndLowersToOr (program : Ir.Program) (target : Target.Program) (fuel : Nat)
    (left right : Ir.Expr) (emittedLeft emittedRight : Target.Expr)
    (leftStep : Everywhere program target fuel left emittedLeft)
    (rightStep : Everywhere program target fuel right emittedRight) :
    Everywhere program target fuel (.boolAnd left right)
      (.logicalOr emittedLeft emittedRight) :=
  Preservation.boolAnd program target fuel left right emittedLeft emittedRight leftStep rightStep

end TSLean.LeanToTypeScript.Semantics.SemanticsFixture
