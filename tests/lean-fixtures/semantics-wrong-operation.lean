import TSLean.LeanToTypeScript.Semantics.Preservation

/-!
Negative fixture: a wrong operation lowering.

`bool.and` lowers to `&&`. This file offers the `&&` row of the `operation` obligation where the `||`
lowering is claimed, which is the shape a registry entry pointing at the wrong operator would have.
The elaborator has to refuse it.

`scripts/check-semantics-registry.mjs --self-test` requires this file to fail.
-/

namespace TSLean.LeanToTypeScript.Semantics.SemanticsFixture

open Preservation

theorem boolAndLowersToOr (runtime : Runtime) (program : Ir.Program) (target : Target.Program)
    (fuel : Nat) (typeArguments : List Ir.Ty) (left right : Ir.Expr)
    (emittedLeft emittedRight : Target.Expr)
    (leftStep : Everywhere program target runtime fuel left emittedLeft)
    (rightStep : Everywhere program target runtime fuel right emittedRight) :
    Everywhere program target runtime fuel (.operation .boolAnd typeArguments [left, right])
      (.logicalOr emittedLeft emittedRight) :=
  (Preservation.operation program target fuel).1 typeArguments left right emittedLeft emittedRight
    leftStep rightStep

end TSLean.LeanToTypeScript.Semantics.SemanticsFixture
