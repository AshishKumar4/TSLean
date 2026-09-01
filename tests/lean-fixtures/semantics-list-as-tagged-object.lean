import TSLean.LeanToTypeScript.Semantics.Preservation

/-!
Negative fixture: a list lowered to a tagged object.

A `List` reaches the target as a dense array: `nil` is `[]` and `cons` is `[head, ...tail]`.
`constructorsOf` does give a list `nil` and `cons` constructors, but that is the surface a match
destructures, not the representation. This file reads it as the representation and claims `nil`
lowers to its own tag string, which is what an enum with no payload lowers to. The elaborator has to
refuse it.

`scripts/check-semantics-registry.mjs --self-test` requires this file to fail.
-/

namespace TSLean.LeanToTypeScript.Semantics.SemanticsFixture

open Preservation

theorem nilLowersToTag (runtime : Runtime) (program : Ir.Program) (target : Target.Program)
    (fuel : Nat) (element : Ir.Ty) :
    Everywhere program target runtime fuel (.variant (.list element) "nil" [])
      (.stringLit "nil") :=
  (Preservation.variant program target fuel).2.1 element

end TSLean.LeanToTypeScript.Semantics.SemanticsFixture
