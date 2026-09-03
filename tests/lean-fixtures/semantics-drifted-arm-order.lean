import TSLean.LeanToTypeScript.Semantics.Program

/-!
Negative fixture: a statement-form dispatch whose arms drift from declaration order.

`emitMatchStatements` reads each arm's payload field list positionally out of the declaration, so the
arm at position `i` names the fields of the constructor declared at position `i`. An arm order the
declaration does not have would bind another constructor's fields, and
`Preservation.EverywhereArms` is stated on exactly that positional correspondence: offering the arms
in the order this fixture writes them has to fail.

Every other obligation is taken as a hypothesis, so the only goal left open is the drift itself —
`[unheld, held] = held :: [unheld]`, which is `False`. `Compile.decidesInOrder` refuses the same
document at the lowering and `ir.ts` refuses it at the decoder; this is the place that would let a
wrong lowering through if the correspondence were merely assumed.

`scripts/check-semantics-registry.mjs --self-test` requires this file to fail.
-/

namespace TSLean.LeanToTypeScript.Semantics.SemanticsFixture

open TSLean.JS

/-- `Fixture.Lease`, whose declaration order is `unheld` then `held`. -/
def leaseConstructors : List Ir.Constructor :=
  [⟨"unheld", []⟩, ⟨"held", [⟨"exclusive", .boolean⟩]⟩]

/-- The arms in the other order, with the emitted arms drifted to match them. -/
theorem driftedArms (program : Ir.Program) (target : Target.Program) (runtime : Runtime)
    (fuel : Nat)
    (heldArm : Preservation.EverywhereBody program target runtime fuel (.varRef 0)
      (.ret (.binding 0)))
    (unheldArm : Preservation.EverywhereBody program target runtime fuel (.boolLit false)
      (.ret (.boolLit false))) :
    Preservation.EverywhereArms program target runtime fuel leaseConstructors
      [("held", .varRef 0), ("unheld", .boolLit false)]
      [("held", ["exclusive"], .ret (.binding 0)), ("unheld", [], .ret (.boolLit false))] := by
  unfold Preservation.EverywhereArms
  refine ⟨⟨"held", [⟨"exclusive", .boolean⟩]⟩, [⟨"unheld", []⟩], .ret (.binding 0),
    [("unheld", [], .ret (.boolLit false))], ?_, rfl, rfl, heldArm, ?_⟩
  · simp [leaseConstructors]
  · unfold Preservation.EverywhereArms
    exact ⟨⟨"unheld", []⟩, [], .ret (.boolLit false), [], rfl, rfl, rfl, unheldArm, ⟨rfl, rfl⟩⟩

end TSLean.LeanToTypeScript.Semantics.SemanticsFixture
