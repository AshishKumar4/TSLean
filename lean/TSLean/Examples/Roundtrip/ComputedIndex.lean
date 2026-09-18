/-
The third adversarial case: a use site whose index is computed.

`Label` itself is fine — `tag` reaches no field, so the erasure is sound and `PhantomIndex` admits
exactly this shape. What is refused here is the *use site*: `chosen` names the type
`Label (flip tag)`, whose index is the result of a call. The index is erased, so the emitted program
never evaluates `flip tag`, and there is then no constructor and no parameter a reader could name
the erased index by.

That refusal is about the exporter's record rather than about soundness. Erasing a computed index
would still be sound — the obligation on `Label` holds at every index, computed or not. But an
erased index that cannot be recorded leaves the emitted type unrelatable to the Lean type it stands
for, and a partial record is worse than a refusal: a checker reading `Label` back would have to
guess which index it was written at. So the exporter records every index it erases, in exactly two
forms — a nullary constructor, or one of the declaration's own emitted parameters — and refuses the
residue by name.

Everything here except the computed index is inside the fragment, so the refusal has exactly one
cause. Nothing in this module is expected to compile.
-/

namespace TSLean.Examples.Roundtrip.ComputedIndex

/-- Nullary constructors only, so an index is a name. -/
inductive Tag where
  | run
  | turn
  deriving DecidableEq, Repr

/-- The payload, an enumeration so that nothing but the index is outside the fragment. -/
inductive Level where
  | low
  | high
  deriving DecidableEq, Repr

/-- A genuinely phantom index: `tag` reaches no field, exactly as in `PhantomIndex`. -/
structure Label (tag : Tag) where
  level : Level
  deriving DecidableEq

/-- A computation on tags. -/
def flip : Tag → Tag
  | .run => .turn
  | .turn => .run

/-- The refused shape: the result type's index is a call, not a name and not a parameter. -/
def chosen (tag : Tag) (level : Level) : Label (flip tag) := { level := level }

end TSLean.Examples.Roundtrip.ComputedIndex
