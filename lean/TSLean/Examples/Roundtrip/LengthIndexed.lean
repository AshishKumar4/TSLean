/-
The second adversarial case: a length-indexed container.

`Fixed n` holds a list constrained to have length `n`. The subtype's carrier is the same `List Nat`
at every index, so a compiler that read only the *carrier* would think the index erasable — and it
would be wrong in a way that matters, because `Fixed 3` and `Fixed 4` are different types whose
values are never interchangeable, and one emitted TypeScript type would say they are.

This is the case the plan names explicitly. `erasedDataParameters` refuses it because the field's
declared type mentions `size`, which is the right reason: the obligation is about the field's type
as declared, not about whatever the type happens to erase to. Reading the erasure instead of the
declaration is exactly the mistake that would admit this.

Like `DependentField`, nothing here is expected to compile.
-/

namespace TSLean.Examples.Roundtrip.LengthIndexed

/-- A list of a fixed length. The field's type mentions the index. -/
structure Fixed (size : Nat) where
  items : { values : List Nat // values.length = size }

/-- A reader, so the refusal has a declaration to name. -/
def firstOf (fixed : Fixed 3) : List Nat := fixed.items.val

end TSLean.Examples.Roundtrip.LengthIndexed
