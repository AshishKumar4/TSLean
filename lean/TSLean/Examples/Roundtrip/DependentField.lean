/-
The adversarial case for index erasure: a type former whose index decides what its field holds.

`Payload` is a function from a `Bool` to a type, so `Slot true` carries a `String` and `Slot false`
carries a `Nat`. Erasing `flag` and emitting one TypeScript type would claim those two records have
the same shape, which is false, and a decoder written against the claim would read the wrong field.
This is the case the compiler must REFUSE, and it must refuse it by name.

It is worth writing down why refusing it is not optional. Lean's own compiler erases the index here
too: measured under Lean 4.33.1, `Lean.Compiler.LCNF.toMonoType` answers `lcAny` for both
`Slot true` and `Slot false`, the same answer it gives a genuinely phantom index. Lean can afford
that because its runtime boxes every value and carries no types at all. A target that emits types
cannot, so the refusal rests on this compiler's own obligation — every surviving field's type is
index-independent — and not on Lean's erasure.

Nothing here is expected to compile to TypeScript. The module exists so the refusal is exercised
rather than asserted.
-/

namespace TSLean.Examples.Roundtrip.DependentField

/-- The index decides the type. -/
def Payload : Bool → Type
  | true => String
  | false => Nat

/-- A data field whose type mentions the index. `erasedDataParameters` refuses this. -/
structure Slot (flag : Bool) where
  payload : Payload flag

/-- A reader, so the refusal has a declaration to name. -/
def textOf (slot : Slot true) : String := slot.payload

end TSLean.Examples.Roundtrip.DependentField
