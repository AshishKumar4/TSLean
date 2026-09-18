/-!
# Structures that make their illegal states unrepresentable

Every declaration here is a shape `AgentCore/Kernel` uses to keep an invariant inside a type rather
than beside it, written small enough to compile end to end and to enumerate.

A `Prop` field holds no data. Lean's proof irrelevance is definitional, so the surviving fields
determine the value the record came from, and the emitted record is the data alone —
`Semantics.ProofErasure` states and proves that, and `Export.lean` performs it. What this module
carries is one declaration per way a program meets such a field:

* `Window.fits`, typed by the `Prop`-**sorted** definition `Fits`, which the exporter skips exactly
  as it skips a theorem — the shape `PlacementPin.chosen` has;
* `Gate.openedHasLimit`, a **function-typed** `Prop` field — the shape `TurnLease.heldHasExpiry` has;
* `Tally.allPositive`, a **∀-quantified** `Prop` field — the shape `RecordCodec.roundTrip` has;
* `build`, a dependent `if` whose bound hypothesis *is* the proof the field needs;
* `widened`, a `{ record with … }` update that re-proves the invariant for a changed field;
* `emptyTally`, an anonymous constructor whose proof argument is discharged by a tactic.

A root may **return** a proof-carrying record and may reach one through the closure. It may not
**accept** one: reading the data back does not establish the invariant, and the compiler refuses
that boundary rather than casting past it.
-/

namespace TSLean.Examples.Roundtrip.Invariant

/-- The ceiling a window has to fit inside. -/
def ceiling : Nat := 8

/-- Whether a window starting at `start` and `width` wide fits under the ceiling, stated rather
than decided.

A `Prop`-sorted declaration: its type's result is `Prop`, so it names a proposition instead of
computing one. It has no runtime image, the exporter skips it, and that skip is what lets a module
state its own invariants beside the definitions that keep them — a refusal here would stop every
declaration in the same closure. -/
def Fits (start width : Nat) : Prop := start + width ≤ ceiling

/-- A window under the ceiling: where it starts, how wide it is, and the proof it fits.

The proof is a `Prop` field, so the extracted image is the two numbers the runtime holds and
nothing else. A window that does not fit cannot be built at all. -/
structure Window where
  start : Nat
  width : Nat
  /-- The window fits under the ceiling. The field's type is a `Prop`-sorted *definition*, which is
  how the kernel names an invariant it states in more than one place. -/
  fits : Fits start width

namespace Window

/-- The first position past the window. -/
def stop (window : Window) : Nat := window.start + window.width

/-- **The window is inside the ceiling.** The `Prop` field is exactly this fact, so no window that
was built at all reaches past the ceiling — including one a caller reads back out of the generated
package, because the only way to obtain one is the constructor that proves it. -/
theorem stop_le_ceiling (window : Window) : window.stop ≤ ceiling := window.fits

end Window

/-- A gate that promises a positive limit whenever it is open.

The `Prop` field is an implication, so its type is a *function* type. It is still one irrelevant
proof: `Prop`-valued arrows are `Prop`s, and proof irrelevance does not care about the shape of the
proposition. -/
structure Gate where
  opened : Bool
  limit : Nat
  /-- An open gate has room. -/
  openedHasLimit : opened = true → 0 < limit

/-- A tally whose entries are all positive.

The `Prop` field is ∀-quantified over the data beside it, which is the shape a law about a codec or
a collection takes. Erasure drops it for the same reason: one proof, irrelevant. -/
structure Tally where
  counts : List Nat
  /-- No entry is zero. -/
  allPositive : ∀ count ∈ counts, 0 < count

/-- Build a window, refusing one that does not fit.

A dependent `if`: the hypothesis `fits` the decision binds *is* the proof the `Prop` field needs,
and the anonymous constructor is what fills the field with it. Erasure drops both, so the emitted
branch builds the record from the two numbers under the same decision. -/
def build (start width : Nat) : Option Window :=
  if fits : start + width ≤ ceiling then some ⟨start, width, fits⟩ else none

/-- Widen a window by one, refusing the step that would leave the ceiling.

A `{ record with … }` update: `start` is kept from the window that was given and the invariant is
re-proved for the new width, which is the shape a kernel transition has. -/
def widened (window : Window) : Option Window :=
  if fits : window.start + (window.width + 1) ≤ ceiling then
    some { window with width := window.width + 1, fits := fits }
  else
    none

/-- The window's width, read off the record the compiler emits: one of the two fields that survived
erasure. -/
def widthOf (window : Window) : Nat := window.width

/-- Build a window and widen it, refusing whichever step leaves the ceiling. -/
def widenedFrom (start width : Nat) : Option Window :=
  match build start width with
  | some window => widened window
  | none => none

/-- The width a built window has after one widening, or zero where either step is refused. -/
def widthAfterWidening (start width : Nat) : Nat :=
  match widenedFrom start width with
  | some window => widthOf window
  | none => 0

/-- A shut gate, whose promise holds because it is never open. The proof argument is discharged by
a tactic and erased, so the emitted record is the flag and the number. -/
def shutGate (limit : Nat) : Gate := ⟨false, limit, by simp⟩

/-- Whether the gate is open, read off the emitted record. -/
def gateOpened (gate : Gate) : Bool := gate.opened

/-- Whether a shut gate reports itself open. -/
def shutGateOpened (limit : Nat) : Bool := gateOpened (shutGate limit)

/-- The empty tally, whose law holds because it has no entries. -/
def emptyTally : Tally := ⟨[], by simp⟩

/-- How many entries a tally holds, read off the emitted record. -/
def tallySize (tally : Tally) : Nat := tally.counts.length

/-- How many entries the empty tally holds. -/
def emptyTallySize : Nat := tallySize emptyTally

/-- How wide the widest window starting here can be. -/
def room (start : Nat) : Nat := ceiling - start

/-- **Widening keeps the start.** The update reads `start` off the record it was handed, so a
widened window begins where the original did. -/
theorem widened_start (window : Window) (widerWindow : Window)
    (stepped : widened window = some widerWindow) : widerWindow.start = window.start := by
  unfold widened at stepped
  by_cases fits : window.start + (window.width + 1) ≤ ceiling
  · simp only [fits, dite_true, Option.some.injEq] at stepped
    exact (stepped ▸ rfl)
  · simp [fits] at stepped

/-- **A built window is the window that was asked for.** The two numbers survive construction, so
the record a caller gets back is the one the arguments named. -/
theorem build_width (start width : Nat) (window : Window)
    (built : build start width = some window) : window.width = width := by
  unfold build at built
  by_cases fits : start + width ≤ ceiling
  · simp only [fits, dite_true, Option.some.injEq] at built
    exact (built ▸ rfl)
  · simp [fits] at built

end TSLean.Examples.Roundtrip.Invariant
