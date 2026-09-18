import TSLean.LeanToTypeScript.Semantics.Erasure

/-!
# Erasing a `Prop` field, as theorems rather than as an assumption

`Export.lean` drops a structure's `Prop` fields on its way to the IR, so a record reaches the
emitted TypeScript with fewer fields than its Lean constructor declares. This module is why that is
sound, and it is *soundness as a theorem*: Lean's proof irrelevance is definitional, so every claim
below closes by `rfl` or by cases on a decision, and none of it is an assumption row.

The reasoning is a retraction, not an isomorphism, and the difference is the whole story:

* **`data`**, the map that keeps the surviving fields, is total and *determines* the value it came
  from — `record_determined_by_data`. That is what makes dropping the proof invisible to every
  program: a constructor answers the same value at every proof, and a projection of a data field
  answers the data.
* **The other direction needs the invariant as a hypothesis** — `record_reconstructed`. A caller
  holding the data alone has not established what the type asserts, which is exactly why the
  emitter refuses a *decode* boundary for such a record while keeping `toData` and `equals`.

The shape of the proposition never matters. A `Prop`-valued arrow is a `Prop`, a `∀` over one is a
`Prop`, and a `Prop` named by a definition is a `Prop`; the three named sections below say that at
the shapes `TurnLease.heldHasExpiry`, `RecordCodec.roundTrip` and `PlacementPin.chosen` have.

`dite_data_erasable` is the last piece: it is the theorem behind admitting a dependent `if` whose
bound hypothesis fills a proof field. The generated code decides the same condition and builds the
same data in each branch, so the data of the dependent `if` is the plain `if` of the two branches'
data.
-/

namespace TSLean.LeanToTypeScript.Semantics

namespace ProofErasure

/-! ## A record is its data

`construct` stands for a structure's constructor and `data` for the projection that keeps a
surviving field. A Lean structure gives both definitionally, so instantiating these at a real
structure discharges the hypotheses by `rfl` — the `Window`, `Gate` and `Tally` sections below do
exactly that.
-/

/-- A constructor answers the same value at every proof of the same invariant. This is the erasure:
the proof argument cannot change what is built, so the emitted constructor call does not take
one. -/
theorem construct_proof_irrelevant {α : Sort u} {invariant : α → Prop} {record : Sort v}
    (construct : ∀ value : α, invariant value → record) (value : α)
    (left right : invariant value) : construct value left = construct value right := rfl

/-- A data projection reads the data it was built from, whichever proof came with it. -/
theorem data_of_construct {α : Sort u} {invariant : α → Prop} {record : Sort v}
    (construct : ∀ value : α, invariant value → record) (data : record → α)
    (reads : ∀ (value : α) (held : invariant value), data (construct value held) = value)
    (value : α) (held : invariant value) : data (construct value held) = value :=
  reads value held

/--
**The surviving fields determine the record.** Two values of the structure with equal data are
equal, so nothing a program computes from a record can depend on the component erasure dropped.

This is the theorem the emitted `equals` is correct by: comparing the data fields *is* comparing
the values.
-/
theorem record_determined_by_data {α : Sort u} {invariant : α → Prop} {record : Sort v}
    (construct : ∀ value : α, invariant value → record) (data : record → α)
    (built : ∀ held : record, ∃ value, ∃ proof : invariant value, held = construct value proof)
    (left right : record) (same : data left = data right)
    (reads : ∀ (value : α) (held : invariant value), data (construct value held) = value) :
    left = right := by
  obtain ⟨leftValue, leftProof, leftBuilt⟩ := built left
  obtain ⟨rightValue, rightProof, rightBuilt⟩ := built right
  subst leftBuilt
  subst rightBuilt
  rw [reads leftValue leftProof, reads rightValue rightProof] at same
  subst same
  exact construct_proof_irrelevant construct leftValue leftProof rightProof

/--
**The record is rebuilt from its data and the invariant, and from nothing less.** Given a value's
own data and *any* proof that the data satisfies the invariant, the constructor answers exactly the
value the data came from.

The hypothesis `held : invariant (data value)` is the point. It is not derivable from the data — a
`String` is not a `Digest`, a `Nat` is not a `Revision` — so a decoder that read the data back out
of bytes would still owe it. That is why `fromData` does not exist for a proof-carrying record and
why `planBoundary` refuses a root that would need one.
-/
theorem record_reconstructed {α : Sort u} {invariant : α → Prop} {record : Sort v}
    (construct : ∀ value : α, invariant value → record) (data : record → α)
    (built : ∀ held : record, ∃ value, ∃ proof : invariant value, held = construct value proof)
    (reads : ∀ (value : α) (held : invariant value), data (construct value held) = value)
    (value : record) :
    ∀ held : invariant (data value), construct (data value) held = value := by
  obtain ⟨plain, proof, isBuilt⟩ := built value
  subst isBuilt
  -- The invariant's own argument is what is being rewritten, so the quantifier stays in the goal:
  -- `fun read => ∀ held : invariant read, construct read held = …` is a type-correct motive while
  -- `fun read => construct read held = …` is not.
  rw [reads plain proof]
  intro held
  exact construct_proof_irrelevant construct plain held proof

/--
**An update that re-proves the invariant agrees with every other proof of it.** `{ record with … }`
elaborates to the constructor applied to the fields it keeps and the fields it changes, with a fresh
proof for the invariant; the fresh proof cannot change the value, so the emitted update is the data
alone.
-/
theorem update_proof_irrelevant {α : Sort u} {invariant : α → Prop} {record : Sort v}
    (construct : ∀ value : α, invariant value → record) (step : α → α) (value : α)
    (left right : invariant (step value)) :
    construct (step value) left = construct (step value) right := rfl

/-! ## The shape of the proposition never matters

Three named shapes from the kernel, each a `Prop` and therefore each one irrelevant proof. There is
nothing to prove beyond that, which is the point: a field's *proposition* can be as complicated as
the law it states and the *field* is still weightless.
-/

/-- A **function-typed** `Prop` field, the shape `TurnLease.heldHasExpiry` has: an implication
between two decidable facts about the data beside it. -/
theorem implication_field_irrelevant {α : Sort u} {premise conclusion : α → Prop} {record : Sort v}
    (construct : ∀ value : α, (premise value → conclusion value) → record) (value : α)
    (left right : premise value → conclusion value) :
    construct value left = construct value right := rfl

/-- A **∀-quantified** `Prop` field, the shape `RecordCodec.roundTrip` has: a law quantified over
every input, stated about the functions the record carries. -/
theorem forall_field_irrelevant {α : Sort u} {index : Sort w} {law : α → index → Prop}
    {record : Sort v}
    (construct : ∀ value : α, (∀ argument : index, law value argument) → record) (value : α)
    (left right : ∀ argument : index, law value argument) :
    construct value left = construct value right := rfl

/-- A `Prop` field **named by a definition**, the shape `PlacementPin.chosen` has. A definition that
unfolds to a proposition is a proposition, so naming it changes nothing: the field is still one
irrelevant proof, and the definition itself has no runtime image, which is why the exporter skips a
`Prop`-sorted declaration instead of refusing it. -/
theorem named_field_irrelevant {α : Sort u} {stated : α → Prop} {record : Sort v}
    (construct : ∀ value : α, stated value → record) (value : α) (left right : stated value) :
    construct value left = construct value right := rfl

/-! ## A dependent `if` whose hypothesis fills a proof field -/

/--
**A branch that spends its hypothesis on a proof field is constant in that hypothesis.** The taken
branch of `if h : p then ⟨value, fill h⟩ else …` builds the same record at every `h`, so it is a
constant function of the decision's proof — which is what lets the exporter drop the binder and walk
the branch as a plain `if` branch.
-/
theorem proof_field_branch_constant {claim : Prop} {α : Sort u} {invariant : α → Prop}
    {record : Sort v} (construct : ∀ value : α, invariant value → record) (value : α)
    (fill : claim → invariant value) (witness : invariant value) (given : claim) :
    construct value (fill given) = construct value witness := rfl

/--
**The data of a dependent `if` is the plain `if` of the two branches' data.**

The left side is the Lean term: a `dite` whose taken branch builds a record from `value` and a proof
derived from the decision's own hypothesis. The right side is what the generated TypeScript
computes: the same condition, and the data of each branch. Erasure is the map `data`, and this says
it commutes with the branch.
-/
theorem dite_data_erasable {claim : Prop} [Decidable claim] {α : Sort u} {invariant : α → Prop}
    {record : Sort v} (construct : ∀ value : α, invariant value → record) (data : record → α)
    (reads : ∀ (value : α) (held : invariant value), data (construct value held) = value)
    (value : α) (fill : claim → invariant value) (untaken : ¬claim → record) (fallback : α)
    (untakenData : ∀ refuted : ¬claim, data (untaken refuted) = fallback) :
    data (dite claim (fun given => construct value (fill given)) untaken)
      = ite claim value fallback := by
  by_cases decided : claim
  · simp only [decided, dite_true, if_pos]
    exact reads value (fill decided)
  · simp only [decided, dite_false, if_neg, not_false_eq_true]
    exact untakenData decided

/--
A dependent `if` whose branches do not observe their hypotheses at all is the plain `if`. Stated
separately from `dite_data_erasable` because it is the degenerate case the exporter also admits: the
hypothesis is bound and never used, and the emitted condition is unchanged.
-/
theorem dite_erased_branches {claim : Prop} [Decidable claim] {α : Sort u}
    (taken untaken : α) :
    dite claim (fun _ => taken) (fun _ => untaken) = ite claim taken untaken := rfl

/-! ## The same theorems at the shapes the fixture carries

`TSLean/Examples/Roundtrip/Invariant.lean` compiles these three structures end to end. Instantiating
the general statements at them is what makes the fixture evidence rather than illustration: the
hypotheses `record_determined_by_data` and `record_reconstructed` take are discharged by `rfl` and
`cases`, because a Lean structure supplies its constructor and projections definitionally.
-/

/-- The ceiling the example window fits under, mirrored here so this module proves things about the
fixture's own shapes without importing the example tree. -/
private def ceiling : Nat := 8

private def Fits (start width : Nat) : Prop := start + width ≤ ceiling

private structure Window where
  start : Nat
  width : Nat
  fits : Fits start width

/-- The data a `Window` keeps: the pair the emitted record carries. -/
private def Window.data (window : Window) : Nat × Nat := (window.start, window.width)

private def Window.construct : ∀ value : Nat × Nat, Fits value.1 value.2 → Window :=
  fun value fits => ⟨value.1, value.2, fits⟩

private theorem window_built (window : Window) :
    ∃ value, ∃ proof : Fits value.1 value.2, window = Window.construct value proof := by
  obtain ⟨start, width, fits⟩ := window
  exact ⟨(start, width), fits, rfl⟩

private theorem window_reads (value : Nat × Nat) (held : Fits value.1 value.2) :
    Window.data (Window.construct value held) = value := rfl

/-- The window every refused step answers with, so the `dite` below has a total else branch. -/
private def Window.origin : Window := ⟨0, 0, by simp [Fits, ceiling]⟩

/-- **Two windows with the same numbers are the same window.** The instantiation of
`record_determined_by_data` at the fixture's proof-carrying structure. -/
theorem window_determined_by_data (left right : Window) (same : left.data = right.data) :
    left = right :=
  record_determined_by_data Window.construct Window.data window_built left right same window_reads

/-- **A window is rebuilt from its numbers and the invariant.** The instantiation of
`record_reconstructed`: the hypothesis is the invariant, which is precisely what a decoder cannot
supply. -/
theorem window_reconstructed (window : Window) (held : Fits window.data.1 window.data.2) :
    Window.construct window.data held = window :=
  record_reconstructed Window.construct Window.data window_built window_reads window held

/-- **The fixture's `build` is the emitted `if`.** The instantiation of `dite_data_erasable` at the
dependent `if` the example compiles: the data of the Lean term is the condition and the pair, which
is what the generated function returns. The `fill` argument is the identity on the hypothesis,
because `Fits start width` unfolds to exactly the decision the `if` takes. -/
theorem window_build_data (start width : Nat) :
    Window.data (dite (start + width ≤ ceiling)
        (fun fits => Window.construct (start, width) fits)
        (fun _ => Window.origin))
      = ite (start + width ≤ ceiling) (start, width) (0, 0) :=
  dite_data_erasable Window.construct Window.data window_reads (start, width)
    (fun fits : start + width ≤ ceiling => fits) (fun _ => Window.origin) (0, 0)
    (fun _ => rfl)

private structure Gate where
  opened : Bool
  limit : Nat
  openedHasLimit : opened = true → 0 < limit

/-- **A gate is its flag and its number.** The function-typed `Prop` field is irrelevant, so the
constructor answers the same gate at every proof of the implication. -/
theorem gate_implication_irrelevant (opened : Bool) (limit : Nat)
    (left right : opened = true → 0 < limit) :
    Gate.mk opened limit left = Gate.mk opened limit right :=
  implication_field_irrelevant (fun value proof => Gate.mk value.1 value.2 proof)
    (opened, limit) left right

private structure Tally where
  counts : List Nat
  allPositive : ∀ count ∈ counts, 0 < count

/-- **A tally is its list.** The ∀-quantified `Prop` field is irrelevant, so the constructor answers
the same tally at every proof of the law. -/
theorem tally_forall_irrelevant (counts : List Nat)
    (left right : ∀ count ∈ counts, 0 < count) :
    Tally.mk counts left = Tally.mk counts right :=
  forall_field_irrelevant (law := fun counts count => count ∈ counts → 0 < count)
    (fun value proof => Tally.mk value proof) counts left right

end ProofErasure

end TSLean.LeanToTypeScript.Semantics
