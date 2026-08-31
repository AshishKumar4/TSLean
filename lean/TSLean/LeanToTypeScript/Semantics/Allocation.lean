import TSLean.LeanToTypeScript.Semantics.Relation

/-!
# Object construction in the target heap

One lemma: an emitted object literal builds exactly the own-property shape the refinement relation
names. It also proves that ordinary object allocation preserves every existing function object's
internal closure payload, because the allocation updates only the JavaScript heap.

The proof is an induction over the properties still to define, carrying the invariant that the object
under construction is a fresh, extensible, ordinary object whose own shape is exactly the properties
defined so far. `TSLean/JS/Heap.lean` exports the two bridges it needs:
`allocate_ordinary_observations` for the fresh object and `createDataProperty_ordinary_append` for
one definition step.
-/

namespace TSLean.LeanToTypeScript.Semantics

open TSLean.JS

namespace Allocation

/-- The invariant carried while an object literal is under construction. -/
structure Building (start : Heap) (ref : RefId) (done : List (String × Value)) (heap : Heap) :
    Prop where
  valid : heap.WellFormed
  extension : TSLean.Refinement.Heap.ExactExtension start heap
  shape : Relation.HasOwnFields heap ref done
  ordinary : ∃ object, heap.get? ref = .ok object ∧ object.kind = .ordinary ∧
    object.extensible = true
  fresh : start.size ≤ ref.value

/-- Every own key of an object under construction is a string key. -/
private theorem keys_are_strings (done : List (String × Value)) (symbol : SymbolId) :
    PropertyKey.symbol symbol ∉ done.map fun entry => Ir.propertyKey entry.1 := by
  intro member
  obtain ⟨entry, _, keyEq⟩ := List.mem_map.mp member
  exact absurd keyEq (by simp [Ir.propertyKey])

/-- A name absent from the properties defined so far has an absent own key. -/
private theorem key_fresh {done : List (String × Value)} {name : String}
    (absent : name ∉ done.map Prod.fst) :
    Ir.propertyKey name ∉ done.map fun entry => Ir.propertyKey entry.1 := by
  intro member
  obtain ⟨entry, entryMember, keyEq⟩ := List.mem_map.mp member
  exact absent (List.mem_map.mpr ⟨entry, entryMember, Ir.propertyKey_injective keyEq⟩)

/-- Defining one fresh property extends the object's own shape by exactly that property. -/
private theorem step {start : Heap} {ref : RefId} {done : List (String × Value)} {heap : Heap}
    {name : String} {value : Value}
    (building : Building start ref done heap)
    (validKey : Ir.ValidKey name) (absent : name ∉ done.map Prod.fst)
    (valueValid : heap.valueValid value = true) :
    ∃ next, heap.createDataProperty ref (Ir.propertyKey name) value = .ok (true, next) ∧
      (∀ observed, next.valueValid observed = heap.valueValid observed) ∧
      Building start ref (done ++ [(name, value)]) next := by
  obtain ⟨object, found, ordinary, extensible⟩ := building.ordinary
  obtain ⟨next, defined, sizeEq, othersEq, validEq, freshObject, keysEq, readEq, otherReads⟩ :=
    Heap.createDataProperty_ordinary_append heap ref object (JSString.ofLeanString name) value
      (done.map fun entry => Ir.propertyKey entry.1) building.valid found ordinary extensible
      validKey building.shape.keys (key_fresh absent) (keys_are_strings done) valueValid
  refine ⟨next, defined, validEq, ?_⟩
  obtain ⟨nextObject, nextFound, nextOrdinary, _, nextExtensible⟩ := freshObject
  have nextValid : next.WellFormed :=
    Heap.createDataProperty_preserves_wellFormed heap next ref (Ir.propertyKey name) value
      true building.valid defined
  refine ⟨nextValid, ?_, ⟨?_, ?_⟩, ⟨nextObject, nextFound, nextOrdinary, nextExtensible⟩,
    building.fresh⟩
  · refine ⟨building.extension.oldWellFormed, nextValid, ?_, ?_⟩
    · exact Nat.le_trans building.extension.size_le (Nat.le_of_eq sizeEq.symm)
    · intro oldRef oldObject oldFound
      have carried := building.extension.get_eq oldRef oldObject oldFound
      have different : oldRef ≠ ref := by
        intro same
        subst same
        exact absurd (Heap.get?_ok_valid start oldRef oldObject oldFound)
          (Nat.not_lt_of_ge building.fresh)
      rw [othersEq oldRef different]
      exact carried
  · rw [keysEq, List.map_append]
    rfl
  · intro query
    by_cases same : query = name
    · subst same
      rw [show Ir.propertyKey query = PropertyKey.string (JSString.ofLeanString query) from rfl,
        readEq]
      have absentQuery : (done.find? fun entry => entry.1 == query) = none := by
        apply List.find?_eq_none.mpr
        intro entry member matched
        exact absent (List.mem_map.mpr ⟨entry, member, by simpa using of_decide_eq_true matched⟩)
      simp [List.find?_append, absentQuery]
    · rw [otherReads (Ir.propertyKey query) (fun keyEq => same (Ir.propertyKey_injective keyEq)),
        building.shape.read query]
      simp [List.find?_append, Ne.symm same]

/-- Defining the remaining properties of a fresh object completes the record shape and preserves the
callable-payload list exactly. -/
private theorem defineAll {start : Heap} {ref : RefId} :
    ∀ (remaining done : List (String × Value)) (state : Target.State),
      Building start ref done state.heap →
      (∀ entry ∈ remaining, Ir.ValidKey entry.1) →
      ((done ++ remaining).map Prod.fst).Nodup →
      (∀ entry ∈ remaining, state.heap.valueValid entry.2 = true) →
      ∃ final, Target.defineProperties ref state remaining = .ok (.object ref) final ∧
        final.trace = state.trace ∧ final.closures = state.closures ∧
          Building start ref (done ++ remaining) final.heap
  | [], done, state, building, _, _, _ => by
      refine ⟨state, rfl, rfl, rfl, ?_⟩
      simpa using building
  | (name, value) :: rest, done, state, building, validKeys, distinct, valuesValid => by
      have absent : name ∉ done.map Prod.fst := by
        rw [List.map_append, List.map_cons] at distinct
        have parts := List.nodup_append.mp distinct
        intro member
        exact parts.2.2 name member name (List.Mem.head _) rfl
      obtain ⟨next, defined, validEq, nextBuilding⟩ :=
        step building (validKeys (name, value) (by simp)) absent
          (valuesValid (name, value) (by simp))
      have carried : ∀ entry ∈ rest, next.valueValid entry.2 = true := by
        intro entry member
        exact (validEq entry.2).trans (valuesValid entry (by simp [member]))
      obtain ⟨final, ran, traceEq, closuresEq, finalBuilding⟩ :=
        defineAll rest (done ++ [(name, value)]) (state.withHeap next) nextBuilding
          (fun entry member => validKeys entry (by simp [member]))
          (by simpa using distinct) carried
      refine ⟨final, ?_, traceEq, ?_, by simpa using finalBuilding⟩
      · unfold Target.defineProperties
        rw [defined]
        exact ran
      · simpa [Target.State.withHeap] using closuresEq

/--
The emitted object literal allocates a fresh object whose own properties are exactly the listed
fields, in the listed order, and touches nothing that already existed. It preserves every existing
callable payload because object-literal allocation only updates the heap.
-/
theorem allocateLiteral_shape (state : Target.State) (entries : List (String × Value))
    (valid : state.heap.WellFormed) (closuresValid : state.ClosuresWellFormed)
    (validKeys : ∀ entry ∈ entries, Ir.ValidKey entry.1)
    (distinct : (entries.map Prod.fst).Nodup)
    (valuesValid : ∀ entry ∈ entries, state.heap.valueValid entry.2 = true) :
    ∃ ref final, Target.allocateLiteral state entries = .ok (.object ref) final ∧
      final.trace = state.trace ∧ final.closures = state.closures ∧
        Target.State.Extension state final ∧ final.ClosuresWellFormed ∧
          state.heap.size ≤ ref.value ∧ Relation.HasOwnFields final.heap ref entries := by
  obtain ⟨ref, heap, allocated⟩ := Heap.allocate_null_prototype_ok state.heap true
  obtain ⟨⟨object, found, ordinary, _, extensible⟩, emptyKeys, emptyReads⟩ :=
    Heap.allocate_ordinary_observations state.heap heap true ref allocated
  have extension := TSLean.Refinement.Heap.allocate_exactExtension state.heap heap none true ref
    valid allocated
  have freshIndex := (Heap.allocate_result_fresh_kind state.heap heap none true ref allocated).1
  have building : Building state.heap ref [] heap := by
    refine ⟨extension.nextWellFormed, extension, ⟨?_, ?_⟩,
      ⟨object, found, ordinary, extensible⟩, Nat.le_of_eq freshIndex.symm⟩
    · simpa using emptyKeys
    · intro name
      simpa using emptyReads (Ir.propertyKey name)
  obtain ⟨final, ran, traceEq, closuresEq, finalBuilding⟩ :=
    defineAll entries [] (state.withHeap heap) building validKeys (by simpa using distinct)
      (fun entry member => extension.preserves_valueValid entry.2 (valuesValid entry member))
  have lookupEq : ∀ lookupRef, final.lookupClosure lookupRef = state.lookupClosure lookupRef := by
    intro lookupRef
    simp [Target.State.lookupClosure, closuresEq, Target.State.withHeap]
  have stateExtension : Target.State.Extension state final := by
    refine ⟨finalBuilding.extension, ?_⟩
    intro oldRef closure oldFound
    rw [lookupEq oldRef]
    exact oldFound
  have finalClosuresValid : final.ClosuresWellFormed := by
    intro oldRef closure finalFound
    rw [lookupEq oldRef] at finalFound
    obtain ⟨oldRefValid, capturedValid⟩ := closuresValid oldRef closure finalFound
    refine ⟨finalBuilding.extension.preserves_valueValid (.object oldRef) oldRefValid, ?_⟩
    intro value member
    exact finalBuilding.extension.preserves_valueValid value (capturedValid value member)
  refine ⟨ref, final, ?_, traceEq, closuresEq, stateExtension, finalClosuresValid,
    finalBuilding.fresh, ?_⟩
  · unfold Target.allocateLiteral
    rw [allocated]
    exact ran
  · simpa using finalBuilding.shape

end Allocation

end TSLean.LeanToTypeScript.Semantics
