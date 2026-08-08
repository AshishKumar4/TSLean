import TSLean.JS.Iterator

namespace TSLean.JS

namespace ArrayCopy

private def heapFault (fault : HeapFault) : ModelFault := .runtime (.heap fault)

private def FreshArrayResult (baseline : Nat) (ref : RefId) (machine : Machine P) : Prop :=
  baseline ≤ ref.value ∧
  (∃ slots, machine.heap.objectKind? ref = some (.array slots)) ∧
  machine.heap.valueValid (.object ref) = true

private theorem heapSizeLower_stable (baseline : Nat) (initial final : Machine P)
    (continued : initial.ContinuesFrom final) (lower : baseline ≤ initial.heap.size) :
    baseline ≤ final.heap.size :=
  Nat.le_trans lower continued.1.1

private def allocateCollected (prototype : Option RefId) (values : List (Option Value)) :
    JSM P RefId := fun machine =>
  match machine.heap.allocateArray values.reverse prototype with
  | .error (.heap fault) => .fault (heapFault fault) machine
  | .error (.invalidValueRef ref) | .error (.invalidAccessor ref) |
      .error (.nonCallableAccessor ref) => .fault (heapFault (.invalidRef ref)) machine
  | .error (.arrayTooLong _) | .error (.invalidArrayLength _) =>
      ObjectAccess.throwRangeError "invalid array length" machine
  | .error (.invalidArrayLengthValue _) | .error (.syntax _) =>
      ObjectAccess.throwTypeError "invalid array allocation" machine
  | .ok (ref, heap) => .done (.normal ref) (machine.setHeap heap)

private theorem allocateCollected_preservesResults (prototype : Option RefId)
    (values : List (Option Value)) :
    JSM.PreservesResults (fun ref machine => machine.heap.valueValid (.object ref) = true)
      (allocateCollected (P := P) prototype values) := by
  constructor
  · intro machine valid
    unfold allocateCollected
    cases allocated : machine.heap.allocateArray values.reverse prototype with
    | error fault => cases fault <;> exact ⟨valid, machine.continuesFrom_refl⟩
    | ok result =>
        rcases result with ⟨ref, heap⟩
        have allocation := Heap.allocateArray_preserves_machineReferences machine.heap heap
          values.reverse prototype ref allocated
        have heapValid := Heap.allocateArray_preserves_wellFormed machine.heap heap values.reverse
          prototype ref (Machine.wellFormed_heap machine valid) allocated
        exact ⟨Machine.setHeap_preserves_wellFormed machine heap valid heapValid allocation.1,
          Machine.setHeap_continuesFrom_machineReferences machine heap valid heapValid allocation.1⟩
  · intro machine valid
    unfold allocateCollected
    cases allocated : machine.heap.allocateArray values.reverse prototype with
    | error fault => cases fault <;> trivial
    | ok result =>
        rcases result with ⟨ref, heap⟩
        exact (Heap.allocateArray_preserves_machineReferences machine.heap heap values.reverse
          prototype ref allocated).2

private theorem allocateCollected_preservesFreshArrayResults (baseline : Nat)
    (prototype : Option RefId) (values : List (Option Value)) :
    JSM.PreservesResultsWhen (fun machine => baseline ≤ machine.heap.size)
      (FreshArrayResult (P := P) baseline) (allocateCollected prototype values) := by
  constructor
  · intro machine valid lower
    exact (allocateCollected_preservesResults (P := P) prototype values).1 machine valid
  · intro machine valid lower
    unfold allocateCollected
    cases allocated : machine.heap.allocateArray values.reverse prototype with
    | error fault => cases fault <;> trivial
    | ok result =>
        rcases result with ⟨ref, heap⟩
        have facts := Heap.allocateArray_result_fresh_kind machine.heap heap values.reverse
          prototype ref allocated
        have valueValid := (Heap.allocateArray_preserves_machineReferences machine.heap heap
          values.reverse prototype ref allocated).2
        exact ⟨Nat.le_trans lower (Nat.le_of_eq facts.1.symm),
          ⟨⟨values.reverse.length, true⟩, facts.2⟩, valueValid⟩

private def collectSlice (hook : BodyHook P) (source : RefId) (stop : Nat) :
    Nat → List (Option Value) → JSM P (List (Option Value))
  | index, values =>
      if stop ≤ index then pure values
      else do
        let heap ← JSM.readHeap
        let key := PropertyKey.string (PropertyKey.arrayIndexString index)
        match Prototype.lookup heap source key with
        | .error (.heap fault) => JSM.fail (heapFault fault)
        | .error .cycleOrFuelExhausted => JSM.fail (heapFault .cycleOrFuelExhausted)
        | .ok none => collectSlice hook source stop (index + 1) (none :: values)
        | .ok (some _) =>
            let value ← ObjectAccess.get hook source key (.object source)
            collectSlice hook source stop (index + 1) (some value :: values)

private theorem collectSlice_preservesResultsAux (hook : BodyHook P) (source : RefId) (stop : Nat)
    (index fuel : Nat) (values : List (Option Value)) (bound : stop - index ≤ fuel)
    (hookPreserves : BodyHookPreservesWellFormed hook) :
    JSM.PreservesResults (fun _ _ => True) (collectSlice hook source stop index values) := by
  induction fuel generalizing index values with
  | zero =>
      unfold collectSlice
      split
      · exact JSM.pure_preservesResults _ values (by intros; trivial)
      · omega
  | succ fuel ih =>
      unfold collectSlice
      split
      · exact JSM.pure_preservesResults _ values (by intros; trivial)
      · apply JSM.bind_preservesResults
        · exact JSM.readHeap_preservesResults
        · intro heap machine valid heapEq
          cases lookup : Prototype.lookup heap source
              (.string (PropertyKey.arrayIndexString index)) with
          | error fault =>
              cases fault with
              | heap fault => exact ⟨JSM.fail_preservesWellFormed _ machine valid, trivial⟩
              | cycleOrFuelExhausted =>
                  exact ⟨JSM.fail_preservesWellFormed _ machine valid, trivial⟩
          | ok descriptor =>
              cases descriptor with
              | none =>
                  have next := ih (index + 1) (none :: values) (by omega)
                  exact ⟨next.1 machine valid, next.2 machine valid⟩
              | some found =>
                  have next : JSM.PreservesResults (fun _ _ => True) (do
                      let value ← ObjectAccess.get hook source
                        (.string (PropertyKey.arrayIndexString index)) (.object source)
                      collectSlice hook source stop (index + 1) (some value :: values)) := by
                    apply JSM.bind_preservesResults
                    · exact ObjectAccess.get_preservesResults hook source
                        (.string (PropertyKey.arrayIndexString index)) (.object source) hookPreserves
                    · intro value afterGet afterGetValid valueValid
                      have rest := ih (index + 1) (some value :: values) (by omega)
                      exact ⟨rest.1 afterGet afterGetValid, rest.2 afterGet afterGetValid⟩
                  exact ⟨next.1 machine valid, next.2 machine valid⟩

private theorem collectSlice_preservesResults (hook : BodyHook P) (source : RefId) (stop index : Nat)
    (values : List (Option Value)) (hookPreserves : BodyHookPreservesWellFormed hook) :
    JSM.PreservesResults (fun _ _ => True) (collectSlice hook source stop index values) :=
  collectSlice_preservesResultsAux hook source stop index (stop - index) values (Nat.le_refl _)
    hookPreserves

/-- Creates a fresh array for `[start, end)`. Absent properties remain holes; inherited numeric
properties and accessors are observed as required by ordinary `Get`. Nested references are shared. -/
def slice (hook : BodyHook P) (source : RefId) (start : Nat := 0)
    (endIndex : Option Nat := none) : JSM P RefId := do
  let heap ← JSM.readHeap
  let length ← match heap.arrayLength source with
    | .ok length => pure length
    | .error fault => JSM.fail (heapFault fault)
  let first := min start length
  let stop := min (endIndex.getD length) length
  let values ← collectSlice hook source stop first []
  allocateCollected none values

/-- Array slice preserves continuity and validates its normal returned array reference. -/
theorem slice_preservesResults (hook : BodyHook P) (source : RefId) (start : Nat := 0)
    (endIndex : Option Nat := none) (hookPreserves : BodyHookPreservesWellFormed hook) :
    JSM.PreservesResults (fun ref machine => machine.heap.valueValid (.object ref) = true)
      (slice hook source start endIndex) := by
  unfold slice
  apply JSM.bind_preservesResults
  · exact JSM.readHeap_preservesResults
  · intro heap machine valid heapEq
    cases lengthResult : heap.arrayLength source with
    | error fault => exact ⟨JSM.fail_preservesWellFormed _ machine valid, trivial⟩
    | ok length =>
        have rest : JSM.PreservesResults
            (fun ref machine => machine.heap.valueValid (.object ref) = true) (do
            let values ← collectSlice hook source (min (endIndex.getD length) length)
              (min start length) []
            allocateCollected none values) := by
          apply JSM.bind_preservesResults
          · exact collectSlice_preservesResults hook source (min (endIndex.getD length) length)
              (min start length) [] hookPreserves
          · intro values afterCollect afterCollectValid _
            have allocated := allocateCollected_preservesResults (P := P) none values
            exact ⟨allocated.1 afterCollect afterCollectValid,
              allocated.2 afterCollect afterCollectValid⟩
        exact ⟨rest.1 machine valid, rest.2 machine valid⟩

private theorem slice_preservesFreshArrayResults (baseline : Nat) (hook : BodyHook P)
    (source : RefId) (start : Nat) (endIndex : Option Nat)
    (hookPreserves : BodyHookPreservesWellFormed hook) :
    JSM.PreservesResultsWhen (fun machine => baseline ≤ machine.heap.size)
      (FreshArrayResult (P := P) baseline) (slice hook source start endIndex) := by
  have readPreserves := JSM.preservesResults_carryPrecondition (JSM.readHeap : JSM P Heap)
    JSM.readHeap_preservesResults (fun machine => baseline ≤ machine.heap.size)
    (heapSizeLower_stable baseline)
  unfold slice
  apply JSM.bind_preservesResultsWhen _ _ readPreserves
  intro heap machine valid readResult
  cases lengthResult : heap.arrayLength source with
  | error fault => exact ⟨JSM.fail_preservesWellFormed _ machine valid, trivial⟩
  | ok length =>
      have collected := JSM.preservesResults_carryPrecondition
        (collectSlice hook source (min (endIndex.getD length) length) (min start length) [])
        (collectSlice_preservesResults hook source (min (endIndex.getD length) length)
          (min start length) [] hookPreserves)
        (fun current => baseline ≤ current.heap.size) (heapSizeLower_stable baseline)
      have rest : JSM.PreservesResultsWhen (fun current => baseline ≤ current.heap.size)
          (FreshArrayResult (P := P) baseline) (do
          let values ← collectSlice hook source (min (endIndex.getD length) length)
            (min start length) []
          allocateCollected none values) := by
        apply JSM.bind_preservesResultsWhen _ _ collected
        intro values afterCollect afterCollectValid collectResult
        have allocated := allocateCollected_preservesFreshArrayResults (P := P) baseline none values
        exact ⟨allocated.1 afterCollect afterCollectValid collectResult.2,
          allocated.2 afterCollect afterCollectValid collectResult.2⟩
      exact ⟨rest.1 machine valid readResult.2, rest.2 machine valid readResult.2⟩

/-- A normal slice result is a fresh array allocated after all indexed `Get` effects. -/
theorem slice_normal_result (hook : BodyHook P) (source : RefId) (start : Nat)
    (endIndex : Option Nat) (hookPreserves : BodyHookPreservesWellFormed hook)
    (initial final : Machine P) (ref : RefId) (valid : initial.WellFormed)
    (run : slice hook source start endIndex initial = .done (.normal ref) final) :
    final.WellFormed ∧ initial.ContinuesFrom final ∧
      initial.heap.size ≤ ref.value ∧
      (∀ old, initial.heap.valueValid (.object old) = true → ref ≠ old) ∧
      (∃ slots, final.heap.objectKind? ref = some (.array slots)) ∧
      final.heap.valueValid (.object ref) = true := by
  have preserved := (slice_preservesFreshArrayResults initial.heap.size hook source start endIndex
    hookPreserves).1 initial valid (Nat.le_refl _)
  have result := (slice_preservesFreshArrayResults initial.heap.size hook source start endIndex
    hookPreserves).2 initial valid (Nat.le_refl _)
  rw [run] at preserved result
  exact ⟨preserved.1, preserved.2, result.1,
    fun old oldValid => Heap.fresh_distinct_of_oldValid initial.heap ref old result.1 oldValid,
    result.2.1, result.2.2⟩

private def collectIterator (hook : BodyHook P) (iterator : RefId) :
    Nat → List (Option Value) → JSM P (List (Option Value))
  | 0, _ => JSM.fail (heapFault .cycleOrFuelExhausted)
  | fuel + 1, values => do
      let result ← Iterator.next hook iterator
      if result.done then pure values
      else collectIterator hook iterator fuel (some result.value :: values)

private theorem collectIterator_preservesResults (hook : BodyHook P) (iterator : RefId)
    (fuel : Nat) (values : List (Option Value))
    (hookPreserves : BodyHookPreservesWellFormed hook) :
    JSM.PreservesResults (fun _ _ => True) (collectIterator hook iterator fuel values) := by
  induction fuel generalizing values with
  | zero => exact JSM.fail_preservesResults _ _
  | succ fuel ih =>
      unfold collectIterator
      apply JSM.bind_preservesResults
      · exact Iterator.next_preservesResults hook iterator hookPreserves
      · intro result machine valid resultValid
        cases done : result.done with
        | true => exact ⟨JSM.pure_preservesWellFormed values machine valid, trivial⟩
        | false =>
            have rest := ih (some result.value :: values)
            exact ⟨rest.1 machine valid, rest.2 machine valid⟩

/-- Consumes this model's live array-values iterator into a fresh array. Iterator `Get` turns holes
into explicit `undefined`, and length is re-read between steps so getter-driven appends are observed.
This is not canonical iterable spread: `GetIterator`, custom iterables, and `IteratorClose` on abrupt
completion remain outside the model. -/
def spread (hook : BodyHook P) (source : RefId) : JSM P RefId := do
  let iterator ← Iterator.arrayValues source
  let values ← collectIterator hook iterator (Heap.maxArrayLength + 1) []
  allocateCollected none values

/-- Modeled array spread preserves continuity and validates its normal returned array reference. -/
theorem spread_preservesResults (hook : BodyHook P) (source : RefId)
    (hookPreserves : BodyHookPreservesWellFormed hook) :
    JSM.PreservesResults (fun ref machine => machine.heap.valueValid (.object ref) = true)
      (spread hook source) := by
  unfold spread
  apply JSM.bind_preservesResults
  · exact Iterator.arrayValues_preservesResults source
  · intro iterator machine valid iteratorValid
    have rest : JSM.PreservesResults
        (fun ref machine => machine.heap.valueValid (.object ref) = true) (do
        let values ← collectIterator hook iterator (Heap.maxArrayLength + 1) []
        allocateCollected none values) := by
      apply JSM.bind_preservesResults
      · exact collectIterator_preservesResults hook iterator (Heap.maxArrayLength + 1) []
          hookPreserves
      · intro values afterCollect afterCollectValid _
        have allocated := allocateCollected_preservesResults (P := P) none values
        exact ⟨allocated.1 afterCollect afterCollectValid,
          allocated.2 afterCollect afterCollectValid⟩
    exact ⟨rest.1 machine valid, rest.2 machine valid⟩

private theorem spread_preservesFreshArrayResults (baseline : Nat) (hook : BodyHook P)
    (source : RefId) (hookPreserves : BodyHookPreservesWellFormed hook) :
    JSM.PreservesResultsWhen (fun machine => baseline ≤ machine.heap.size)
      (FreshArrayResult (P := P) baseline) (spread hook source) := by
  have iteratorPreserves := JSM.preservesResults_carryPrecondition
    (Iterator.arrayValues (P := P) source)
    (Iterator.arrayValues_preservesResults (P := P) source)
    (fun machine : Machine P => baseline ≤ machine.heap.size)
    (heapSizeLower_stable (P := P) baseline)
  unfold spread
  apply JSM.bind_preservesResultsWhen _ _ iteratorPreserves
  intro iterator machine valid iteratorResult
  have collected := JSM.preservesResults_carryPrecondition
    (collectIterator hook iterator (Heap.maxArrayLength + 1) [])
    (collectIterator_preservesResults hook iterator (Heap.maxArrayLength + 1) [] hookPreserves)
    (fun current => baseline ≤ current.heap.size) (heapSizeLower_stable baseline)
  have rest : JSM.PreservesResultsWhen (fun current => baseline ≤ current.heap.size)
      (FreshArrayResult (P := P) baseline) (do
      let values ← collectIterator hook iterator (Heap.maxArrayLength + 1) []
      allocateCollected none values) := by
    apply JSM.bind_preservesResultsWhen _ _ collected
    intro values afterCollect afterCollectValid collectResult
    have allocated := allocateCollected_preservesFreshArrayResults (P := P) baseline none values
    exact ⟨allocated.1 afterCollect afterCollectValid collectResult.2,
      allocated.2 afterCollect afterCollectValid collectResult.2⟩
  exact ⟨rest.1 machine valid iteratorResult.2,
    rest.2 machine valid iteratorResult.2⟩

/-- A normal modeled array spread result is a fresh array allocated after live iteration. -/
theorem spread_normal_result (hook : BodyHook P) (source : RefId)
    (hookPreserves : BodyHookPreservesWellFormed hook)
    (initial final : Machine P) (ref : RefId) (valid : initial.WellFormed)
    (run : spread hook source initial = .done (.normal ref) final) :
    final.WellFormed ∧ initial.ContinuesFrom final ∧
      initial.heap.size ≤ ref.value ∧
      (∀ old, initial.heap.valueValid (.object old) = true → ref ≠ old) ∧
      (∃ slots, final.heap.objectKind? ref = some (.array slots)) ∧
      final.heap.valueValid (.object ref) = true := by
  have preserved := (spread_preservesFreshArrayResults initial.heap.size hook source
    hookPreserves).1 initial valid (Nat.le_refl _)
  have result := (spread_preservesFreshArrayResults initial.heap.size hook source
    hookPreserves).2 initial valid (Nat.le_refl _)
  rw [run] at preserved result
  exact ⟨preserved.1, preserved.2, result.1,
    fun old oldValid => Heap.fresh_distinct_of_oldValid initial.heap ref old result.1 oldValid,
    result.2.1, result.2.2⟩

end ArrayCopy
end TSLean.JS
