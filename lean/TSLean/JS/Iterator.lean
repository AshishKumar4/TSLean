import TSLean.JS.ObjectAccess

namespace TSLean.JS

/-- The observable payload of iterator `next`. Allocating ECMAScript iterator-result objects is a
later object-model boundary; iteration semantics do not depend on that wrapper identity. -/
structure IteratorResult where
  value : Value
  done : Bool
  deriving DecidableEq

namespace Iterator

private def undefined : Value := .primitive .undefined

private def heapFault (fault : HeapFault) : ModelFault := .runtime (.heap fault)

/-- Allocates a fresh array iterator with stable target identity. -/
def arrayValues (target : RefId) : JSM P RefId := fun machine =>
  match machine.heap.allocateArrayIterator target with
  | .error fault => .fault (heapFault fault) machine
  | .ok (iterator, heap) => .done (.normal iterator) (machine.setHeap heap)

/-- Array-iterator allocation preserves complete machine validity. -/
theorem arrayValues_preservesWellFormed (target : RefId) :
    JSM.PreservesWellFormed (arrayValues (P := P) target) := by
  intro machine valid
  unfold arrayValues
  cases allocated : machine.heap.allocateArrayIterator target with
  | error fault => exact ⟨valid, machine.continuesFrom_refl⟩
  | ok result =>
      rcases result with ⟨iterator, heap⟩
      have heapValid := Heap.allocateArrayIterator_preserves_wellFormed machine.heap heap target
        none iterator (Machine.wellFormed_heap machine valid) allocated
      have references := Heap.allocateArrayIterator_preserves_machineReferences machine.heap heap
        target none iterator allocated
      exact ⟨Machine.setHeap_preserves_wellFormed machine heap valid heapValid references,
        Machine.setHeap_continuesFrom_machineReferences machine heap valid heapValid references⟩

/-- Array-iterator allocation preserves continuity and validates its normal returned reference. -/
theorem arrayValues_preservesResults (target : RefId) :
    JSM.PreservesResults (fun iterator machine =>
      machine.heap.valueValid (.object iterator) = true) (arrayValues (P := P) target) := by
  refine ⟨arrayValues_preservesWellFormed target, ?_⟩
  intro machine valid
  unfold arrayValues
  cases allocated : machine.heap.allocateArrayIterator target with
  | error fault => trivial
  | ok result =>
      rcases result with ⟨iterator, heap⟩
      exact Heap.allocateArrayIterator_result_valueValid machine.heap heap target none iterator allocated

/-- A normal array-values result is the fresh iterator allocated at the initial heap frontier. -/
theorem arrayValues_normal_result (target : RefId) (initial final : Machine P) (iterator : RefId)
    (valid : initial.WellFormed)
    (run : arrayValues target initial = .done (.normal iterator) final) :
    final.WellFormed ∧ initial.ContinuesFrom final ∧
      iterator.value = initial.heap.size ∧
      initial.heap.size ≤ iterator.value ∧
      (∀ old, initial.heap.valueValid (.object old) = true → iterator ≠ old) ∧
      final.heap.objectKind? iterator = some (.arrayIterator ⟨target, 0, false⟩) ∧
      final.heap.valueValid (.object iterator) = true := by
  have preserved := (arrayValues_preservesResults (P := P) target).1 initial valid
  have resultValid := (arrayValues_preservesResults (P := P) target).2 initial valid
  rw [run] at preserved resultValid
  unfold arrayValues at run
  cases allocated : initial.heap.allocateArrayIterator target with
  | error fault => simp [allocated] at run
  | ok result =>
      rcases result with ⟨allocatedIterator, heap⟩
      simp [allocated] at run
      obtain ⟨rfl, rfl⟩ := run
      have facts := Heap.allocateArrayIterator_result_fresh_kind initial.heap heap target none
        allocatedIterator allocated
      have lowerBound : initial.heap.size ≤ allocatedIterator.value :=
        Nat.le_of_eq facts.1.symm
      exact ⟨preserved.1, preserved.2, facts.1, lowerBound,
        fun old oldValid => Heap.fresh_distinct_of_oldValid initial.heap allocatedIterator old
          lowerBound oldValid,
        facts.2, resultValid⟩

/-- Advances an array iterator, re-reading target length and performing ordinary `Get` for every
index. Appends before completion are therefore visible, and holes materialize as `undefined`. -/
def next (hook : BodyHook P) (iterator : RefId) : JSM P IteratorResult := fun machine =>
  match machine.heap.advanceArrayIterator iterator with
  | .error fault => .fault (heapFault fault) machine
  | .ok (none, heap) => .done (.normal ⟨undefined, true⟩) (machine.setHeap heap)
  | .ok (some (target, index), heap) =>
      let nextMachine := machine.setHeap heap
      match ObjectAccess.get hook target (.string (PropertyKey.arrayIndexString index))
          (.object target) nextMachine with
      | .done (.normal value) finalMachine => .done (.normal ⟨value, false⟩) finalMachine
      | .done (.thrown value) finalMachine => .done (.thrown value) finalMachine
      | .done (.returned _) finalMachine | .done (.break _) finalMachine |
          .done (.continue _) finalMachine => .fault (.runtime .escapingFunctionControl) finalMachine
      | .exhausted finalMachine => .exhausted finalMachine
      | .fault fault finalMachine => .fault fault finalMachine

/-- Array-iterator stepping preserves complete machine validity under a preserving evaluator hook. -/
theorem next_preservesWellFormed (hook : BodyHook P) (iterator : RefId)
    (hookPreserves : BodyHookPreservesWellFormed hook) :
    JSM.PreservesWellFormed (next hook iterator) := by
  intro machine valid
  unfold next
  cases advanced : machine.heap.advanceArrayIterator iterator with
  | error fault => exact ⟨valid, machine.continuesFrom_refl⟩
  | ok result =>
      rcases result with ⟨value, heap⟩
      have heapValid := Heap.advanceArrayIterator_preserves_wellFormed machine.heap heap iterator
        value (Machine.wellFormed_heap machine valid) advanced
      have referencesPreserved :=
        Heap.advanceArrayIterator_preserves_machineReferences machine.heap heap iterator value advanced
      have nextMachineValid : (machine.setHeap heap).WellFormed :=
        Machine.setHeap_preserves_wellFormed machine heap valid heapValid referencesPreserved
      have nextMachineContinues : machine.ContinuesFrom (machine.setHeap heap) :=
        Machine.setHeap_continuesFrom_machineReferences machine heap valid heapValid referencesPreserved
      cases value with
      | none => exact ⟨nextMachineValid, nextMachineContinues⟩
      | some yielded =>
          rcases yielded with ⟨target, index⟩
          let action := ObjectAccess.get hook target
            (.string (PropertyKey.arrayIndexString index)) (.object target)
          have actionValid := ObjectAccess.get_preservesWellFormed hook target
            (.string (PropertyKey.arrayIndexString index)) (.object target) hookPreserves
            (machine.setHeap heap) nextMachineValid
          cases actionRun : action (machine.setHeap heap) with
          | done completion finalMachine =>
              change RunResult.MachinePreserved (machine.setHeap heap)
                (action (machine.setHeap heap)) at actionValid
              rw [actionRun] at actionValid
              have finalPreserved : finalMachine.WellFormed ∧ machine.ContinuesFrom finalMachine :=
                ⟨actionValid.1, Machine.continuesFrom_trans _ _ _ nextMachineContinues actionValid.2⟩
              cases completion <;> simpa [advanced, action, actionRun] using finalPreserved
          | exhausted finalMachine | fault fault finalMachine =>
              change RunResult.MachinePreserved (machine.setHeap heap)
                (action (machine.setHeap heap)) at actionValid
              rw [actionRun] at actionValid
              simp only [action, actionRun]
              exact ⟨actionValid.1,
                Machine.continuesFrom_trans _ _ _ nextMachineContinues actionValid.2⟩

/-- Array-iterator stepping validates yielded and abrupt values; a done result contains valid
`undefined`. -/
theorem next_preservesResults (hook : BodyHook P) (iterator : RefId)
    (hookPreserves : BodyHookPreservesWellFormed hook) :
    JSM.PreservesResults (fun result machine =>
      machine.heap.valueValid result.value = true ∧
        (result.done = true → result.value = undefined)) (next hook iterator) := by
  refine ⟨next_preservesWellFormed hook iterator hookPreserves, ?_⟩
  intro machine valid
  unfold next
  cases advanced : machine.heap.advanceArrayIterator iterator with
  | error fault => trivial
  | ok result =>
      rcases result with ⟨value, heap⟩
      cases value with
      | none => exact ⟨rfl, fun _ => rfl⟩
      | some yielded =>
          rcases yielded with ⟨target, index⟩
          let action := ObjectAccess.get hook target
            (.string (PropertyKey.arrayIndexString index)) (.object target)
          have valuesValid := ObjectAccess.get_preservesResults hook target
            (.string (PropertyKey.arrayIndexString index)) (.object target) hookPreserves |>.2
            (machine.setHeap heap)
            (Machine.setHeap_preserves_wellFormed machine heap valid
              (Heap.advanceArrayIterator_preserves_wellFormed machine.heap heap iterator
                (some (target, index)) (Machine.wellFormed_heap machine valid) advanced)
              (Heap.advanceArrayIterator_preserves_machineReferences machine.heap heap iterator
                (some (target, index)) advanced))
          cases actionRun : action (machine.setHeap heap) with
          | done completion finalMachine =>
              change RunResult.CompletionValuesValid
                (fun value machine => machine.heap.valueValid value = true)
                (action (machine.setHeap heap)) at valuesValid
              rw [actionRun] at valuesValid
              simp only [advanced, action, actionRun]
              cases completion with
              | normal value => exact ⟨valuesValid, by simp⟩
              | thrown value => exact valuesValid
              | returned value | «break» label | «continue» label => trivial
          | exhausted finalMachine | fault fault finalMachine =>
              simp [advanced, action, actionRun, RunResult.CompletionValuesValid]

end Iterator
end TSLean.JS
