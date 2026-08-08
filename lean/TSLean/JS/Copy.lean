import TSLean.JS.AbstractOperations

namespace TSLean.JS

namespace Copy

private def heapFault (fault : HeapFault) : ModelFault := .runtime (.heap fault)

private def excluded (exclusions : List PropertyKey) (key : PropertyKey) : Bool :=
  exclusions.any (PropertyKey.equal key)

private def enumerable : PropertyDescriptor → Bool
  | .data descriptor => descriptor.enumerable
  | .accessor descriptor => descriptor.enumerable

private def createData (target : RefId) (key : PropertyKey) (value : Value) : JSM P Unit :=
  do
    if ← ObjectAccess.createDataProperty target key value then pure ()
    else ObjectAccess.throwTypeError "CreateDataProperty rejected"

private theorem createData_preservesResults (target : RefId) (key : PropertyKey) (value : Value) :
    JSM.PreservesResults (fun _ _ => True) (createData (P := P) target key value) := by
  unfold createData
  apply JSM.bind_preservesResults
  · exact ObjectAccess.createDataProperty_preservesResults target key value
  · intro success machine valid _
    cases success with
    | false =>
        exact ⟨JSM.throwJS_preservesWellFormed _ machine valid, rfl⟩
    | true => exact ⟨JSM.pure_preservesWellFormed () machine valid, trivial⟩

private def copyKeys (hook : BodyHook P) (target source : RefId)
    (exclusions : List PropertyKey) : List PropertyKey → JSM P Unit
  | [] => pure ()
  | key :: rest => do
      if excluded exclusions key then copyKeys hook target source exclusions rest
      else
        let heap ← JSM.readHeap
        match OrdinaryObject.getOwnProperty heap source key with
        | .error fault => JSM.fail (heapFault fault)
        | .ok none => copyKeys hook target source exclusions rest
        | .ok (some descriptor) =>
            if !enumerable descriptor then copyKeys hook target source exclusions rest
            else
              let value ← ObjectAccess.get hook source key (.object source)
              createData target key value
              copyKeys hook target source exclusions rest

private theorem copyKeys_preservesResults (hook : BodyHook P) (target source : RefId)
    (exclusions : List PropertyKey) (keys : List PropertyKey)
    (hookPreserves : BodyHookPreservesWellFormed hook) :
    JSM.PreservesResults (fun _ _ => True) (copyKeys hook target source exclusions keys) := by
  induction keys with
  | nil => exact JSM.pure_preservesResults _ () (by intros; trivial)
  | cons key rest ih =>
      unfold copyKeys
      split
      · exact ih
      · apply JSM.bind_preservesResults
        · exact JSM.readHeap_preservesResults
        · intro heap machine valid heapEq
          cases own : OrdinaryObject.getOwnProperty heap source key with
          | error fault =>
              exact ⟨JSM.fail_preservesWellFormed _ machine valid, trivial⟩
          | ok descriptor =>
              cases descriptor with
              | none => exact ⟨ih.1 machine valid, ih.2 machine valid⟩
              | some descriptor =>
                  simp only
                  split
                  · exact ⟨ih.1 machine valid, ih.2 machine valid⟩
                  · have copied : JSM.PreservesResults (fun _ _ => True) (do
                        let value ← ObjectAccess.get hook source key (.object source)
                        createData target key value
                        copyKeys hook target source exclusions rest) := by
                      apply JSM.bind_preservesResults
                      · exact ObjectAccess.get_preservesResults hook source key (.object source)
                          hookPreserves
                      · intro value afterGet afterGetValid valueValid
                        have tail : JSM.PreservesResults (fun _ _ => True) (do
                            createData target key value
                            copyKeys hook target source exclusions rest) := by
                          apply JSM.bind_preservesResults
                          · exact createData_preservesResults target key value
                          · intro _ afterCreate afterCreateValid _
                            exact ⟨ih.1 afterCreate afterCreateValid,
                              ih.2 afterCreate afterCreateValid⟩
                        exact ⟨tail.1 afterGet afterGetValid, tail.2 afterGet afterGetValid⟩
                    exact ⟨copied.1 machine valid, copied.2 machine valid⟩

/-- Copies enumerable own properties from a snapshotted key list. Each descriptor and value is read
at its turn; accessors run, symbols participate, and nested object references remain unchanged. -/
def copyDataProperties (hook : BodyHook P) (target source : RefId)
    (exclusions : List PropertyKey := []) : JSM P Unit := do
  let heap ← JSM.readHeap
  match heap.get? target with
  | .error fault => JSM.fail (heapFault fault)
  | .ok _ => pure ()
  match heap.get? source with
  | .error fault => JSM.fail (heapFault fault)
  | .ok _ => pure ()
  match OrdinaryObject.ownPropertyKeys heap source with
  | .error fault => JSM.fail (heapFault fault)
  | .ok keys => copyKeys hook target source exclusions keys

/-- CopyDataProperties preserves machine continuity and validates accessor or definition throws. -/
theorem copyDataProperties_preservesResults (hook : BodyHook P) (target source : RefId)
    (exclusions : List PropertyKey := []) (hookPreserves : BodyHookPreservesWellFormed hook) :
    JSM.PreservesResults (fun _ _ => True)
      (copyDataProperties hook target source exclusions) := by
  unfold copyDataProperties
  apply JSM.bind_preservesResults
  · exact JSM.readHeap_preservesResults
  · intro heap machine valid heapEq
    cases targetFound : heap.get? target with
    | error fault => exact ⟨JSM.fail_preservesWellFormed _ machine valid, trivial⟩
    | ok targetObject =>
        cases sourceFound : heap.get? source with
        | error fault => exact ⟨JSM.fail_preservesWellFormed _ machine valid, trivial⟩
        | ok sourceObject =>
            cases keys : OrdinaryObject.ownPropertyKeys heap source with
            | error fault => exact ⟨JSM.fail_preservesWellFormed _ machine valid, trivial⟩
            | ok keyList =>
                have copied := copyKeys_preservesResults hook target source exclusions keyList
                  hookPreserves
                exact ⟨copied.1 machine valid, copied.2 machine valid⟩

private def assignKeys (hook : BodyHook P) (target source : RefId) :
    List PropertyKey → JSM P Unit
  | [] => pure ()
  | key :: rest => do
      let heap ← JSM.readHeap
      match OrdinaryObject.getOwnProperty heap source key with
      | .error fault => JSM.fail (heapFault fault)
      | .ok none => assignKeys hook target source rest
      | .ok (some descriptor) =>
          if !enumerable descriptor then assignKeys hook target source rest
          else
            let value ← ObjectAccess.get hook source key (.object source)
            ObjectAccess.setStrict hook target key value (.object target)
            assignKeys hook target source rest

private theorem assignKeys_preservesResults (hook : BodyHook P) (target source : RefId)
    (keys : List PropertyKey) (hookPreserves : BodyHookPreservesWellFormed hook) :
    JSM.PreservesResults (fun _ _ => True) (assignKeys hook target source keys) := by
  induction keys with
  | nil => exact JSM.pure_preservesResults _ () (by intros; trivial)
  | cons key rest ih =>
      unfold assignKeys
      apply JSM.bind_preservesResults
      · exact JSM.readHeap_preservesResults
      · intro heap machine valid heapEq
        cases own : OrdinaryObject.getOwnProperty heap source key with
        | error fault => exact ⟨JSM.fail_preservesWellFormed _ machine valid, trivial⟩
        | ok descriptor =>
            cases descriptor with
            | none => exact ⟨ih.1 machine valid, ih.2 machine valid⟩
            | some descriptor =>
                simp only
                split
                · exact ⟨ih.1 machine valid, ih.2 machine valid⟩
                · have assigned : JSM.PreservesResults (fun _ _ => True) (do
                      let value ← ObjectAccess.get hook source key (.object source)
                      ObjectAccess.setStrict hook target key value (.object target)
                      assignKeys hook target source rest) := by
                    apply JSM.bind_preservesResults
                    · exact ObjectAccess.get_preservesResults hook source key (.object source)
                        hookPreserves
                    · intro value afterGet afterGetValid valueValid
                      have tail : JSM.PreservesResults (fun _ _ => True) (do
                          ObjectAccess.setStrict hook target key value (.object target)
                          assignKeys hook target source rest) := by
                        apply JSM.bind_preservesResults
                        · exact ObjectAccess.setStrict_preservesResults hook target key value
                            (.object target) hookPreserves
                        · intro _ afterSet afterSetValid _
                          exact ⟨ih.1 afterSet afterSetValid, ih.2 afterSet afterSetValid⟩
                      exact ⟨tail.1 afterGet afterGetValid, tail.2 afterGet afterGetValid⟩
                  exact ⟨assigned.1 machine valid, assigned.2 machine valid⟩

private def assignSource (hook : BodyHook P) (target : RefId) : Value → JSM P Unit
  | .primitive .null | .primitive .undefined => pure ()
  | sourceValue => do
      let source ← AbstractOperations.toObject sourceValue
      let heap ← JSM.readHeap
      match OrdinaryObject.ownPropertyKeys heap source with
      | .error fault => JSM.fail (heapFault fault)
      | .ok keys => assignKeys hook target source keys

private theorem assignSource_preservesResults (hook : BodyHook P) (target : RefId)
    (source : Value) (hookPreserves : BodyHookPreservesWellFormed hook) :
    JSM.PreservesResults (fun _ _ => True) (assignSource hook target source) := by
  cases source with
  | primitive primitive =>
      cases primitive with
      | null | undefined => exact JSM.pure_preservesResults _ () (by intros; trivial)
      | boolean value | number value | string value | bigint value | symbol value =>
          unfold assignSource
          apply JSM.bind_preservesResults
          · exact AbstractOperations.toObject_preservesResults _
          · intro sourceRef machine valid sourceValid
            have rest : JSM.PreservesResults (fun _ _ => True) (do
                let heap ← JSM.readHeap
                match OrdinaryObject.ownPropertyKeys heap sourceRef with
                | .error fault => JSM.fail (heapFault fault)
                | .ok keys => assignKeys hook target sourceRef keys) := by
              apply JSM.bind_preservesResults
              · exact JSM.readHeap_preservesResults
              · intro heap afterRead afterReadValid heapEq
                cases keys : OrdinaryObject.ownPropertyKeys heap sourceRef with
                | error fault =>
                    exact ⟨JSM.fail_preservesWellFormed _ afterRead afterReadValid, trivial⟩
                | ok keyList =>
                    have assigned := assignKeys_preservesResults hook target sourceRef keyList
                      hookPreserves
                    exact ⟨assigned.1 afterRead afterReadValid, assigned.2 afterRead afterReadValid⟩
            exact ⟨rest.1 machine valid, rest.2 machine valid⟩
  | object sourceRef =>
      unfold assignSource
      apply JSM.bind_preservesResults
      · exact AbstractOperations.toObject_preservesResults _
      · intro boxed machine valid boxedValid
        have rest : JSM.PreservesResults (fun _ _ => True) (do
            let heap ← JSM.readHeap
            match OrdinaryObject.ownPropertyKeys heap boxed with
            | .error fault => JSM.fail (heapFault fault)
            | .ok keys => assignKeys hook target boxed keys) := by
          apply JSM.bind_preservesResults
          · exact JSM.readHeap_preservesResults
          · intro heap afterRead afterReadValid heapEq
            cases keys : OrdinaryObject.ownPropertyKeys heap boxed with
            | error fault =>
                exact ⟨JSM.fail_preservesWellFormed _ afterRead afterReadValid, trivial⟩
            | ok keyList =>
                have assigned := assignKeys_preservesResults hook target boxed keyList hookPreserves
                exact ⟨assigned.1 afterRead afterReadValid, assigned.2 afterRead afterReadValid⟩
        exact ⟨rest.1 machine valid, rest.2 machine valid⟩

private def assignSources (hook : BodyHook P) (target : RefId) : List Value → JSM P Unit
  | [] => pure ()
  | source :: rest => do
      assignSource hook target source
      assignSources hook target rest

private theorem assignSources_preservesResults (hook : BodyHook P) (target : RefId)
    (sources : List Value) (hookPreserves : BodyHookPreservesWellFormed hook) :
    JSM.PreservesResults (fun _ _ => True) (assignSources hook target sources) := by
  induction sources with
  | nil => exact JSM.pure_preservesResults _ () (by intros; trivial)
  | cons source rest ih =>
      unfold assignSources
      apply JSM.bind_preservesResults
      · exact assignSource_preservesResults hook target source hookPreserves
      · intro _ machine valid _
        exact ⟨ih.1 machine valid, ih.2 machine valid⟩

/-- Mutates an object target or a fresh wrapper for a primitive target and returns that same object.
Nullish targets throw TypeError; nullish sources are skipped and all other primitives are boxed. -/
def objectAssign (hook : BodyHook P) (target : Value) (sources : List Value) : JSM P Value := do
  match target with
  | .primitive .null | .primitive .undefined =>
      ObjectAccess.throwTypeError "cannot convert nullish target to object"
  | _ => pure ()
  let targetRef ← AbstractOperations.toObject target
  assignSources hook targetRef sources
  pure (.object targetRef)

/-- Object.assign preserves continuity; normal results are valid and retain object-target identity. -/
theorem objectAssign_preservesResults (hook : BodyHook P) (target : Value) (sources : List Value)
    (hookPreserves : BodyHookPreservesWellFormed hook) :
    JSM.PreservesResults (fun result machine =>
      machine.heap.valueValid result = true ∧
        ∀ ref, target = .object ref → result = .object ref)
      (objectAssign hook target sources) := by
  unfold objectAssign
  have rest : JSM.PreservesResults (fun result machine =>
      machine.heap.valueValid result = true ∧
        ∀ ref, target = .object ref → result = .object ref) (do
      let targetRef ← AbstractOperations.toObject target
      assignSources hook targetRef sources
      pure (.object targetRef)) := by
    apply JSM.bind_preservesResults
    · exact AbstractOperations.toObject_preservesResults target
    · intro targetRef afterTarget afterTargetValid targetValid
      have sourcesValid := JSM.preservesResults_carryPrecondition
        (assignSources hook targetRef sources)
        (assignSources_preservesResults hook targetRef sources hookPreserves)
        (fun current => current.heap.valueValid (.object targetRef) = true)
        (fun initial final continued validRef =>
          continued.1.preserves_valueValid (.object targetRef) validRef)
      have tail : JSM.PreservesResultsWhen
          (fun current => current.heap.valueValid (.object targetRef) = true)
          (fun result machine => machine.heap.valueValid result = true ∧
            ∀ ref, target = .object ref → result = .object ref) (do
          assignSources hook targetRef sources
          pure (.object targetRef)) := by
        apply JSM.bind_preservesResultsWhen _ _ sourcesValid
        intro _ final finalValid result
        exact ⟨JSM.pure_preservesWellFormed (Value.object targetRef) final finalValid,
          ⟨result.2, by
            intro original targetEq
            rw [targetValid.2 original targetEq]⟩⟩
      exact ⟨tail.1 afterTarget afterTargetValid targetValid.1,
        tail.2 afterTarget afterTargetValid targetValid.1⟩
  cases target with
  | object ref =>
      apply JSM.bind_preservesResults
      · exact JSM.pure_preservesResults (fun _ _ => True) () (by intros; trivial)
      · intro _ machine valid _
        exact ⟨rest.1 machine valid, rest.2 machine valid⟩
  | primitive primitive =>
      cases primitive with
      | null | undefined =>
          exact ⟨JSM.throwJS_preservesWellFormed _, by intros; rfl⟩
      | boolean value | number value | string value | bigint value | symbol value =>
          apply JSM.bind_preservesResults
          · exact JSM.pure_preservesResults (fun _ _ => True) () (by intros; trivial)
          · intro _ machine valid _
            exact ⟨rest.1 machine valid, rest.2 machine valid⟩

private def spreadSources (hook : BodyHook P) (target : RefId)
    (exclusions : List PropertyKey) : List Value → JSM P Unit
  | [] => pure ()
  | .primitive .null :: rest | .primitive .undefined :: rest =>
      spreadSources hook target exclusions rest
  | sourceValue :: rest => do
      let source ← AbstractOperations.toObject sourceValue
      copyDataProperties hook target source exclusions
      spreadSources hook target exclusions rest

private theorem spreadSources_preservesResults (hook : BodyHook P) (target : RefId)
    (exclusions : List PropertyKey) (sources : List Value)
    (hookPreserves : BodyHookPreservesWellFormed hook) :
    JSM.PreservesResults (fun _ _ => True) (spreadSources hook target exclusions sources) := by
  induction sources with
  | nil => exact JSM.pure_preservesResults _ () (by intros; trivial)
  | cons source rest ih =>
      cases source with
      | primitive primitive =>
          cases primitive with
          | null | undefined => exact ih
          | boolean value | number value | string value | bigint value | symbol value =>
              unfold spreadSources
              apply JSM.bind_preservesResults
              · exact AbstractOperations.toObject_preservesResults _
              · intro sourceRef machine valid sourceValid
                have tail : JSM.PreservesResults (fun _ _ => True) (do
                    copyDataProperties hook target sourceRef exclusions
                    spreadSources hook target exclusions rest) := by
                  apply JSM.bind_preservesResults
                  · exact copyDataProperties_preservesResults hook target sourceRef exclusions
                      hookPreserves
                  · intro _ afterCopy afterCopyValid _
                    exact ⟨ih.1 afterCopy afterCopyValid, ih.2 afterCopy afterCopyValid⟩
                exact ⟨tail.1 machine valid, tail.2 machine valid⟩
      | object sourceRef =>
          unfold spreadSources
          apply JSM.bind_preservesResults
          · exact AbstractOperations.toObject_preservesResults _
          · intro boxed machine valid boxedValid
            have tail : JSM.PreservesResults (fun _ _ => True) (do
                copyDataProperties hook target boxed exclusions
                spreadSources hook target exclusions rest) := by
              apply JSM.bind_preservesResults
              · exact copyDataProperties_preservesResults hook target boxed exclusions hookPreserves
              · intro _ afterCopy afterCopyValid _
                exact ⟨ih.1 afterCopy afterCopyValid, ih.2 afterCopy afterCopyValid⟩
            exact ⟨tail.1 machine valid, tail.2 machine valid⟩

/-- Allocates a fresh ordinary object and copies sources left-to-right with CreateDataProperty, so
target prototype setters cannot intercept writes and source prototypes are not copied. -/
def objectSpread (hook : BodyHook P) (sources : List Value)
    (exclusions : List PropertyKey := []) : JSM P RefId := fun machine =>
  match machine.heap.allocate none true with
  | .error fault => .fault (heapFault fault) machine
  | .ok (target, heap) =>
      match spreadSources hook target exclusions sources (machine.setHeap heap) with
      | .done (.normal ()) next => .done (.normal target) next
      | .done (.thrown value) next => .done (.thrown value) next
      | .done (.returned _) next | .done (.break _) next | .done (.continue _) next =>
          .fault (.runtime .escapingFunctionControl) next
      | .exhausted next => .exhausted next
      | .fault fault next => .fault fault next

/-- Object spread preserves continuity and validates its normal returned object reference. -/
theorem objectSpread_preservesResults (hook : BodyHook P) (sources : List Value)
    (exclusions : List PropertyKey := []) (hookPreserves : BodyHookPreservesWellFormed hook) :
    JSM.PreservesResults (fun ref machine => machine.heap.valueValid (.object ref) = true)
      (objectSpread hook sources exclusions) := by
  constructor
  · intro machine valid
    unfold objectSpread
    cases allocated : machine.heap.allocate none true with
    | error fault => exact ⟨valid, machine.continuesFrom_refl⟩
    | ok result =>
        rcases result with ⟨target, heap⟩
        have allocation := Heap.allocate_preserves_machineReferences machine.heap heap none true
          target allocated
        have heapValid := Heap.allocate_preserves_wellFormed machine.heap heap none true target
          (Machine.wellFormed_heap machine valid) allocated
        have allocatedValid := Machine.setHeap_preserves_wellFormed machine heap valid heapValid
          allocation.1
        have allocatedContinues := Machine.setHeap_continuesFrom_machineReferences machine heap valid
          heapValid allocation.1
        have spreadValid := spreadSources_preservesResults hook target exclusions sources hookPreserves
        have spreadMachine := spreadValid.1 (machine.setHeap heap) allocatedValid
        cases spreadRun : spreadSources hook target exclusions sources (machine.setHeap heap) with
        | done completion final =>
            rw [spreadRun] at spreadMachine
            have finalPreserved := spreadMachine.trans allocatedContinues
            cases completion <;> simpa [allocated, spreadRun] using finalPreserved
        | exhausted final | fault fault final =>
            rw [spreadRun] at spreadMachine
            simpa [allocated, spreadRun] using spreadMachine.trans allocatedContinues
  · intro machine valid
    unfold objectSpread
    cases allocated : machine.heap.allocate none true with
    | error fault => trivial
    | ok result =>
        rcases result with ⟨target, heap⟩
        have allocation := Heap.allocate_preserves_machineReferences machine.heap heap none true
          target allocated
        have heapValid := Heap.allocate_preserves_wellFormed machine.heap heap none true target
          (Machine.wellFormed_heap machine valid) allocated
        have allocatedValid := Machine.setHeap_preserves_wellFormed machine heap valid heapValid
          allocation.1
        have spreadValid := spreadSources_preservesResults hook target exclusions sources hookPreserves
        have spreadMachine := spreadValid.1 (machine.setHeap heap) allocatedValid
        have spreadValues := spreadValid.2 (machine.setHeap heap) allocatedValid
        cases spreadRun : spreadSources hook target exclusions sources (machine.setHeap heap) with
        | done completion final =>
            rw [spreadRun] at spreadMachine spreadValues
            cases completion with
            | normal _ =>
                simpa [allocated, spreadRun] using
                  spreadMachine.2.1.preserves_valueValid (.object target) allocation.2
            | thrown value => simpa [allocated, spreadRun] using spreadValues
            | returned value | «break» label | «continue» label =>
                simp [spreadRun, RunResult.CompletionValuesValid]
        | exhausted final | fault fault final =>
            simp [spreadRun, RunResult.CompletionValuesValid]

/-- A normal object-spread result is the fresh ordinary target allocated before any source hook. -/
theorem objectSpread_normal_result (hook : BodyHook P) (sources : List Value)
    (exclusions : List PropertyKey) (hookPreserves : BodyHookPreservesWellFormed hook)
    (initial final : Machine P) (ref : RefId) (valid : initial.WellFormed)
    (run : objectSpread hook sources exclusions initial = .done (.normal ref) final) :
    final.WellFormed ∧ initial.ContinuesFrom final ∧
      ref.value = initial.heap.size ∧
      initial.heap.size ≤ ref.value ∧
      (∀ old, initial.heap.valueValid (.object old) = true → ref ≠ old) ∧
      final.heap.objectKind? ref = some .ordinary ∧
      final.heap.valueValid (.object ref) = true := by
  have preserved := (objectSpread_preservesResults hook sources exclusions hookPreserves).1
    initial valid
  have resultValid := (objectSpread_preservesResults hook sources exclusions hookPreserves).2
    initial valid
  rw [run] at preserved resultValid
  have relational : ref.value = initial.heap.size ∧ initial.heap.size ≤ ref.value ∧
      (∀ old, initial.heap.valueValid (.object old) = true → ref ≠ old) ∧
      final.heap.objectKind? ref = some .ordinary := by
    unfold objectSpread at run
    cases allocated : initial.heap.allocate none true with
    | error fault => simp [allocated] at run
    | ok allocation =>
        rcases allocation with ⟨target, heap⟩
        have targetFacts := Heap.allocate_result_fresh_kind initial.heap heap none true target allocated
        cases spreadRun : spreadSources hook target exclusions sources (initial.setHeap heap) with
        | exhausted next | fault fault next => simp [allocated, spreadRun] at run
        | done completion next =>
            cases completion with
            | normal resultUnit =>
                cases resultUnit
                simp [allocated, spreadRun] at run
                obtain ⟨rfl, rfl⟩ := run
                have lowerBound : initial.heap.size ≤ target.value :=
                  Nat.le_of_eq targetFacts.1.symm
                have spreadPreserved :=
                  (spreadSources_preservesResults hook target exclusions sources hookPreserves).1
                    (initial.setHeap heap)
                    (by
                      have allocationPreserved := Heap.allocate_preserves_machineReferences
                        initial.heap heap none true target allocated
                      have heapValid := Heap.allocate_preserves_wellFormed initial.heap heap none true
                        target (Machine.wellFormed_heap initial valid) allocated
                      exact Machine.setHeap_preserves_wellFormed initial heap valid heapValid
                        allocationPreserved.1)
                rw [spreadRun] at spreadPreserved
                exact ⟨targetFacts.1, lowerBound,
                  fun old oldValid => Heap.fresh_distinct_of_oldValid initial.heap target old
                    lowerBound oldValid,
                  spreadPreserved.2.1.preserves_stableKind target .ordinary targetFacts.2 trivial⟩
            | returned value | thrown value | «break» label | «continue» label =>
                simp [allocated, spreadRun] at run
  exact ⟨preserved.1, preserved.2, relational.1, relational.2.1, relational.2.2.1,
    relational.2.2.2, resultValid⟩

end Copy
end TSLean.JS
