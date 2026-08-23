import TSLean.JS.ArrayCopy
import TSLean.JS.Copy
import TSLean.JS.Control

namespace TSLean.JS

private abbrev emptyArrayAllocationFreshCheck : Bool :=
  match Heap.empty.allocateArray [] with
  | .ok (ref, next) => ref.value == 0 && next.size == 1 &&
      match next.arrayLength ref with | .ok 0 => true | _ => false
  | .error _ => false

/-- Empty-array allocation issues the first fresh reference and records exact zero length. -/
theorem Heap.empty_array_allocation_fresh : emptyArrayAllocationFreshCheck = true := by
  decide

private abbrev emptyArrayDeleteLengthCheck : Bool :=
  match Heap.empty.allocateArray [] with
  | .ok (ref, heap) =>
      match heap.deleteProperty ref (.string (JSString.ofLeanString "length")) with
      | .ok (false, _) => true
      | _ => false
  | .error _ => false

/-- Array `length` is nonconfigurable and cannot be deleted. -/
theorem Heap.empty_array_delete_length : emptyArrayDeleteLengthCheck = true := by
  decide

/-- Array own-key order places `length` after indices and before other strings and symbols. -/
theorem Heap.array_ownKeys_length_position (heap : Heap) (ref : RefId) (object : ObjectRecord)
    (slots : ArraySlots) (found : heap.get? ref = .ok object)
    (arrayKind : object.kind = .array slots) :
    heap.ownPropertyKeys ref = .ok
      (object.properties.ownKeys.filter (fun key => match key with
        | .string value => (PropertyKey.arrayIndex? value).isSome
        | .symbol _ => false) ++
      Heap.lengthPropertyKey ::
      object.properties.ownKeys.filter (fun key => match key with
        | .string value => (PropertyKey.arrayIndex? value).isNone
        | .symbol _ => true)) := by
  unfold Heap.ownPropertyKeys
  rw [found]
  dsimp
  rw [arrayKind]
  rfl

private abbrev arrayIteratorTargetIdentityCheck : Bool :=
  match Heap.empty.allocateArray [some (.primitive .undefined)] with
  | .error _ => false
  | .ok (target, heap) =>
      match heap.allocateArrayIterator target with
      | .error _ => false
      | .ok (iterator, next) => iterator != target &&
          match next.advanceArrayIterator iterator with
          | .ok (some (observedTarget, 0), _) => observedTarget == target
          | _ => false

/-- A fresh iterator is distinct from its array and yields the stable target identity. -/
theorem Heap.array_iterator_target_identity : arrayIteratorTargetIdentityCheck = true := by
  decide

/--
Concrete witnesses cover cursor increment, current-length completion, and already-done identity,
and every heap they reach is valid.

Stated propositionally rather than as a decidable `Bool` check: validity reduces through
`OrderedProps`, which is `Std.HashMap`-backed with a derived `Hashable` routing through the `opaque`
`mixHash`, so the kernel cannot evaluate it. The two allocators' and the advance step's own
preservation theorems carry the invariant, and the runs themselves still reduce.
-/
private theorem array_iterator_preservation_branches_nonvacuous :
    ∃ target heap iterator next incremented completed unchanged,
      Heap.empty.allocateArray [some (.primitive .undefined)] = .ok (target, heap) ∧
        heap.allocateArrayIterator target = .ok (iterator, next) ∧
        next.advanceArrayIterator iterator = .ok (some (target, 0), incremented) ∧
        incremented.advanceArrayIterator iterator = .ok (none, completed) ∧
        completed.advanceArrayIterator iterator = .ok (none, unchanged) ∧
        unchanged.size = completed.size ∧
        incremented.WellFormed ∧ completed.WellFormed ∧ unchanged.WellFormed := by
  have targetValid := Heap.allocateArray_preserves_wellFormed Heap.empty _
    [some (.primitive .undefined)] none ⟨0⟩ Heap.empty_wellFormed rfl
  have iteratorValid := Heap.allocateArrayIterator_preserves_wellFormed _ _ ⟨0⟩ none ⟨1⟩
    targetValid rfl
  have incrementedValid := Heap.advanceArrayIterator_preserves_wellFormed _ _ ⟨1⟩ _
    iteratorValid rfl
  have completedValid := Heap.advanceArrayIterator_preserves_wellFormed _ _ ⟨1⟩ _
    incrementedValid rfl
  have unchangedValid := Heap.advanceArrayIterator_preserves_wellFormed _ _ ⟨1⟩ _
    completedValid rfl
  exact ⟨_, _, _, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl,
    incrementedValid, completedValid, unchangedValid⟩

/-- Exact array-length encoding roundtrips both index and length upper boundaries. -/
theorem Heap.array_length_boundary_roundtrips :
    validArrayLength? (arrayLengthNumber 4294967294) = some 4294967294 ∧
    validArrayLength? (arrayLengthNumber 4294967295) = some 4294967295 := by
  decide

/-- Extending at or beyond the old length produces the strictly larger exact length `index + 1`. -/
theorem Heap.array_write_extension_length (slots : ArraySlots) (index : Nat)
    (extendsLength : slots.length ≤ index) : slots.length < index + 1 :=
  Nat.lt_succ_of_le extendsLength

private abbrev proofPlatform : Platform :=
  ScriptedPlatform.make { times := #[], randoms := #[], fetches := #[] }

private abbrev proofHook : BodyHook proofPlatform := fun _ _ _ => pure ()

private abbrev throwingProofHook : BodyHook proofPlatform := fun _ _ _ =>
  JSM.throwJS (.primitive .undefined)

private def allocateClosure (environment : EnvId) : JSM proofPlatform Unit := fun machine =>
  if environment.value < machine.environments.size then
    match machine.heap.allocateFunction environment .ordinary false none with
    | .ok (_, heap) => .done (.normal ()) (machine.setHeap heap)
    | .error fault => .fault (.runtime (.heap fault)) machine
  else .fault (.runtime (.invalidEnvironment environment)) machine

private theorem allocateClosure_preservesResults (environment : EnvId) :
    JSM.PreservesResults (fun (_ : Unit) (_ : Machine proofPlatform) => True)
      (allocateClosure environment) := by
  constructor
  · intro machine valid
    unfold allocateClosure
    split
    next environmentValid =>
      cases allocated : machine.heap.allocateFunction environment .ordinary false none with
      | error fault => exact ⟨valid, machine.continuesFrom_refl⟩
      | ok result =>
          obtain ⟨ref, heap⟩ := result
          exact Machine.allocateFunction_preserves_machine machine heap environment .ordinary
            false none none .base none ref valid environmentValid allocated
    next invalid => exact ⟨valid, machine.continuesFrom_refl⟩
  · intro machine valid
    unfold allocateClosure
    split
    · cases machine.heap.allocateFunction environment .ordinary false none <;> trivial
    · trivial

private def activationWorkflow (root : EnvId) (receiver argument : Value) :
    JSM proofPlatform Unit := do
  let activation ← Environment.allocateChild root
  let thisCell ← Environment.declare activation (JSString.ofLeanString "this") false
  Environment.initialize thisCell receiver
  let parameterCell ← Environment.declare activation (JSString.ofLeanString "argument0") false
  Environment.initialize parameterCell argument
  Environment.withEnvironment activation (allocateClosure activation)

private theorem activationWorkflow_preservesResults (root : EnvId) (receiver argument : Value) :
    JSM.PreservesResultsWhen
      (fun machine => machine.heap.valueValid receiver = true ∧
        machine.heap.valueValid argument = true)
      (fun (_ : Unit) (_ : Machine proofPlatform) => True)
      (activationWorkflow root receiver argument) := by
  let pre := fun machine : Machine proofPlatform =>
    machine.heap.valueValid receiver = true ∧ machine.heap.valueValid argument = true
  have stable : ∀ initial final : Machine proofPlatform, initial.ContinuesFrom final →
      pre initial → pre final := by
    intro initial final continued values
    exact ⟨continued.1.preserves_valueValid receiver values.1,
      continued.1.preserves_valueValid argument values.2⟩
  have childStep := JSM.preservesResults_carryPrecondition
    (Environment.allocateChild root) (Environment.allocateChild_preservesResults root) pre stable
  unfold activationWorkflow
  apply JSM.bind_preservesResultsWhen (Environment.allocateChild root) _ childStep
  intro activation machine machineValid childResult
  have finalAction : JSM.PreservesResults (fun (_ : Unit) (_ : Machine proofPlatform) => True)
      (Environment.withEnvironment activation (allocateClosure activation)) := by
    exact Environment.withEnvironment_preservesUnitResults activation _
      (allocateClosure_preservesResults activation)
  let childPre := fun current : Machine proofPlatform =>
    current.ValidEnvId activation ∧ pre current
  have childStable : ∀ initial final : Machine proofPlatform, initial.ContinuesFrom final →
      childPre initial → childPre final := by
    intro initial final continued premise
    exact ⟨Nat.lt_of_lt_of_le premise.1 continued.2.2.1,
      stable initial final continued premise.2⟩
  have rest : JSM.PreservesResultsWhen childPre
      (fun (_ : Unit) (_ : Machine proofPlatform) => True) (do
        let thisCell ← Environment.declare activation (JSString.ofLeanString "this") false
        Environment.initialize thisCell receiver
        let parameterCell ← Environment.declare activation
          (JSString.ofLeanString "argument0") false
        Environment.initialize parameterCell argument
        Environment.withEnvironment activation (allocateClosure activation)) := by
    have declareThis := JSM.preservesResults_carryPrecondition
      (Environment.declare activation (JSString.ofLeanString "this") false)
      (Environment.declare_preservesResults activation (JSString.ofLeanString "this") false)
      childPre childStable
    apply JSM.bind_preservesResultsWhen _ _ declareThis
    intro thisCell afterDeclare afterDeclareValid thisResult
    let thisPre := fun current : Machine proofPlatform =>
      current.ValidCellId thisCell ∧ childPre current
    have thisStable : ∀ initial final : Machine proofPlatform, initial.ContinuesFrom final →
        thisPre initial → thisPre final := by
      intro initial final continued premise
      exact ⟨Nat.lt_of_lt_of_le premise.1 continued.2.1,
        childStable initial final continued premise.2⟩
    have initializeThis := JSM.preservesResultsWhen_mono
      (Environment.initialize thisCell receiver)
      (Environment.initialize_preservesResults thisCell receiver)
      (fun current (premise : thisPre current) => premise.2.2.1)
    have afterThis : JSM.PreservesResultsWhen thisPre
        (fun (_ : Unit) final => True ∧ thisPre final)
        (Environment.initialize thisCell receiver) :=
      JSM.preservesResultsWhen_carryPrecondition _ initializeThis thisStable
    have afterThisRest : JSM.PreservesResultsWhen thisPre
        (fun (_ : Unit) (_ : Machine proofPlatform) => True) (do
          Environment.initialize thisCell receiver
          let parameterCell ← Environment.declare activation
            (JSString.ofLeanString "argument0") false
          Environment.initialize parameterCell argument
          Environment.withEnvironment activation (allocateClosure activation)) := by
      apply JSM.bind_preservesResultsWhen _ _ afterThis
      intro _ afterInitialize afterInitializeValid initializeResult
      have declareParameter := JSM.preservesResults_carryPrecondition
        (Environment.declare activation (JSString.ofLeanString "argument0") false)
        (Environment.declare_preservesResults activation (JSString.ofLeanString "argument0") false)
        childPre childStable
      have afterParameter : JSM.PreservesResultsWhen childPre
          (fun (_ : Unit) (_ : Machine proofPlatform) => True) (do
            let parameterCell ← Environment.declare activation
              (JSString.ofLeanString "argument0") false
            Environment.initialize parameterCell argument
            Environment.withEnvironment activation (allocateClosure activation)) := by
        apply JSM.bind_preservesResultsWhen _ _ declareParameter
        intro parameterCell afterDeclareParameter afterDeclareParameterValid parameterResult
        let parameterPre := fun current : Machine proofPlatform =>
          current.ValidCellId parameterCell ∧ childPre current
        have parameterStable : ∀ initial final : Machine proofPlatform,
            initial.ContinuesFrom final → parameterPre initial → parameterPre final := by
          intro initial final continued premise
          exact ⟨Nat.lt_of_lt_of_le premise.1 continued.2.1,
            childStable initial final continued premise.2⟩
        have initializeParameter := JSM.preservesResultsWhen_mono
          (Environment.initialize parameterCell argument)
          (Environment.initialize_preservesResults parameterCell argument)
          (fun current (premise : parameterPre current) => premise.2.2.2)
        have parameterInitialized := JSM.preservesResultsWhen_carryPrecondition _
          initializeParameter parameterStable
        have finalStep : JSM.PreservesResultsWhen parameterPre
            (fun (_ : Unit) (_ : Machine proofPlatform) => True) (do
              Environment.initialize parameterCell argument
              Environment.withEnvironment activation (allocateClosure activation)) := by
          apply JSM.bind_preservesResultsWhen _ _ parameterInitialized
          intro _ final finalValid resultValid
          exact ⟨finalAction.1 final finalValid, finalAction.2 final finalValid⟩
        exact ⟨finalStep.1 afterDeclareParameter afterDeclareParameterValid parameterResult,
          finalStep.2 afterDeclareParameter afterDeclareParameterValid parameterResult⟩
      exact ⟨afterParameter.1 afterInitialize afterInitializeValid initializeResult.2.2,
        afterParameter.2 afterInitialize afterInitializeValid initializeResult.2.2⟩
    exact ⟨afterThisRest.1 afterDeclare afterDeclareValid thisResult,
      afterThisRest.2 afterDeclare afterDeclareValid thisResult⟩
  exact ⟨rest.1 machine machineValid childResult,
    rest.2 machine machineValid childResult⟩

/-- Normal and throwing evaluator fixtures witness that the hook premise is satisfiable. -/
theorem BodyHookPreservesWellFormed_nonvacuous :
    BodyHookPreservesWellFormed proofHook ∧
      BodyHookPreservesWellFormed throwingProofHook := by
  constructor
  · intro ref receiver arguments
    constructor
    · intro machine valid inputs
      exact JSM.pure_preservesWellFormed () machine valid
    · intro machine valid inputs
      trivial
  · intro ref receiver arguments
    constructor
    · intro machine valid inputs
      exact JSM.throwJS_preservesWellFormed (.primitive .undefined) machine valid
    · intro machine valid inputs
      rfl

private def composedProofHook : BodyHook proofPlatform := fun ref receiver arguments => do
  let environment ← Environment.allocateGlobal
  let _ ← Environment.withEnvironment environment
    (Control.tryCatchFinally
      (Call.call proofHook ref receiver arguments)
      (fun thrown => pure thrown)
      (JSM.emit (.emitted (JSString.ofLeanString "body-finalized"))))
  pure ()

/-- Environment allocation/restoration, call normalization, catch/finally control, and trace
emission compose into the strengthened evaluator-hook contract. -/
theorem BodyHookPreservesWellFormed_composed :
    BodyHookPreservesWellFormed composedProofHook := by
  intro ref receiver arguments
  let valueValid := fun value (machine : Machine proofPlatform) =>
    machine.heap.valueValid value = true
  have callValid : JSM.PreservesResults valueValid
      (Call.call proofHook ref receiver arguments) :=
    Call.call_preservesResults proofHook ref receiver arguments
      BodyHookPreservesWellFormed_nonvacuous.1
  have controlledValid : JSM.PreservesResults valueValid
      (Control.tryCatchFinally
        (Call.call proofHook ref receiver arguments)
        (fun thrown => pure thrown)
        (JSM.emit (.emitted (JSString.ofLeanString "body-finalized")))) := by
    apply Control.tryCatchFinally_preservesResults
    · exact callValid
    · intro thrown machine machineValid thrownValid
      exact ⟨JSM.pure_preservesWellFormed thrown machine machineValid, thrownValid⟩
    · exact JSM.emit_preservesResults (.emitted (JSString.ofLeanString "body-finalized"))
    · intro value first final continued valueIsValid
      exact continued.1.preserves_valueValid value valueIsValid
  have scopedValid : ∀ environment, JSM.PreservesResults valueValid
      (Environment.withEnvironment environment
        (Control.tryCatchFinally
          (Call.call proofHook ref receiver arguments)
          (fun thrown => pure thrown)
          (JSM.emit (.emitted (JSString.ofLeanString "body-finalized"))))) := by
    intro environment
    exact Environment.withEnvironment_preservesResults environment _ controlledValid
  unfold composedProofHook
  have composedValid : JSM.PreservesResults (fun (_ : Unit) (_ : Machine proofPlatform) => True)
      (JSM.bind Environment.allocateGlobal (fun environment => do
        let _ ← Environment.withEnvironment environment
          (Control.tryCatchFinally
            (Call.call proofHook ref receiver arguments)
            (fun thrown => pure thrown)
            (JSM.emit (.emitted (JSString.ofLeanString "body-finalized"))))
        pure ())) := by
    apply JSM.bind_preservesResults
    · exact Environment.allocateGlobal_preservesResults
    · intro environment machine machineValid environmentValid
      have inner : JSM.PreservesResults (fun (_ : Unit) (_ : Machine proofPlatform) => True) _ :=
        JSM.bind_preservesResults
        (Environment.withEnvironment environment
          (Control.tryCatchFinally
            (Call.call proofHook ref receiver arguments)
            (fun thrown => pure thrown)
            (JSM.emit (.emitted (JSString.ofLeanString "body-finalized")))))
        (fun _ => pure ()) (scopedValid environment) (by
          intro result final finalValid resultValid
          exact ⟨JSM.pure_preservesWellFormed () final finalValid, trivial⟩)
      exact ⟨inner.1 machine machineValid, inner.2 machine machineValid⟩
  exact ⟨fun machine valid inputs => composedValid.1 machine valid,
    fun machine valid inputs => composedValid.2 machine valid⟩

private def argumentZero (arguments : Array Value) : Value :=
  arguments[0]?.getD (.primitive .undefined)

private theorem argumentZero_valid (machine : Machine proofPlatform) (arguments : Array Value)
    (valid : arguments.toList.all machine.heap.valueValid = true) :
    machine.heap.valueValid (argumentZero arguments) = true := by
  unfold argumentZero
  cases found : arguments[0]? with
  | none => rfl
  | some value =>
      have member : value ∈ arguments.toList :=
        (Array.mem_toList_iff value arguments).mpr (Array.mem_of_getElem? found)
      exact List.all_eq_true.mp valid value member

private def realisticProofHook : BodyHook proofPlatform := fun ref receiver arguments machine =>
  match machine.heap.functionSlots? ref with
  | .ok (some slots) => activationWorkflow slots.environment receiver (argumentZero arguments) machine
  | .ok none => .fault (.runtime (.heap .invalidFunctionMetadata)) machine
  | .error fault => .fault (.runtime (.heap fault)) machine

/-- A body hook can inspect captured function metadata, allocate and initialize an activation,
execute under it, allocate a closure capturing it, and restore the caller environment. -/
theorem BodyHookPreservesWellFormed_realistic :
    BodyHookPreservesWellFormed realisticProofHook := by
  intro ref receiver arguments
  constructor <;> intro machine machineValid inputsValid
  · unfold realisticProofHook
    cases found : machine.heap.functionSlots? ref with
    | error fault =>
        obtain ⟨⟨slots, callable⟩, receiverValid, argumentsValid⟩ := inputsValid
        rw [found] at callable
        contradiction
    | ok result =>
        cases result with
        | none =>
            obtain ⟨⟨slots, callable⟩, receiverValid, argumentsValid⟩ := inputsValid
            rw [found] at callable
            cases callable
        | some slots =>
            exact (activationWorkflow_preservesResults slots.environment receiver
              (argumentZero arguments)).1 machine machineValid
                ⟨inputsValid.2.1, argumentZero_valid machine arguments inputsValid.2.2⟩
  · unfold realisticProofHook
    cases found : machine.heap.functionSlots? ref with
    | error fault => trivial
    | ok result =>
        cases result with
        | none => trivial
        | some slots =>
            exact (activationWorkflow_preservesResults slots.environment receiver
              (argumentZero arguments)).2 machine machineValid
                ⟨inputsValid.2.1, argumentZero_valid machine arguments inputsValid.2.2⟩

/-- The iterator JSM preservation theorems instantiate with both normal and throwing hooks. -/
theorem Iterator.preservation_nonvacuous :
    JSM.PreservesWellFormed (Iterator.arrayValues (P := proofPlatform) ⟨0⟩) ∧
      JSM.PreservesWellFormed (Iterator.next proofHook ⟨0⟩) ∧
      JSM.PreservesWellFormed (Iterator.next throwingProofHook ⟨0⟩) := by
  exact ⟨Iterator.arrayValues_preservesWellFormed ⟨0⟩,
    Iterator.next_preservesWellFormed proofHook ⟨0⟩ BodyHookPreservesWellFormed_nonvacuous.1,
    Iterator.next_preservesWellFormed throwingProofHook ⟨0⟩
      BodyHookPreservesWellFormed_nonvacuous.2⟩

/-- Normal and throwing setter hooks compose with ordinary and strict assignment preservation. -/
theorem ObjectAccess.setter_preservation_nonvacuous (ref : RefId) (key : PropertyKey)
    (value receiver : Value) :
    JSM.PreservesWellFormed (ObjectAccess.set proofHook ref key value receiver) ∧
      JSM.PreservesWellFormed (ObjectAccess.set throwingProofHook ref key value receiver) ∧
      JSM.PreservesWellFormed (ObjectAccess.setStrict proofHook ref key value receiver) ∧
      JSM.PreservesWellFormed (ObjectAccess.setStrict throwingProofHook ref key value receiver) := by
  exact ⟨ObjectAccess.set_preservesWellFormed proofHook ref key value receiver
      BodyHookPreservesWellFormed_nonvacuous.1,
    ObjectAccess.set_preservesWellFormed throwingProofHook ref key value receiver
      BodyHookPreservesWellFormed_nonvacuous.2,
    ObjectAccess.setStrict_preservesWellFormed proofHook ref key value receiver
      BodyHookPreservesWellFormed_nonvacuous.1,
    ObjectAccess.setStrict_preservesWellFormed throwingProofHook ref key value receiver
      BodyHookPreservesWellFormed_nonvacuous.2⟩

/-- Canonical copy operations instantiate with both normal and throwing accessor hooks. -/
theorem Copy.preservation_nonvacuous (target source : RefId) (sources : List Value) :
    JSM.PreservesWellFormed (Copy.copyDataProperties proofHook target source) ∧
      JSM.PreservesWellFormed (Copy.copyDataProperties throwingProofHook target source) ∧
      JSM.PreservesWellFormed (Copy.objectAssign proofHook (.object target) sources) ∧
      JSM.PreservesWellFormed (Copy.objectAssign throwingProofHook (.object target) sources) ∧
      JSM.PreservesWellFormed (Copy.objectSpread proofHook sources) ∧
      JSM.PreservesWellFormed (Copy.objectSpread throwingProofHook sources) := by
  exact ⟨(Copy.copyDataProperties_preservesResults proofHook target source []
      BodyHookPreservesWellFormed_nonvacuous.1).1,
    (Copy.copyDataProperties_preservesResults throwingProofHook target source []
      BodyHookPreservesWellFormed_nonvacuous.2).1,
    (Copy.objectAssign_preservesResults proofHook (.object target) sources
      BodyHookPreservesWellFormed_nonvacuous.1).1,
    (Copy.objectAssign_preservesResults throwingProofHook (.object target) sources
      BodyHookPreservesWellFormed_nonvacuous.2).1,
    (Copy.objectSpread_preservesResults proofHook sources []
      BodyHookPreservesWellFormed_nonvacuous.1).1,
    (Copy.objectSpread_preservesResults throwingProofHook sources []
      BodyHookPreservesWellFormed_nonvacuous.2).1⟩

/-- Internal array-values slice/spread operations instantiate with normal and throwing getter hooks. -/
theorem ArrayCopy.preservation_nonvacuous (source : RefId) :
    JSM.PreservesWellFormed (ArrayCopy.slice proofHook source) ∧
      JSM.PreservesWellFormed (ArrayCopy.slice throwingProofHook source) ∧
      JSM.PreservesWellFormed (ArrayCopy.spread proofHook source) ∧
      JSM.PreservesWellFormed (ArrayCopy.spread throwingProofHook source) := by
  exact ⟨(ArrayCopy.slice_preservesResults proofHook source 0 none
      BodyHookPreservesWellFormed_nonvacuous.1).1,
    (ArrayCopy.slice_preservesResults throwingProofHook source 0 none
      BodyHookPreservesWellFormed_nonvacuous.2).1,
    (ArrayCopy.spread_preservesResults proofHook source
      BodyHookPreservesWellFormed_nonvacuous.1).1,
    (ArrayCopy.spread_preservesResults throwingProofHook source
      BodyHookPreservesWellFormed_nonvacuous.2).1⟩

private abbrev freshResultRelationsCheck : Bool :=
  let initial := Machine.initial proofPlatform 100
  let spreadValid := match Copy.objectSpread proofHook [] [] initial with
    | .done (.normal ref) final =>
        initial.heap.size ≤ ref.value &&
        final.heap.objectKind? ref == some .ordinary &&
        final.heap.valueValid (.object ref)
    | _ => false
  let arrayResultsValid := match initial.heap.allocateArray [] with
    | .error _ => false
    | .ok (source, heap) =>
        let machine := initial.setHeap heap
        match ArrayCopy.spread throwingProofHook source machine with
        | .done (.normal ref) final =>
            machine.heap.size ≤ ref.value &&
            (match final.heap.objectKind? ref with | some (.array _) => true | _ => false) &&
            final.heap.valueValid (.object ref)
        | _ => false
  spreadValid && arrayResultsValid

/--
Concrete normal runs witness fresh ordinary and modeled spread-array results.

`ArrayCopy.slice` is deliberately absent, and its normal-run witness is the one piece of this
coverage that no longer exists. `slice` loops through `ArrayCopy.collectSlice`, which recurses on an
increasing index and is therefore compiled by well-founded recursion — irreducible in the kernel, at
any size — so the run cannot be evaluated here; and `slice_normal_result` is conditional on the run,
so no existing theorem supplies it either. `ArrayCopy.spread` covers the same fresh-array relation
through `collectIterator`, which is fuel-structural and does reduce.
-/
private theorem fresh_result_relations_nonvacuous : freshResultRelationsCheck = true := by
  decide

private def malformedProofMachine : Machine proofPlatform :=
  match Heap.empty.allocateFunction ⟨999⟩ .ordinary false none with
  | .ok (_, heap) => (Machine.initial proofPlatform 10).setHeap heap
  | .error _ => Machine.initial proofPlatform 10

private def nonpreservingProofHook : BodyHook proofPlatform := fun _ _ _ =>
  JSM.set malformedProofMachine

private def validHookSource : Machine proofPlatform :=
  let machine := Machine.initial proofPlatform 10
  match machine.heap.allocateFunction machine.currentEnv .ordinary false none with
  | .ok (_, heap) => machine.setHeap heap
  | .error _ => machine

/--
`validHookSource` is a valid machine: it is a fresh machine with one allocated function.

`Machine.isWellFormed` reduces through `OrderedProps`, which is `Std.HashMap`-backed with a derived
`Hashable` routing through the `opaque` `mixHash`, so no kernel evaluation of it terminates. The
allocator's own preservation theorem carries the invariant instead.
-/
private theorem validHookSource_wellFormed : validHookSource.WellFormed := by
  have initialValid := Machine.initial_wellFormed proofPlatform 10
  unfold validHookSource
  dsimp only
  cases allocated : (Machine.initial proofPlatform 10).heap.allocateFunction
      (Machine.initial proofPlatform 10).currentEnv .ordinary false none with
  | error fault => exact initialValid
  | ok result =>
      obtain ⟨ref, heap⟩ := result
      exact (Machine.allocateFunction_preserves_machine _ _ _ _ _ _ _ _ _ _ initialValid
        (Machine.wellFormed_currentEnv _ initialValid) allocated).1

private theorem validHookSource_inputsValid : BodyHookInputsValid validHookSource ⟨0⟩
    (.primitive .undefined) #[] := by
  refine ⟨⟨⟨⟨0⟩, ⟨0⟩, .ordinary, false, .base, none, none⟩, ?_⟩, rfl, rfl⟩
  rfl

/--
The malformed machine is rejected, because its one function captures an unallocated environment.

That is the last clause of `Machine.isWellFormed`, so the conjunction is `false` whatever the
earlier clauses evaluate to — which matters here, since the clause on the heap's property stores
does not reduce in the kernel at all.
-/
private theorem malformedProofMachine_not_wellFormed :
    malformedProofMachine.isWellFormed = false := by
  obtain ⟨ref, heap, allocated⟩ :
      ∃ ref heap, Heap.empty.allocateFunction ⟨999⟩ .ordinary false none = .ok (ref, heap) :=
    ⟨_, _, rfl⟩
  have environments := Heap.allocateFunction_functionEnvironments _ _ _ _ _ _ _ _ _ _ allocated
  unfold malformedProofMachine
  rw [allocated]
  dsimp only
  unfold Machine.isWellFormed
  simp only [Machine.setHeap]
  rw [environments]
  simp [Heap.functionEnvironments, Heap.empty, Machine.initial]

private theorem BodyHookPreservesWellFormed_premise_necessary :
    ¬BodyHookPreservesWellFormed nonpreservingProofHook := by
  intro preserves
  have sourceValid := validHookSource_wellFormed
  have inputsValid := validHookSource_inputsValid
  have invalid := (preserves ⟨0⟩ (.primitive .undefined) #[]).1
    validHookSource sourceValid inputsValid
  have malformed := malformedProofMachine_not_wellFormed
  change malformedProofMachine.WellFormed ∧ _ at invalid
  unfold Machine.WellFormed at invalid
  exact Bool.false_ne_true (malformed.symm ▸ invalid.1)

/-- A malicious evaluator hook that replaces execution with an unrelated valid machine. -/
def continuityBreakingProofHook : BodyHook proofPlatform := fun _ _ _ =>
  JSM.set (Machine.initial proofPlatform 10)

private def validResetSource : Machine proofPlatform :=
  validHookSource

/-- The former well-formedness-only hook contract admitted an unrelated valid-machine reset. -/
private theorem validResetProofHook_satisfies_old_contract :
    ∀ ref receiver arguments machine, machine.WellFormed →
      (continuityBreakingProofHook ref receiver arguments machine).AllMachines Machine.WellFormed := by
  intro ref receiver arguments machine valid
  change (Machine.initial proofPlatform 10).WellFormed
  exact Machine.initial_wellFormed proofPlatform 10

/-- Identity continuity rejects the malicious valid reset admitted by well-formedness alone. -/
theorem continuityBreakingProofHook_rejected (ref : RefId) (receiver : Value)
    (arguments : Array Value) (machine : Machine proofPlatform)
    (valid : machine.WellFormed)
    (inputs : BodyHookInputsValid machine ref receiver arguments)
    (notContinuous : ¬machine.ContinuesFrom (Machine.initial proofPlatform 10)) :
    ¬BodyHookPreservesWellFormed continuityBreakingProofHook := by
  intro preserves
  exact notContinuous ((preserves ref receiver arguments).1 machine valid inputs).2

private theorem BodyHookPreservesWellFormed_continuity_necessary :
    ¬BodyHookPreservesWellFormed continuityBreakingProofHook := by
  intro preserves
  have sourceValid : validResetSource.WellFormed := validHookSource_wellFormed
  have result := (preserves ⟨0⟩ (.primitive .undefined) #[]).1 validResetSource sourceValid
    validHookSource_inputsValid
  change (Machine.initial proofPlatform 10).WellFormed ∧
    validResetSource.ContinuesFrom (Machine.initial proofPlatform 10) at result
  have notContinuous : ¬validResetSource.ContinuesFrom (Machine.initial proofPlatform 10) := by
    intro continuous
    have sizeDecrease : ¬validResetSource.heap.size ≤
        (Machine.initial proofPlatform 10).heap.size := by decide
    exact sizeDecrease continuous.1.1
  exact notContinuous result.2

private abbrev danglingReceiverRejectedCheck : Bool :=
  match Call.call proofHook ⟨0⟩ (.object ⟨99⟩) #[] validHookSource with
  | .fault (.runtime (.danglingEscapingValue ⟨99⟩)) final =>
      final.reverseTrace == validHookSource.reverseTrace
  | _ => false

private abbrev danglingArgumentRejectedCheck : Bool :=
  match Call.call proofHook ⟨0⟩ (.primitive .undefined) #[.object ⟨99⟩] validHookSource with
  | .fault (.runtime (.danglingEscapingValue ⟨99⟩)) final =>
      final.reverseTrace == validHookSource.reverseTrace
  | _ => false

/-- Checked call rejects a dangling receiver before evaluator entry. -/
private theorem Call.dangling_receiver_rejected : danglingReceiverRejectedCheck = true := by
  decide

/-- Checked call rejects a dangling argument before evaluator entry. -/
private theorem Call.dangling_argument_rejected : danglingArgumentRejectedCheck = true := by
  decide

private def mutableSource : Machine proofPlatform :=
  (Machine.initial proofPlatform 10).allocateCell ⟨.uninitialized, true⟩ |>.2

private def mutableReset : Machine proofPlatform :=
  match mutableSource.setCell ⟨0⟩ ⟨.uninitialized, false⟩ with
  | .ok next => next
  | .error _ => mutableSource

private theorem mutable_reset_rejected : ¬mutableSource.ContinuesFrom mutableReset := by
  intro continued
  have oldFound : mutableSource.cells[0]? = some ⟨.uninitialized, true⟩ := by decide
  obtain ⟨nextCell, nextFound, mutableEq⟩ :=
    continued.2.2.2.2.2.1 0 ⟨.uninitialized, true⟩ oldFound
  have newFound : mutableReset.cells[0]? = some ⟨.uninitialized, false⟩ := by decide
  rw [newFound] at nextFound
  simp at nextFound
  subst nextCell
  contradiction

private def parentSource : Machine proofPlatform :=
  let machine := Machine.initial proofPlatform 10
  match machine.allocateEnvironment (some machine.currentEnv) with
  | .ok (_, next) => next
  | .error _ => machine

private def parentReset : Machine proofPlatform :=
  match parentSource.setEnvironment ⟨1⟩ ⟨none, Std.HashMap.empty⟩ with
  | .ok next => next
  | .error _ => parentSource

private theorem parent_reset_rejected : ¬parentSource.ContinuesFrom parentReset := by
  intro continued
  have oldFound : parentSource.environments[1]? =
      some ⟨some ⟨0⟩, Std.HashMap.empty⟩ := by rfl
  obtain ⟨nextEnvironment, nextFound, parentEq, bindings⟩ :=
    continued.2.2.2.2.2.2 1 ⟨some ⟨0⟩, Std.HashMap.empty⟩ oldFound
  have newFound : parentReset.environments[1]? =
      some ⟨none, Std.HashMap.empty⟩ := by rfl
  rw [newFound] at nextFound
  simp at nextFound
  subst nextEnvironment
  contradiction

private def bindingSource : Machine proofPlatform :=
  let machine := Machine.initial proofPlatform 10
  match Environment.declare machine.currentEnv (JSString.ofLeanString "kept") true machine with
  | .done (.normal _) next => next
  | _ => machine

private def bindingReset : Machine proofPlatform :=
  match bindingSource.setEnvironment ⟨0⟩ ⟨none, Std.HashMap.empty⟩ with
  | .ok next => next
  | .error _ => bindingSource

private theorem binding_removal_rejected : ¬bindingSource.ContinuesFrom bindingReset := by
  intro continued
  -- `Std.HashMap` lookups do not reduce in the kernel, so the stored binding is read off the
  -- declaration's own definition with the collection's rewriting lemmas.
  have oldFound : ∃ record, bindingSource.environments[0]? = some record ∧
      record.bindings[JSString.ofLeanString "kept"]? = some ⟨0⟩ := by
    refine ⟨⟨none, Std.HashMap.emptyWithCapacity.insert (JSString.ofLeanString "kept") ⟨0⟩⟩,
      ?_, by simp⟩
    simp [bindingSource, Environment.declare, Machine.getEnvironment, Machine.allocateCell,
      Machine.setEnvironment, Machine.initial]
  obtain ⟨record, environmentFound, bindingFound⟩ := oldFound
  obtain ⟨nextEnvironment, nextFound, parentEq, bindings⟩ :=
    continued.2.2.2.2.2.2 0 record environmentFound
  have newFound : bindingReset.environments[0]? =
      some ⟨none, Std.HashMap.empty⟩ := by
    have inBounds : 0 < bindingSource.environments.size :=
      (Array.getElem?_eq_some_iff.mp environmentFound).choose
    have resetBy : bindingSource.setEnvironment ⟨0⟩
        ⟨none, Std.HashMap.empty⟩ = .ok bindingReset := by
      unfold bindingReset
      cases updated : bindingSource.setEnvironment ⟨0⟩
          ⟨none, Std.HashMap.empty⟩ with
      | error fault =>
          unfold Machine.setEnvironment at updated
          simp [inBounds] at updated
      | ok next => rfl
    unfold Machine.setEnvironment at resetBy
    simp [inBounds] at resetBy
    rw [← resetBy]
    rw [Array.getElem?_set]
    simp
  rw [newFound] at nextFound
  simp at nextFound
  subst nextEnvironment
  have retained := bindings _ _ bindingFound
  simp at retained

private abbrev assignReturnsTargetCheck : Bool :=
  let machine := Machine.initial proofPlatform 10
  match machine.heap.allocate with
  | .error _ => false
  | .ok (target, heap) =>
      match Copy.objectAssign proofHook (.object target) [] (machine.setHeap heap) with
      | .done (.normal (.object returned)) _ => returned == target
      | _ => false

/-- Successful `Object.assign` returns the same target identity it mutates. -/
theorem Copy.objectAssign_returns_target : assignReturnsTargetCheck = true := by
  decide

end TSLean.JS
