import TSLean.JS.Call
import TSLean.JS.Prototype

namespace TSLean.JS

namespace ObjectAccess

private def undefined : Value := .primitive .undefined

private def typeError (message : String) : Value :=
  .primitive (.string (JSString.ofLeanString ("TypeError: " ++ message)))

private def rangeError (message : String) : Value :=
  .primitive (.string (JSString.ofLeanString ("RangeError: " ++ message)))

private def heapFault (fault : HeapFault) : ModelFault := .runtime (.heap fault)

private def prototypeFault : PrototypeFault → ModelFault
  | .heap fault => heapFault fault
  | .cycleOrFuelExhausted => heapFault .cycleOrFuelExhausted

/-- Produces a catchable ECMAScript TypeError completion. -/
def throwTypeError (message : String) : JSM P α := JSM.throwJS (typeError message)

/-- Produces a catchable ECMAScript RangeError completion. -/
def throwRangeError (message : String) : JSM P α := JSM.throwJS (rangeError message)

/-- Gets a property through the prototype chain, preserving the original receiver for accessors. -/
def get (hook : BodyHook P) (ref : RefId) (key : PropertyKey) (receiver : Value) : JSM P Value :=
  fun machine =>
    match Prototype.lookup machine.heap ref key with
    | .error fault => .fault (prototypeFault fault) machine
    | .ok none => .done (.normal undefined) machine
    | .ok (some (_, .data descriptor)) => .done (.normal descriptor.value) machine
    | .ok (some (_, .accessor descriptor)) =>
        match descriptor.get with
        | none => .done (.normal undefined) machine
        | some getter => Call.call hook getter receiver #[] machine

/-- Ordinary `Get` preserves complete machine validity under a preserving evaluator hook. -/
theorem get_preservesWellFormed (hook : BodyHook P) (ref : RefId) (key : PropertyKey)
    (receiver : Value) (hookPreserves : BodyHookPreservesWellFormed hook) :
    JSM.PreservesWellFormed (get hook ref key receiver) := by
  intro machine valid
  unfold get
  cases lookup : Prototype.lookup machine.heap ref key with
  | error fault => exact ⟨valid, machine.continuesFrom_refl⟩
  | ok result =>
      cases result with
      | none => exact ⟨valid, machine.continuesFrom_refl⟩
      | some found =>
          rcases found with ⟨owner, descriptor⟩
          cases descriptor with
          | data descriptor => exact ⟨valid, machine.continuesFrom_refl⟩
          | accessor descriptor =>
              cases getResult : descriptor.get with
              | none => simpa [getResult] using And.intro valid machine.continuesFrom_refl
              | some getterRef =>
                  simpa [getResult] using
                    Call.call_preservesWellFormed hook getterRef receiver #[] hookPreserves
                      machine valid

/-- Ordinary `Get` validates every normal and thrown value in its final heap. -/
theorem get_preservesResults (hook : BodyHook P) (ref : RefId) (key : PropertyKey)
    (receiver : Value) (hookPreserves : BodyHookPreservesWellFormed hook) :
    JSM.PreservesResults (fun value machine => machine.heap.valueValid value = true)
      (get hook ref key receiver) := by
  refine ⟨get_preservesWellFormed hook ref key receiver hookPreserves, ?_⟩
  intro machine valid
  unfold get
  cases lookup : Prototype.lookup machine.heap ref key with
  | error fault => trivial
  | ok result =>
      cases result with
      | none => rfl
      | some found =>
          rcases found with ⟨owner, descriptor⟩
          cases descriptor with
          | data descriptor =>
              exact Prototype.lookup_data_valueValid machine.heap ref key owner descriptor
                (Machine.wellFormed_heap machine valid) lookup
          | accessor descriptor =>
              cases getter : descriptor.get with
              | none => simp [getter, RunResult.CompletionValuesValid, undefined, Heap.valueValid]
              | some getterRef =>
                  simpa [getter] using
                    (Call.call_preservesResults hook getterRef receiver #[] hookPreserves).2
                      machine valid

private def defineValue (heap : Heap) (receiver : RefId) (key : PropertyKey) (value : Value) :
    Except DefinePropertyFault (Bool × Heap) :=
  match OrdinaryObject.getOwnProperty heap receiver key with
  | .error fault => .error (.heap fault)
  | .ok (some (.accessor _)) => .ok (false, heap)
  | .ok (some (.data descriptor)) =>
      if descriptor.writable then
        heap.defineOwnProperty receiver key { value := .present value }
      else .ok (false, heap)
  | .ok none => heap.createDataProperty receiver key value

private def completeDefinition (result : Except DefinePropertyFault (Bool × Heap)) : JSM P Bool :=
  fun machine =>
    match result with
    | .ok (success, heap) => .done (.normal success) (machine.setHeap heap)
    | .error (.heap fault) => .fault (heapFault fault) machine
    | .error (.invalidValueRef ref) | .error (.invalidAccessor ref) =>
        .fault (heapFault (.invalidRef ref)) machine
    | .error (.syntax _) => .done (.thrown (typeError "invalid property descriptor")) machine
    | .error (.nonCallableAccessor _) =>
        .done (.thrown (typeError "property accessor is not callable")) machine
    | .error (.invalidArrayLength _) | .error (.arrayTooLong _) =>
        .done (.thrown (rangeError "invalid array length")) machine
    | .error (.invalidArrayLengthValue _) =>
        .done (.thrown (typeError "array length must be a number")) machine

private theorem completeDefinition_valuesValid
    (result : Except DefinePropertyFault (Bool × Heap)) (machine : Machine P) :
    (completeDefinition result machine).CompletionValuesValid (fun _ _ => True) := by
  cases result with
  | ok outcome => simp [completeDefinition, RunResult.CompletionValuesValid]
  | error fault => cases fault <;>
      simp [completeDefinition, RunResult.CompletionValuesValid, typeError, rangeError,
        Heap.valueValid]

private theorem completeDefinition_result_preservesWellFormed
    (machine : Machine P) (result : Except DefinePropertyFault (Bool × Heap))
    (valid : machine.WellFormed)
    (preserves : ∀ success heap, result = .ok (success, heap) →
      heap.WellFormed ∧ machine.heap.MachineReferencesPreserved heap) :
    (completeDefinition result machine).MachinePreserved machine := by
  unfold completeDefinition
  cases result with
  | ok outcome =>
      rcases outcome with ⟨success, heap⟩
      have facts := preserves success heap rfl
      exact ⟨Machine.setHeap_preserves_wellFormed machine heap valid facts.1 facts.2,
        Machine.setHeap_continuesFrom_machineReferences machine heap valid facts.1 facts.2⟩
  | error fault =>
      cases fault <;> exact ⟨valid, machine.continuesFrom_refl⟩

private theorem defineValue_preserves (heap next : Heap) (receiver : RefId) (key : PropertyKey)
    (value : Value) (success : Bool) (valid : heap.WellFormed)
    (defined : defineValue heap receiver key value = .ok (success, next)) :
    next.WellFormed ∧ heap.MachineReferencesPreserved next := by
  unfold defineValue at defined
  cases own : OrdinaryObject.getOwnProperty heap receiver key with
  | error fault => simp [own] at defined
  | ok descriptor =>
      cases descriptor with
      | none =>
          exact ⟨Heap.createDataProperty_preserves_wellFormed heap next receiver key value success
              valid (by simpa [own] using defined),
            Heap.createDataProperty_preserves_machineReferences heap next receiver key value success
              (by simpa [own] using defined)⟩
      | some descriptor =>
          cases descriptor with
          | accessor descriptor =>
              simp [own] at defined
              obtain ⟨rfl, rfl⟩ := defined
              exact ⟨valid, ⟨Nat.le_refl _, rfl, fun _ kind found =>
                ⟨kind, found, ObjectKind.continuesFrom_refl kind⟩⟩⟩
          | data descriptor =>
              cases writable : descriptor.writable with
              | false =>
                  simp [own, writable] at defined
                  obtain ⟨rfl, rfl⟩ := defined
                  exact ⟨valid, ⟨Nat.le_refl _, rfl, fun _ kind found =>
                    ⟨kind, found, ObjectKind.continuesFrom_refl kind⟩⟩⟩
              | true =>
                  exact ⟨Heap.defineOwnProperty_preserves_wellFormed heap next receiver key
                      { value := .present value } success valid (by simpa [own, writable] using defined),
                    Heap.defineOwnProperty_preserves_machineReferences heap next receiver key
                      { value := .present value } success (by simpa [own, writable] using defined)⟩

/-- Defines a property while preserving JavaScript descriptor and array-length exceptions. -/
def defineOwnProperty (ref : RefId) (key : PropertyKey) (update : DescriptorUpdate) : JSM P Bool :=
  fun machine => completeDefinition (machine.heap.defineOwnProperty ref key update) machine

/-- Creates an enumerable writable configurable data property with typed semantic completion. -/
def createDataProperty (ref : RefId) (key : PropertyKey) (value : Value) : JSM P Bool :=
  fun machine => completeDefinition (machine.heap.createDataProperty ref key value) machine

/-- CreateDataProperty preserves continuity and validates every abrupt completion. -/
theorem createDataProperty_preservesResults (ref : RefId) (key : PropertyKey) (value : Value) :
    JSM.PreservesResults (fun _ _ => True) (createDataProperty (P := P) ref key value) := by
  constructor
  · intro machine valid
    unfold createDataProperty
    apply completeDefinition_result_preservesWellFormed machine _ valid
    intro success heap created
    exact ⟨Heap.createDataProperty_preserves_wellFormed machine.heap heap ref key value success
        (Machine.wellFormed_heap machine valid) created,
      Heap.createDataProperty_preserves_machineReferences machine.heap heap ref key value success
        created⟩
  · intro machine valid
    exact completeDefinition_valuesValid (machine.heap.createDataProperty ref key value) machine

/-- Sets a property using ordinary receiver semantics. Inherited writable data properties create
an own receiver property; inherited accessors invoke their setter with that receiver. -/
def set (hook : BodyHook P) (ref : RefId) (key : PropertyKey) (value receiver : Value) : JSM P Bool :=
  fun machine =>
    match Prototype.lookup machine.heap ref key with
    | .error fault => .fault (prototypeFault fault) machine
    | .ok (some (_, .data descriptor)) =>
        if !descriptor.writable then .done (.normal false) machine
        else
          match receiver with
          | .primitive _ => .done (.normal false) machine
          | .object receiverRef =>
              completeDefinition (defineValue machine.heap receiverRef key value) machine
    | .ok (some (_, .accessor descriptor)) =>
        match descriptor.set with
        | none => .done (.normal false) machine
        | some setter =>
            match Call.call hook setter receiver #[value] machine with
            | .done (.normal _) next => .done (.normal true) next
            | .done (.thrown thrown) next => .done (.thrown thrown) next
            | .done (.returned _) next | .done (.break _) next | .done (.continue _) next =>
                .fault (.runtime .escapingFunctionControl) next
            | .exhausted next => .exhausted next
            | .fault fault next => .fault fault next
    | .ok none =>
        match receiver with
        | .primitive _ => .done (.normal false) machine
        | .object receiverRef =>
             completeDefinition (defineValue machine.heap receiverRef key value) machine

/-- Ordinary `Set` preserves complete machine validity for every rejection, definition commit,
checked setter completion, model fault, and exhaustion outcome. -/
theorem set_preservesWellFormed (hook : BodyHook P) (ref : RefId) (key : PropertyKey)
    (value receiver : Value) (hookPreserves : BodyHookPreservesWellFormed hook) :
    JSM.PreservesWellFormed (set hook ref key value receiver) := by
  intro machine valid
  unfold set
  cases lookup : Prototype.lookup machine.heap ref key with
  | error fault => exact ⟨valid, machine.continuesFrom_refl⟩
  | ok result =>
      cases result with
      | none =>
          cases receiver with
          | primitive receiver => exact ⟨valid, machine.continuesFrom_refl⟩
          | object receiverRef =>
              apply completeDefinition_result_preservesWellFormed machine _ valid
              intro success next defined
              exact defineValue_preserves machine.heap next receiverRef key value success
                (Machine.wellFormed_heap machine valid) defined
      | some found =>
          rcases found with ⟨owner, descriptor⟩
          cases descriptor with
          | data descriptor =>
              cases writable : descriptor.writable with
              | false => simpa [writable] using And.intro valid machine.continuesFrom_refl
              | true =>
                  cases receiver with
                  | primitive receiver => simp [writable]; exact ⟨valid, machine.continuesFrom_refl⟩
                  | object receiverRef =>
                      simp only [writable, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
                      apply completeDefinition_result_preservesWellFormed machine _ valid
                      intro success next defined
                      exact defineValue_preserves machine.heap next receiverRef key value success
                        (Machine.wellFormed_heap machine valid) defined
          | accessor descriptor =>
              cases setterResult : descriptor.set with
              | none => simpa [setterResult] using And.intro valid machine.continuesFrom_refl
              | some setter =>
                  simp only [setterResult]
                  cases callResult : Call.call hook setter receiver #[value] machine with
                  | done completion next =>
                      have nextPreserved :=
                        Call.call_preservesWellFormed hook setter receiver #[value] hookPreserves
                          machine valid
                      rw [callResult] at nextPreserved
                      cases completion <;> exact nextPreserved
                  | exhausted next | fault fault next =>
                      simpa [callResult] using
                        Call.call_preservesWellFormed hook setter receiver #[value] hookPreserves
                          machine valid

/-- Ordinary `Set` validates every abrupt value while its Boolean normal result needs no heap
reference. -/
theorem set_preservesResults (hook : BodyHook P) (ref : RefId) (key : PropertyKey)
    (value receiver : Value) (hookPreserves : BodyHookPreservesWellFormed hook) :
    JSM.PreservesResults (fun _ _ => True) (set hook ref key value receiver) := by
  refine ⟨set_preservesWellFormed hook ref key value receiver hookPreserves, ?_⟩
  intro machine valid
  unfold set
  cases lookup : Prototype.lookup machine.heap ref key with
  | error fault => trivial
  | ok result =>
      cases result with
      | none =>
          cases receiver with
          | primitive primitive => simp [lookup, RunResult.CompletionValuesValid]
          | object receiverRef =>
              simpa [lookup] using
                (completeDefinition_valuesValid
                  (defineValue machine.heap receiverRef key value) machine)
      | some found =>
          rcases found with ⟨owner, descriptor⟩
          cases descriptor with
          | data descriptor =>
              cases writable : descriptor.writable with
              | false => simp [lookup, writable, RunResult.CompletionValuesValid]
              | true =>
                  cases receiver with
                  | primitive primitive => simp [lookup, writable, RunResult.CompletionValuesValid]
                  | object receiverRef =>
                      simpa [lookup, writable] using
                        (completeDefinition_valuesValid
                          (defineValue machine.heap receiverRef key value) machine)
          | accessor descriptor =>
              cases setter : descriptor.set with
              | none => simp [lookup, setter, RunResult.CompletionValuesValid]
              | some setterRef =>
                  cases callResult : Call.call hook setterRef receiver #[value] machine with
                  | done completion next =>
                      have valuesValid :=
                        (Call.call_preservesResults hook setterRef receiver #[value] hookPreserves).2
                          machine valid
                      rw [callResult] at valuesValid
                      cases completion with
                      | thrown thrown => simpa [lookup, setter, callResult] using valuesValid
                      | normal result | returned result | «break» result | «continue» result =>
                          simp [lookup, setter, callResult, RunResult.CompletionValuesValid]
                  | exhausted next | fault fault next =>
                      simp [lookup, setter, callResult, RunResult.CompletionValuesValid]

/-- Strict assignment turns an ordinary `false` rejection into a modeled TypeError throw. -/
def setStrict (hook : BodyHook P) (ref : RefId) (key : PropertyKey)
    (value receiver : Value) : JSM P Unit := do
  if ← set hook ref key value receiver then pure ()
  else JSM.throwJS (typeError "assignment rejected")

/-- Strict `Set` preserves complete machine validity, including the false-to-TypeError branch. -/
theorem setStrict_preservesWellFormed (hook : BodyHook P) (ref : RefId) (key : PropertyKey)
    (value receiver : Value) (hookPreserves : BodyHookPreservesWellFormed hook) :
    JSM.PreservesWellFormed (setStrict hook ref key value receiver) := by
  unfold setStrict
  apply JSM.bind_preservesWellFormed
  · exact set_preservesWellFormed hook ref key value receiver hookPreserves
  · intro success
    cases success with
    | false => exact JSM.throwJS_preservesWellFormed (typeError "assignment rejected")
    | true => exact JSM.pure_preservesWellFormed ()

/-- Strict `Set` preserves continuity and validates its rejection TypeError. -/
theorem setStrict_preservesResults (hook : BodyHook P) (ref : RefId) (key : PropertyKey)
    (value receiver : Value) (hookPreserves : BodyHookPreservesWellFormed hook) :
    JSM.PreservesResults (fun _ _ => True) (setStrict hook ref key value receiver) := by
  unfold setStrict
  apply JSM.bind_preservesResults
  · exact set_preservesResults hook ref key value receiver hookPreserves
  · intro success machine valid successValid
    cases success with
    | false =>
        exact ⟨JSM.throwJS_preservesWellFormed (typeError "assignment rejected") machine valid, rfl⟩
    | true =>
        exact ⟨JSM.pure_preservesWellFormed () machine valid, trivial⟩

end ObjectAccess
end TSLean.JS
