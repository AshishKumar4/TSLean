import TSLean.JS.Monad

namespace TSLean.JS

/-- Evaluator boundary for executing a function body. Normal completion means fallthrough;
explicit JavaScript return is represented by `Completion.returned`. -/
abbrev BodyHook (P : Platform) := RefId → Value → Array Value → JSM P Unit

/-- Machine-local authority required before entering an evaluator body. -/
def BodyHookInputsValid (machine : Machine P) (ref : RefId) (receiver : Value)
    (arguments : Array Value) : Prop :=
  (∃ slots, machine.heap.functionSlots? ref = .ok (some slots)) ∧
  machine.heap.valueValid receiver = true ∧
  arguments.toList.all machine.heap.valueValid = true

/-- Every valid evaluator entry preserves execution identity and validates escaping values. -/
def BodyHookPreservesWellFormed (hook : BodyHook P) : Prop :=
  ∀ ref receiver arguments,
    JSM.PreservesResultsWhen (fun machine => BodyHookInputsValid machine ref receiver arguments)
      (fun _ _ => True) (hook ref receiver arguments)

namespace Call

private def undefined : Value := .primitive .undefined

private def typeError (message : String) : Value :=
  .primitive (.string (JSString.ofLeanString ("TypeError: " ++ message)))

private def heapFault (fault : HeapFault) : ModelFault := .runtime (.heap fault)

private def invalidValueRef? (heap : Heap) : Value → Option RefId
  | .primitive _ => none
  | .object ref => if heap.valueValid (.object ref) then none else some ref

private def firstInvalidArgument? (heap : Heap) : List Value → Option RefId
  | [] => none
  | value :: rest => invalidValueRef? heap value <|> firstInvalidArgument? heap rest

private def firstInvalidCallValue? (heap : Heap) (receiver : Value) (arguments : Array Value) :
    Option RefId :=
  invalidValueRef? heap receiver <|> firstInvalidArgument? heap arguments.toList

private theorem invalidValueRef?_none_iff (heap : Heap) (value : Value) :
    invalidValueRef? heap value = none ↔ heap.valueValid value = true := by
  cases value with
  | primitive value => simp [invalidValueRef?, Heap.valueValid]
  | object ref =>
      unfold invalidValueRef?
      cases valid : heap.valueValid (.object ref) <;> simp [valid]

private theorem firstInvalidArgument?_none_iff (heap : Heap) (values : List Value) :
    firstInvalidArgument? heap values = none ↔ values.all heap.valueValid = true := by
  induction values with
  | nil => simp [firstInvalidArgument?]
  | cons value rest ih =>
      cases value with
      | primitive value =>
          simp [firstInvalidArgument?, invalidValueRef?, Heap.valueValid, ih]
      | object ref =>
          by_cases inBounds : ref.value < heap.size
          · simp [firstInvalidArgument?, invalidValueRef?, Heap.valueValid, inBounds, ih]
          · simp [firstInvalidArgument?, invalidValueRef?, Heap.valueValid, inBounds]

private theorem firstInvalidCallValue?_none (heap : Heap) (receiver : Value)
    (arguments : Array Value) (valid : firstInvalidCallValue? heap receiver arguments = none) :
    heap.valueValid receiver = true ∧ arguments.toList.all heap.valueValid = true := by
  unfold firstInvalidCallValue? at valid
  cases receiverInvalid : invalidValueRef? heap receiver with
  | some ref => simp [receiverInvalid] at valid
  | none =>
      simp [receiverInvalid] at valid
      exact ⟨(invalidValueRef?_none_iff heap receiver).mp receiverInvalid,
        (firstInvalidArgument?_none_iff heap arguments.toList).mp valid⟩

private def normalValue (value : Value) : JSM P Value := fun machine =>
  match value with
  | .primitive _ => .done (.normal value) machine
  | .object ref =>
      if machine.heap.valueValid value then .done (.normal value) machine
      else .fault (.runtime (.danglingEscapingValue ref)) machine

/-- Normalizes evaluator body completion, validating every escaping JavaScript value against the
heap committed by the body. `onReturn` supplies call or construct return semantics. -/
def normalizeBody (fallthrough : Value) (onReturn : Value → Value)
    (body : JSM P Unit) : JSM P Value := fun machine =>
  match body machine with
  | .done (.normal ()) next => normalValue fallthrough next
  | .done (.returned value) next =>
      normalValue (onReturn value) next
  | .done (.thrown value) next =>
      match value with
      | .primitive _ => .done (.thrown value) next
      | .object ref =>
          if next.heap.valueValid value then .done (.thrown value) next
          else .fault (.runtime (.danglingEscapingValue ref)) next
  | .done (.break _) next | .done (.continue _) next =>
      .fault (.runtime .escapingFunctionControl) next
  | .exhausted next => .exhausted next
  | .fault fault next => .fault fault next

/-- Completion normalization preserves an actual body run. -/
theorem normalizeBody_machinePreserved (fallthrough : Value) (onReturn : Value → Value)
    (body : JSM P Unit) (machine : Machine P)
    (preserved : (body machine).MachinePreserved machine) :
    (normalizeBody fallthrough onReturn body machine).MachinePreserved machine := by
  unfold normalizeBody
  cases result : body machine with
  | done completion next =>
      have nextPreserved := preserved
      rw [result] at nextPreserved
      cases completion with
      | normal resultUnit =>
          cases resultUnit
          cases fallthrough with
          | primitive value => exact nextPreserved
          | object ref => simp only [normalValue]; split <;> exact nextPreserved
      | returned value =>
          cases returned : onReturn value with
          | primitive value => simp [normalValue, returned]; exact nextPreserved
          | object ref => simp only [normalValue, returned]; split <;> exact nextPreserved
      | thrown value =>
          cases value with
          | primitive value => exact nextPreserved
          | object ref => simp only; split <;> exact nextPreserved
      | «break» label | «continue» label => exact nextPreserved
  | exhausted next | fault fault next => simpa [result] using preserved

/-- Completion normalization preserves every machine produced by its body. -/
theorem normalizeBody_preservesWellFormed (fallthrough : Value) (onReturn : Value → Value)
    (body : JSM P Unit) (preserves : JSM.PreservesWellFormed body) :
    JSM.PreservesWellFormed (normalizeBody fallthrough onReturn body) := by
  intro machine valid
  exact normalizeBody_machinePreserved fallthrough onReturn body machine
    (preserves machine valid)

/-- Completion normalization validates every normal, returned, or thrown value that escapes. -/
theorem normalizeBody_resultsValid (fallthrough : Value) (onReturn : Value → Value)
    (body : JSM P Unit) (machine : Machine P) :
    (normalizeBody fallthrough onReturn body machine).CompletionValuesValid
      (fun value final => final.heap.valueValid value = true) := by
  unfold normalizeBody
  cases body machine with
  | done completion next =>
      cases completion with
      | normal resultUnit =>
          cases resultUnit
          cases fallthrough with
          | primitive value => rfl
          | object ref =>
              by_cases inBounds : ref.value < next.heap.size <;>
                simp [normalValue, Heap.valueValid, RunResult.CompletionValuesValid, inBounds]
      | returned value =>
          cases returned : onReturn value with
          | primitive result =>
              simp [normalValue, returned, Heap.valueValid, RunResult.CompletionValuesValid]
          | object ref =>
              by_cases inBounds : ref.value < next.heap.size <;>
                simp [normalValue, returned, Heap.valueValid, RunResult.CompletionValuesValid,
                  inBounds]
      | thrown value =>
          cases value with
          | primitive value => rfl
          | object ref =>
              by_cases inBounds : ref.value < next.heap.size <;>
                simp [Heap.valueValid, RunResult.CompletionValuesValid, inBounds]
      | «break» label | «continue» label => trivial
  | exhausted next | fault fault next => trivial

/-- Checked ordinary call dispatch. Class constructors retain `[[Call]]` identity for `typeof`
and accessors, but ordinary invocation rejects them before evaluator entry. -/
def call (hook : BodyHook P) (ref : RefId) (thisValue : Value) (arguments : Array Value) :
    JSM P Value := fun machine =>
  match machine.heap.functionSlots? ref with
  | .error fault => .fault (heapFault fault) machine
  | .ok none => .done (.thrown (typeError "value is not callable")) machine
  | .ok (some slots) =>
      if slots.kind = .classConstructor then
        .done (.thrown (typeError "class constructor requires new")) machine
      else
        let receiver := match slots.kind, slots.lexicalThis with
          | .arrow, some lexicalThis => lexicalThis
          | _, _ => thisValue
        if slots.kind = .arrow && slots.lexicalThis.isNone then
          .fault (heapFault .invalidFunctionMetadata) machine
        else
          match firstInvalidCallValue? machine.heap receiver arguments with
          | some invalid => .fault (.runtime (.danglingEscapingValue invalid)) machine
          | none => normalizeBody undefined id (hook ref receiver arguments) machine

/-- Checked call dispatch preserves complete machine validity under a preserving evaluator hook. -/
theorem call_preservesWellFormed (hook : BodyHook P) (ref : RefId) (thisValue : Value)
    (arguments : Array Value) (hookPreserves : BodyHookPreservesWellFormed hook) :
    JSM.PreservesWellFormed (call hook ref thisValue arguments) := by
  intro machine valid
  unfold call
  cases slotsResult : machine.heap.functionSlots? ref with
  | error fault => exact ⟨valid, machine.continuesFrom_refl⟩
  | ok slots =>
      cases slots with
      | none => exact ⟨valid, machine.continuesFrom_refl⟩
      | some slots =>
          simp_all
          split <;> rename_i branch
          · exact ⟨valid, machine.continuesFrom_refl⟩
          · split
            · exact ⟨valid, machine.continuesFrom_refl⟩
            · let receiver := match slots.kind, slots.lexicalThis with
                | .arrow, some lexicalThis => lexicalThis
                | _, _ => thisValue
              cases inputs : firstInvalidCallValue? machine.heap receiver arguments with
              | some invalid => exact ⟨valid, machine.continuesFrom_refl⟩
              | none =>
                  apply normalizeBody_machinePreserved
                  exact (hookPreserves ref receiver arguments).1 machine valid
                    ⟨⟨slots, slotsResult⟩,
                      firstInvalidCallValue?_none machine.heap receiver arguments inputs⟩

/-- Checked call dispatch preserves continuity and validates every normal or thrown result. -/
theorem call_preservesResults (hook : BodyHook P) (ref : RefId) (thisValue : Value)
    (arguments : Array Value) (hookPreserves : BodyHookPreservesWellFormed hook) :
    JSM.PreservesResults (fun value machine => machine.heap.valueValid value = true)
      (call hook ref thisValue arguments) := by
  refine ⟨call_preservesWellFormed hook ref thisValue arguments hookPreserves, ?_⟩
  intro machine valid
  unfold call
  cases slotsResult : machine.heap.functionSlots? ref with
  | error fault => trivial
  | ok slots =>
      cases slots with
      | none => rfl
      | some slots =>
          simp_all
          split
          · rfl
          · split
            · trivial
            · let receiver := match slots.kind, slots.lexicalThis with
                | .arrow, some lexicalThis => lexicalThis
                | _, _ => thisValue
              cases inputs : firstInvalidCallValue? machine.heap receiver arguments with
              | some invalid => trivial
              | none =>
                  simpa [receiver, inputs] using
                    normalizeBody_resultsValid undefined id (hook ref receiver arguments) machine

end Call

end TSLean.JS
