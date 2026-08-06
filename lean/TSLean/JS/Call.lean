import TSLean.JS.Monad

namespace TSLean.JS

/-- Evaluator boundary for executing a function body. Normal completion means fallthrough;
explicit JavaScript return is represented by `Completion.returned`. -/
abbrev BodyHook (P : Platform) := RefId → Value → Array Value → JSM P Unit

namespace Call

private def undefined : Value := .primitive .undefined

private def typeError (message : String) : Value :=
  .primitive (.string (JSString.ofLeanString ("TypeError: " ++ message)))

private def heapFault (fault : HeapFault) : ModelFault := .runtime (.heap fault)

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
        else normalizeBody undefined id (hook ref receiver arguments) machine

end Call

end TSLean.JS
