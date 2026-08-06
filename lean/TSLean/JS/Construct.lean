import TSLean.JS.Function

namespace TSLean.JS

namespace Construct

private def typeError (message : String) : Value :=
  .primitive (.string (JSString.ofLeanString ("TypeError: " ++ message)))

private def heapFault (fault : HeapFault) : ModelFault := .runtime (.heap fault)

private def invokeWithPrototype (hook : BodyHook P) (constructor prototype : RefId)
    (arguments : Array Value) : JSM P Value := fun machine =>
  match machine.heap.allocate (some prototype) with
  | .error fault => .fault (heapFault fault) machine
  | .ok (receiver, heap) =>
      let withReceiver := machine.setHeap heap
      Call.normalizeBody (.object receiver) (Function.constructorResult receiver)
        (hook constructor (.object receiver) arguments) withReceiver

/-- Complete supported constructor dispatch. Derived constructors are rejected explicitly until
`super()` and uninitialized-`this` semantics are modeled. -/
def construct (hook : BodyHook P) (constructor fallbackObjectPrototype : RefId)
    (arguments : Array Value) : JSM P Value := fun machine =>
  match machine.heap.functionSlots? constructor with
  | .error fault => .fault (heapFault fault) machine
  | .ok none => .done (.thrown (typeError "value is not a constructor")) machine
  | .ok (some slots) =>
      if !slots.constructible then .done (.thrown (typeError "value is not a constructor")) machine
      else if slots.constructorMode = .derived then
        .fault (.runtime (.unsupportedDerivedConstruction constructor)) machine
      else
        match ObjectAccess.get hook constructor
            (.string (JSString.ofLeanString "prototype")) (.object constructor) machine with
        | .done (.normal (.object prototype)) afterPrototype =>
            invokeWithPrototype hook constructor prototype arguments afterPrototype
        | .done (.normal (.primitive _)) afterPrototype =>
            match afterPrototype.heap.get? fallbackObjectPrototype with
            | .error fault => .fault (heapFault fault) afterPrototype
            | .ok _ => invokeWithPrototype hook constructor fallbackObjectPrototype arguments afterPrototype
        | .done (.thrown value) next => .done (.thrown value) next
        | .done (.returned _) next | .done (.break _) next | .done (.continue _) next =>
            .fault (.runtime .escapingFunctionControl) next
        | .exhausted next => .exhausted next
        | .fault fault next => .fault fault next

end Construct
end TSLean.JS
