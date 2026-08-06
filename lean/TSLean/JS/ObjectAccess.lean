import TSLean.JS.Call
import TSLean.JS.Prototype

namespace TSLean.JS

namespace ObjectAccess

private def undefined : Value := .primitive .undefined

private def typeError (message : String) : Value :=
  .primitive (.string (JSString.ofLeanString ("TypeError: " ++ message)))

private def heapFault (fault : HeapFault) : ModelFault := .runtime (.heap fault)

private def prototypeFault : PrototypeFault → ModelFault
  | .heap fault => heapFault fault
  | .cycleOrFuelExhausted => heapFault .cycleOrFuelExhausted

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

private def defineFault : DefinePropertyFault → ModelFault
  | .heap fault => heapFault fault
  | .syntax _ => heapFault .cycleOrFuelExhausted
  | .invalidValueRef ref => heapFault (.invalidRef ref)
  | .invalidAccessor ref => heapFault (.invalidRef ref)
  | .nonCallableAccessor ref => heapFault (.invalidRef ref)

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
              match defineValue machine.heap receiverRef key value with
              | .error fault => .fault (defineFault fault) machine
              | .ok (success, heap) => .done (.normal success) (machine.setHeap heap)
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
            match defineValue machine.heap receiverRef key value with
            | .error fault => .fault (defineFault fault) machine
            | .ok (success, heap) => .done (.normal success) (machine.setHeap heap)

/-- Strict assignment turns an ordinary `false` rejection into a modeled TypeError throw. -/
def setStrict (hook : BodyHook P) (ref : RefId) (key : PropertyKey)
    (value receiver : Value) : JSM P Unit := do
  if ← set hook ref key value receiver then pure ()
  else JSM.throwJS (typeError "assignment rejected")

end ObjectAccess
end TSLean.JS
