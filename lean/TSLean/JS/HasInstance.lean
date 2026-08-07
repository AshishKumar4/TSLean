import TSLean.JS.AbstractOperations

namespace TSLean.JS

namespace Instanceof

private def typeError (message : String) : Value :=
  .primitive (.string (JSString.ofLeanString ("TypeError: " ++ message)))

private def heapFault (fault : HeapFault) : ModelFault := .runtime (.heap fault)

/-- Bounded prototype reachability by reference identity. -/
def reachesPrototype (heap : Heap) (target : RefId) : Nat → RefId → Except HeapFault Bool
  | 0, _ => .error .cycleOrFuelExhausted
  | fuel + 1, ref => do
      let object ← heap.get? ref
      match object.prototype with
      | none => pure false
      | some parent =>
          if parent = target then pure true
          else reachesPrototype heap target fuel parent

/-- ECMAScript ordinary `instanceof` for represented ordinary function objects. -/
def ordinaryHasInstance (hook : BodyHook P) (constructor : RefId) (value : Value) : JSM P Bool :=
  fun machine =>
    match machine.heap.isCallable constructor with
    | .error fault => .fault (heapFault fault) machine
    | .ok false => .done (.normal false) machine
    | .ok true =>
        match value with
        | .primitive _ => .done (.normal false) machine
        | .object object =>
            match machine.heap.get? object with
            | .error fault => .fault (heapFault fault) machine
            | .ok _ =>
                match ObjectAccess.get hook constructor
                    (.string (JSString.ofLeanString "prototype")) (.object constructor) machine with
                | .done (.normal (.object prototype)) next =>
                    match reachesPrototype next.heap prototype (next.heap.size + 1) object with
                    | .ok result => .done (.normal result) next
                    | .error fault => .fault (heapFault fault) next
                | .done (.normal (.primitive _)) next =>
                    .done (.thrown (typeError "constructor prototype is not an object")) next
                | .done (.thrown thrown) next => .done (.thrown thrown) next
                | .done (.returned _) next | .done (.break _) next | .done (.continue _) next =>
                    .fault (.runtime .escapingFunctionControl) next
                | .exhausted next => .exhausted next
                | .fault fault next => .fault fault next

/-- Built-in `Function.prototype[Symbol.hasInstance]`, excluding unrepresented bound exotica. -/
def functionPrototypeHasInstance (hook : BodyHook P) (thisValue value : Value) : JSM P Bool :=
  match thisValue with
  | .object constructor => ordinaryHasInstance hook constructor value
  | .primitive _ => pure false

/-- ECMAScript `instanceof`, including observable custom `Symbol.hasInstance` dispatch. -/
def instanceofOperator (hook : BodyHook P) (value constructor : Value) : JSM P Bool :=
  match constructor with
  | .primitive _ => ObjectAccess.throwTypeError "right-hand side of instanceof is not an object"
  | .object constructorRef => do
      match ← AbstractOperations.getMethod hook constructorRef (.symbol (.wellKnown .hasInstance)) with
      | some method =>
          let result ← Call.call hook method constructor #[value]
          pure result.toBoolean
      | none =>
          let heap ← JSM.readHeap
          match heap.isCallable constructorRef with
          | .error fault => JSM.fail (heapFault fault)
          | .ok false => ObjectAccess.throwTypeError "right-hand side is not callable"
          | .ok true => ordinaryHasInstance hook constructorRef value

end Instanceof
end TSLean.JS
