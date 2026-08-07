import TSLean.JS.AbstractEquality
import TSLean.JS.Copy
import TSLean.JS.HasInstance
import TSLean.JS.Iterator
import TSLean.JS.Typeof
import TSLean.JS.Oracle.Canonical
import TSLean.JS.Oracle.GraphFixture

namespace TSLean.JS.Oracle

private def invalid (request : Request) (code message : String) : Except ProtocolError α :=
  .error { id := some request.id, code, message }

private def argument (graph : MaterializedGraph) (index : Nat) : Except String Value :=
  match graph.arguments[index]? with
  | some value => pure value
  | none => throw s!"missing graph argument {index}"

private def names (graph : MaterializedGraph) : Array String := graph.symbols.map (·.2)

private def valueJson (graph : MaterializedGraph) (value : Value) : Lean.Json := graphValueDatum graph.symbols value
private def primitiveJson (graph : MaterializedGraph) (value : Primitive) : Lean.Json := graphPrimitiveDatum graph.symbols value
private def boolJson (graph : MaterializedGraph) (value : Bool) : Lean.Json := primitiveDatum (names graph) (.boolean value)
private def numberJson (graph : MaterializedGraph) (value : JSNumber) : Lean.Json := primitiveDatum (names graph) (.number value)
private def stringJson (graph : MaterializedGraph) (value : JSString) : Lean.Json := primitiveDatum (names graph) (.string value)

private def familyPrototype (graph : MaterializedGraph) (family : String) : Except String RefId := do
  let intrinsics ← match graph.machine.intrinsics with
    | some intrinsics => pure intrinsics
    | none => throw "realm is not initialized"
  match family with
  | "boolean" => pure intrinsics.booleanPrototype
  | "number" => pure intrinsics.numberPrototype
  | "string" => pure intrinsics.stringPrototype
  | "bigint" => pure intrinsics.bigintPrototype
  | "symbol" => pure intrinsics.symbolPrototype
  | _ => throw s!"unknown wrapper family: {family}"

private def familyArgument (graph : MaterializedGraph) : Except String String := do
  match ← argument graph 0 with
  | .primitive (.string family) =>
      match family.toLeanString? with
      | some family => pure family
      | none => throw "invalid wrapper family string"
  | _ => throw "wrapper family must be a string"

private def prototypeIs (value : Value) (expected : RefId) : JSM oraclePlatform Bool := do
  let ref ← AbstractOperations.toObject value
  let heap ← JSM.readHeap
  match heap.get? ref with
  | .ok object => pure (object.prototype = some expected)
  | .error fault => JSM.fail (.runtime (.heap fault))

private def ownString (hook : BodyHook oraclePlatform) (ref : RefId) (index : String) : JSM oraclePlatform JSString := do
  match ← ObjectAccess.get hook ref (.string (JSString.ofLeanString index)) (.object ref) with
  | .primitive (.string value) => pure value
  | _ => ObjectAccess.throwTypeError "expected string property"

private def assignString (graph : MaterializedGraph) : JSM oraclePlatform JSString := do
  let target := graph.arguments[0]?.getD (.primitive .undefined)
  let source := graph.arguments[1]?.getD (.primitive .undefined)
  match ← Copy.objectAssign graph.bodyHook target [source] with
  | .object ref => pure ((← ownString graph.bodyHook ref "0").append (← ownString graph.bodyHook ref "1"))
  | _ => ObjectAccess.throwTypeError "assign target was not an object"

private def spreadString (graph : MaterializedGraph) : JSM oraclePlatform JSString := do
  let source := graph.arguments[0]?.getD (.primitive .undefined)
  let ref ← Copy.objectSpread graph.bodyHook [source]
  pure ((← ownString graph.bodyHook ref "0").append (← ownString graph.bodyHook ref "1"))

private def spreadCount (graph : MaterializedGraph) : JSM oraclePlatform JSNumber := do
  let sources := graph.arguments.toList
  let ref ← Copy.objectSpread graph.bodyHook sources
  let heap ← JSM.readHeap
  match heap.ownPropertyKeys ref with
  | .ok keys => pure (JSNumber.parse (JSString.ofLeanString keys.length.repr))
  | .error fault => JSM.fail (.runtime (.heap fault))

private def callValue (graph : MaterializedGraph) (function receiver : Value)
    (arguments : Array Value := #[]) : JSM oraclePlatform Value :=
  match function with
  | .object ref => Call.call graph.bodyHook ref receiver arguments
  | .primitive _ => ObjectAccess.throwTypeError "value is not callable"

private def setIndex (graph : MaterializedGraph) (target : Value) (index : Nat) (value : Value) :
    JSM oraclePlatform Unit :=
  match target with
  | .object ref => ObjectAccess.setStrict graph.bodyHook ref
      (.string (PropertyKey.arrayIndexString index)) value target
  | .primitive _ => ObjectAccess.throwTypeError "index target is not an object"

private def liveIteration (graph : MaterializedGraph) (target : Value) : JSM oraclePlatform JSString := do
  let ref ← match target with
    | .object ref => pure ref
    | _ => ObjectAccess.throwTypeError "iterator target is not an object"
  let iterator ← Iterator.arrayValues ref
  let first ← Iterator.next graph.bodyHook iterator
  setIndex graph target 1 (.primitive (.string (JSString.ofLeanString "b")))
  let second ← Iterator.next graph.bodyHook iterator
  let text : Value → JSString
    | .primitive (.string value) => value
    | _ => JSString.ofLeanString "?"
  pure ((text first.value).append (text second.value))

private def observeGraph (graph : MaterializedGraph) (encode : α → Lean.Json)
    (action : JSM oraclePlatform α) : Except String Lean.Json :=
  graphMachineObservation graph encode (action graph.machine)

private def requestObservation (request : Request) (graph : MaterializedGraph)
    (encode : α → Lean.Json) (action : JSM oraclePlatform α) : Except ProtocolError Lean.Json :=
  observeGraph graph encode action |>.mapError fun message =>
    { id := some request.id, code := "model-failure", message }

private def abstractObservation (request : Request) (graph : MaterializedGraph) : Except ProtocolError Lean.Json := do
  let hook := graph.bodyHook
  let machine := graph.machine
  let left ← (argument graph 0).mapError fun message => { id := some request.id, code := "invalid-fixture", message }
  let right? := argument graph 1
  let right := graph.arguments[1]?.getD (.primitive .undefined)
  let third := graph.arguments[2]?.getD (.primitive .undefined)
  let shortCircuitResult := !left.toBoolean && right.toBoolean
  let truthinessResult := strictEqual (if left.toBoolean then left else right) left &&
    strictEqual (if left.toBoolean then third else left) third
  match request.operation with
  | "value-add" => requestObservation request graph (valueJson graph) (AbstractEquality.add hook left (← right?.mapError fun message =>
      { id := some request.id, code := "invalid-fixture", message }))
  | "value-number" => requestObservation request graph (numberJson graph) (AbstractOperations.toNumber hook left)
  | "value-string" => requestObservation request graph (stringJson graph) (AbstractOperations.toString hook left)
  | "value-loose" => requestObservation request graph (boolJson graph) (AbstractEquality.looseEqual hook left (← right?.mapError fun message =>
      { id := some request.id, code := "invalid-fixture", message }))
  | "value-strict" => requestObservation request graph (boolJson graph) (JSM.pure (strictEqual left right))
  | "value-identity" => requestObservation request graph (valueJson graph) (JSM.pure left)
  | "throw-value" => requestObservation request graph (valueJson graph) (JSM.throwJS left)
  | "call-with-argument" => requestObservation request graph (valueJson graph) (callValue graph left (.primitive .undefined) #[right])
  | "utf16-fields" => requestObservation request graph (boolJson graph) (do
      let _ ← callValue graph left (.primitive .undefined)
      let _ ← callValue graph right (.primitive .undefined) #[third]
      pure true)
  | "logical-or" => requestObservation request graph (valueJson graph) (JSM.pure (if left.toBoolean then left else right))
  | "short-circuit-assignment" => requestObservation request graph (boolJson graph) (JSM.pure shortCircuitResult)
  | "truthiness-empty-array" => requestObservation request graph (boolJson graph) (JSM.pure truthinessResult)
  | "while-call-once" => requestObservation request graph (numberJson graph) (do
      let result ← callValue graph right (.primitive .undefined) #[left]
      pure (if result.toBoolean then JSNumber.one else JSNumber.positiveZero))
  | "finally-return" => requestObservation request graph (valueJson graph) (JSM.pure right)
  | "finally-order" => requestObservation request graph (valueJson graph) (do
      let prior ← callValue graph left (.primitive .undefined)
      let _ ← callValue graph right (.primitive .undefined)
      pure prior)
  | "iterate-live" => requestObservation request graph (stringJson graph) (liveIteration graph left)
  | "spread-overwrite" => requestObservation request graph (valueJson graph) (do
      let copied ← Copy.objectSpread graph.bodyHook [left, right]
      ObjectAccess.get graph.bodyHook copied (.string (JSString.ofLeanString "a")) (.object copied))
  | "typeof-string-check" =>
      let tag ← left.typeof graph.machine.heap |>.mapError fun _ =>
        { id := some request.id, code := "model-failure", message := "typeof failed" }
      requestObservation request graph (boolJson graph) (JSM.pure (decide (tag = .string)))
  | "symbol-key-for" => requestObservation request graph (valueJson graph) (JSM.pure (match left with
      | .primitive (.symbol (.allocated id)) =>
          match graph.symbols[id]? with
          | some ("registered", identity) => .primitive (.string (JSString.ofLeanString identity))
          | _ => .primitive .undefined
      | _ => .primitive .undefined))
  | "value-lt" => requestObservation request graph (boolJson graph) (AbstractEquality.lessThan hook left (← right?.mapError fun message =>
      { id := some request.id, code := "invalid-fixture", message }))
  | "value-le" => requestObservation request graph (boolJson graph) (AbstractEquality.lessThanOrEqual hook left (← right?.mapError fun message =>
      { id := some request.id, code := "invalid-fixture", message }))
  | "value-gt" => requestObservation request graph (boolJson graph) (AbstractEquality.greaterThan hook left (← right?.mapError fun message =>
      { id := some request.id, code := "invalid-fixture", message }))
  | "value-ge" => requestObservation request graph (boolJson graph) (AbstractEquality.greaterThanOrEqual hook left (← right?.mapError fun message =>
      { id := some request.id, code := "invalid-fixture", message }))
  | "value-instanceof" => requestObservation request graph (boolJson graph) (Instanceof.instanceofOperator hook left (← right?.mapError fun message =>
      { id := some request.id, code := "invalid-fixture", message }))
  | "box-number" => requestObservation request graph (numberJson graph) (do
      let ref ← AbstractOperations.toObject left
      AbstractOperations.toNumber hook (.object ref))
  | "box-add" => requestObservation request graph (valueJson graph) (do
      let ref ← AbstractOperations.toObject left
      AbstractEquality.add hook (.object ref) right)
  | "box-string" => requestObservation request graph (stringJson graph) (do
      let ref ← AbstractOperations.toObject left
      AbstractOperations.toString hook (.object ref))
  | "box-loose" => requestObservation request graph (boolJson graph) (do
      let ref ← AbstractOperations.toObject left
      AbstractEquality.looseEqual hook (.object ref) right)
  | "box-valueof" => requestObservation request graph (primitiveJson graph) (do
      let ref ← AbstractOperations.toObject left
      AbstractOperations.toPrimitive hook (.object ref) .number)
  | "box-object" => requestObservation request graph (valueJson graph) (do
      let ref ← AbstractOperations.toObject left
      pure (.object ref))
  | "box-prototype-is" =>
      let family ← familyArgument graph |>.mapError fun message => { id := some request.id, code := "invalid-fixture", message }
      let expected ← familyPrototype graph family |>.mapError fun message => { id := some request.id, code := "invalid-fixture", message }
      let value ← argument graph 1 |>.mapError fun message => { id := some request.id, code := "invalid-fixture", message }
      requestObservation request graph (boolJson graph) (prototypeIs value expected)
  | "assign-primitive-prototype-is" =>
      let expected ← familyPrototype graph "boolean" |>.mapError fun message => { id := some request.id, code := "invalid-fixture", message }
      requestObservation request graph (boolJson graph) (do
        match ← Copy.objectAssign hook left [] with
        | .object ref =>
            let heap ← JSM.readHeap
            match heap.get? ref with
            | .ok object => pure (decide (object.prototype = some expected))
            | .error fault => JSM.fail (.runtime (.heap fault))
        | _ => pure false)
  | "assign-string" => requestObservation request graph (stringJson graph) (assignString graph)
  | "spread-string" => requestObservation request graph (stringJson graph) (spreadString graph)
  | "spread-count" => requestObservation request graph (numberJson graph) (spreadCount graph)
  | "intrinsic-valueof" | "intrinsic-tostring" =>
      let family ← familyArgument graph |>.mapError fun message => { id := some request.id, code := "invalid-fixture", message }
      let prototype ← familyPrototype graph family |>.mapError fun message => { id := some request.id, code := "invalid-fixture", message }
      requestObservation request graph (primitiveJson graph) (AbstractOperations.toPrimitive hook (.object prototype)
        (if request.operation = "intrinsic-tostring" then .string else .number))
  | "mutate-intrinsic-prototype" =>
      let expected ← familyPrototype graph "boolean" |>.mapError fun message => { id := some request.id, code := "invalid-fixture", message }
      let heap ← match machine.heap.setPrototypeOf expected none with
        | .ok (true, heap) => pure heap
        | _ => invalid request "model-failure" "intrinsic prototype mutation failed"
      observeGraph { graph with machine := machine.setHeap heap } (boolJson graph)
        (prototypeIs (.primitive (.boolean true)) expected)
        |>.mapError fun message => { id := some request.id, code := "model-failure", message }
  | "mutate-wrapper-prototype" => requestObservation request graph (boolJson graph) (do
      let ref ← AbstractOperations.toObject left
      let heap ← JSM.readHeap
      match heap.setPrototypeOf ref none with
      | .ok (true, heap) =>
          JSM.modifyHeap (fun _ => heap)
          pure true
      | .ok (false, _) => pure false
      | .error fault => JSM.fail (.runtime (.heap fault)))
  | _ => invalid request "unknown-operation" s!"unknown abstract operation: {request.operation}"

def evaluateAbstract (request : Request) : Except ProtocolError Lean.Json := do
  match request.fixtures with
  | #[fixture] =>
      let graph ← materializeGraph fixture |>.mapError fun message =>
        { id := some request.id, code := "invalid-fixture", message }
      abstractObservation request graph
  | _ => invalid request "invalid-arity" "abstract operations require one graph fixture"

end TSLean.JS.Oracle
