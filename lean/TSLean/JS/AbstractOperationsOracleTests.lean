import TSLean.JS.AbstractEquality
import TSLean.JS.Copy
import TSLean.JS.HasInstance
import TSLean.JS.RealmTestSupportTests

namespace TSLean.JS.AbstractOperationsOracleTests

private def platform : Platform := ScriptedPlatform.make {
  times := #[], randoms := #[], fetches := #[]
}

private def key (value : String) : PropertyKey := .string (JSString.ofLeanString value)
private def text (value : String) : Value := .primitive (.string (JSString.ofLeanString value))
private def bigint (value : Int) : Value := .primitive (.bigint value)
private def undefined : Value := .primitive .undefined
private def fallthrough : BodyHook platform := fun _ _ _ => pure ()

private def allocateObject (heap : Heap) (prototype : Option RefId := none) : IO (RefId × Heap) :=
  match heap.allocate prototype with
  | .ok result => pure result
  | _ => throw (IO.userError "object allocation failed")

private def allocateFunction (machine : Machine platform) : IO (RefId × Machine platform) :=
  match machine.heap.allocateFunction machine.globalEnv .ordinary false none with
  | .ok (ref, heap) => pure (ref, machine.setHeap heap)
  | _ => throw (IO.userError "function allocation failed")

private def define (heap : Heap) (ref : RefId) (propertyKey : PropertyKey)
    (update : DescriptorUpdate) : IO Heap :=
  match heap.defineOwnProperty ref propertyKey update with
  | .ok (true, next) => pure next
  | _ => throw (IO.userError "property definition failed")

private def data (heap : Heap) (ref : RefId) (propertyKey : PropertyKey) (value : Value) : IO Heap :=
  define heap ref propertyKey {
    value := .present value
    writable := .present true
    enumerable := .present true
    configurable := .present true }

private def emitted (machine : Machine platform) : List String :=
  machine.trace.filterMap fun
    | .emitted value => value.toLeanString?
    | _ => none

private def withTrace (result : String) (machine : Machine platform) : String :=
  result ++ "|" ++ String.intercalate "," (emitted machine)

private def encodePrimitive : Primitive → String
  | .undefined => "undefined"
  | .null => "null"
  | .boolean value => "boolean:" ++ toString value
  | .number value => "number:" ++ value.bits.toNat.repr
  | .string value => "string:" ++ value.toLeanString?.getD "malformed"
  | .bigint value => "bigint:" ++ value.repr
  | .symbol _ => "symbol"

private def encodeValue : Value → String
  | .primitive primitive => encodePrimitive primitive
  | .object _ => "object"

private def encodeThrown : Value → String
  | .primitive (.string value) =>
      let rendered := value.toLeanString?.getD "malformed"
      if rendered.startsWith "TypeError:" then "error:TypeError"
      else if rendered.startsWith "RangeError:" then "error:RangeError"
      else if rendered.startsWith "ReferenceError:" then "error:ReferenceError"
      else if rendered.startsWith "SyntaxError:" then "error:SyntaxError"
      else "throw:string:" ++ rendered
  | .primitive (.bigint value) => "throw:bigint:" ++ value.repr
  | .primitive (.boolean value) => "throw:boolean:" ++ toString value
  | .primitive (.number value) => "throw:number:" ++ value.bits.toNat.repr
  | .primitive .undefined => "throw:undefined"
  | .primitive .null => "throw:null"
  | .primitive (.symbol _) => "throw:symbol"
  | .object _ => "throw:object"

private def observe (encode : α → String) (action : JSM platform α)
    (machine : Machine platform) : String :=
  match action machine with
  | .done (.normal value) next => withTrace (encode value) next
  | .done (.thrown value) next => withTrace (encodeThrown value) next
  | .fault (.runtime .realmNotInitialized) next => withTrace "fault:realmNotInitialized" next
  | .fault _ next => withTrace "fault:model" next
  | .exhausted next => withTrace "fault:exhausted" next
  | .done _ next => withTrace "fault:control" next

private def observePrimitive (action : JSM platform Primitive) (machine : Machine platform) : String :=
  observe encodePrimitive action machine

private def observeValue (action : JSM platform Value) (machine : Machine platform) : String :=
  observe encodeValue action machine

private def observeBool (action : JSM platform Bool) (machine : Machine platform) : String :=
  observe (fun value => "boolean:" ++ toString value) action machine

private def emitReturn (event : String) (value : Value) : JSM platform Unit := fun machine =>
  JSM.returnJS value (machine.emit (.emitted (JSString.ofLeanString event)))

private def primitiveAndOperatorScenarios : IO (List String) := do
  let machine := Machine.initial platform 10000
  let (left, heap) ← allocateObject machine.heap
  let (right, heap) ← allocateObject heap
  let machine := machine.setHeap heap
  let (leftMethod, machine) ← allocateFunction machine
  let (rightMethod, machine) ← allocateFunction machine
  let heap ← data machine.heap left (.symbol (.wellKnown .toPrimitive)) (.object leftMethod)
  let heap ← data heap right (.symbol (.wellKnown .toPrimitive)) (.object rightMethod)
  let machine := machine.setHeap heap
  let hook : BodyHook platform := fun ref _ arguments =>
    let hint := match arguments[0]? with
      | some (Value.primitive (.string value)) => value.toLeanString?.getD "?"
      | _ => "?"
    if ref = leftMethod then emitReturn ("left:" ++ hint) (text "5")
    else emitReturn ("right:" ++ hint) (text "7")
  let numberFive : Value := .primitive (.number (JSNumber.parse (JSString.ofLeanString "5")))
  let sameSymbol : SymbolId := .allocated 11
  let symbolHook : BodyHook platform := fun ref _ _ =>
    emitReturn (if ref = leftMethod then "left:default" else "right:default")
      (.primitive (.symbol sameSymbol))
  let objectHook : BodyHook platform := fun ref _ _ =>
    emitReturn (if ref = leftMethod then "left:default" else "right:default") (.object left)
  let throwingHook : BodyHook platform := fun ref _ _ current =>
    let event := if ref = leftMethod then "left" else "right"
    let next := current.emit (.emitted (JSString.ofLeanString event))
    if ref = rightMethod then JSM.throwJS (bigint 88) next else JSM.returnJS (text "5") next
  let stringThrowHook : BodyHook platform := fun _ _ _ current =>
    JSM.throwJS (text "user-thrown")
      (current.emit (.emitted (JSString.ofLeanString "string-throw")))
  let rangeThrowHook : BodyHook platform := fun _ _ _ current =>
    JSM.throwJS (text "RangeError: range")
      (current.emit (.emitted (JSString.ofLeanString "range-throw")))
  pure [
    observePrimitive (AbstractOperations.toPrimitive hook (.object left)) machine,
    observe (fun value => "number:" ++ value.bits.toNat.repr)
      (AbstractOperations.toNumber hook (.object left)) machine,
    observe (fun value => "string:" ++ value.toLeanString?.getD "malformed")
      (AbstractOperations.toString hook (.object left)) machine,
    observeBool (AbstractEquality.looseEqual hook (.object left) (text "5")) machine,
    observeBool (AbstractEquality.looseEqual hook (.object left) numberFive) machine,
    observeBool (AbstractEquality.looseEqual hook (.object left) (bigint 5)) machine,
    observeBool (AbstractEquality.looseEqual hook (.object left) (.primitive (.boolean true))) machine,
    observeBool (AbstractEquality.looseEqual hook (.object left) (.primitive (.boolean false))) machine,
    observeBool (AbstractEquality.looseEqual hook (.object left) (.primitive .null) ) machine,
    observeBool (AbstractEquality.looseEqual hook (.object left) undefined) machine,
    observeBool (AbstractEquality.looseEqual hook (.object left)
      (.primitive (.symbol sameSymbol))) machine,
    observeBool (AbstractEquality.looseEqual hook (.object left) (.object left)) machine,
    observeBool (AbstractEquality.looseEqual hook (.object left) (.object right)) machine,
    observeBool (AbstractEquality.looseEqual symbolHook (.object left)
      (.primitive (.symbol sameSymbol))) machine,
    observeBool (AbstractEquality.looseEqual symbolHook (.object left)
      (.primitive (.symbol (.allocated 12)))) machine,
    observeValue (AbstractEquality.add hook (.object left) (.object right)) machine,
    observeBool (AbstractEquality.lessThan hook (.object left) (.object right)) machine,
    observeBool (AbstractEquality.greaterThan hook (.object right) (.object left)) machine,
    observeBool (AbstractEquality.lessThanOrEqual hook (.object left) (.object right)) machine,
    observeBool (AbstractEquality.greaterThanOrEqual hook (.object right) (.object left)) machine,
    observeBool (AbstractEquality.lessThan hook (.object right) (.object left)) machine,
    observeBool (AbstractEquality.greaterThan hook (.object left) (.object right)) machine,
    observeBool (AbstractEquality.lessThanOrEqual hook (.object right) (.object left)) machine,
    observeBool (AbstractEquality.greaterThanOrEqual hook (.object left) (.object right)) machine,
    observePrimitive (AbstractOperations.toPrimitive objectHook (.object left)) machine,
    observePrimitive (AbstractOperations.toPrimitive throwingHook (.object right)) machine,
    observeValue (AbstractEquality.add throwingHook (.object left) (.object right)) machine,
    observeBool (AbstractEquality.lessThan throwingHook (.object left) (.object right)) machine,
    observePrimitive (AbstractOperations.toPrimitive stringThrowHook (.object left)) machine,
    observePrimitive (AbstractOperations.toPrimitive rangeThrowHook (.object left)) machine]

private def getAndOrdinaryScenarios : IO (List String) := do
  let machine := Machine.initial platform 10000
  let (prototype, heap) ← allocateObject machine.heap
  let (base, heap) ← allocateObject heap (some prototype)
  let (undefinedMethod, heap) ← allocateObject heap (some prototype)
  let (nullMethod, heap) ← allocateObject heap (some prototype)
  let (nonCallable, heap) ← allocateObject heap (some prototype)
  let (getterReceiver, heap) ← allocateObject heap (some prototype)
  let machine := machine.setHeap heap
  let (valueOf, machine) ← allocateFunction machine
  let (toStringRef, machine) ← allocateFunction machine
  let (getter, machine) ← allocateFunction machine
  let heap ← data machine.heap prototype (key "valueOf") (.object valueOf)
  let heap ← data heap prototype (key "toString") (.object toStringRef)
  let heap ← data heap undefinedMethod (.symbol (.wellKnown .toPrimitive)) undefined
  let heap ← data heap nullMethod (.symbol (.wellKnown .toPrimitive)) (.primitive .null)
  let heap ← data heap nonCallable (.symbol (.wellKnown .toPrimitive)) (bigint 1)
  let heap ← define heap getterReceiver (key "valueOf") { get := .present (some getter) }
  let machine := machine.setHeap heap
  let hook : BodyHook platform := fun ref receiver _ =>
    if ref = getter then emitReturn "get" (.object valueOf)
    else if ref = valueOf then
      if receiver = .object base then emitReturn "valueOf" (.object base)
      else emitReturn "valueOf" (text "value")
    else emitReturn "toString" (text "ordinary")
  let getterHook : BodyHook platform := fun ref _ _ =>
    if ref = getter then emitReturn "get" (.object valueOf)
    else emitReturn "call" (text "getter")
  let getterThrowHook : BodyHook platform := fun ref _ _ current =>
    let event := if ref = getter then "get" else "call"
    JSM.throwJS (bigint 17) (current.emit (.emitted (JSString.ofLeanString event)))
  let objectHook : BodyHook platform := fun ref _ _ =>
    emitReturn (if ref = valueOf then "valueOf" else "toString") (.object base)
  pure [
    observePrimitive (AbstractOperations.toPrimitive hook (.object undefinedMethod)) machine,
    observePrimitive (AbstractOperations.toPrimitive hook (.object nullMethod)) machine,
    observePrimitive (AbstractOperations.toPrimitive hook (.object nonCallable)) machine,
    observe (fun value => "number:" ++ value.bits.toNat.repr)
      (AbstractOperations.toNumber hook (.object base)) machine,
    observePrimitive (AbstractOperations.toPrimitive hook (.object base) .string) machine,
    observePrimitive (AbstractOperations.toPrimitive getterHook (.object getterReceiver) .number) machine,
    observePrimitive (AbstractOperations.toPrimitive getterThrowHook (.object getterReceiver) .number) machine,
    observePrimitive (AbstractOperations.toPrimitive objectHook (.object base) .number) machine]

private def hasInstanceScenarios : IO (List String) := do
  let machine := Machine.initial platform 10000
  let (objectPrototype, heap) ← allocateObject machine.heap
  let (constructor, prototype, heap) ← match heap.allocateConstructorPair
      machine.globalEnv none (some objectPrototype) with
    | .ok result => pure result
    | _ => throw (IO.userError "constructor allocation failed")
  let (instanceRef, heap) ← allocateObject heap (some prototype)
  let (forged, heap) ← allocateObject heap (some objectPrototype)
  let (ordinary, heap) ← allocateObject heap
  let baseMachine := machine.setHeap heap
  let (method, machine) ← allocateFunction baseMachine
  let (getter, machine) ← allocateFunction machine
  let customHeap ← define machine.heap constructor (.symbol (.wellKnown .hasInstance)) {
    get := .present (some getter), configurable := .present true }
  let customMachine := machine.setHeap customHeap
  let customHook : BodyHook platform := fun ref _ _ =>
    if ref = getter then emitReturn "get" (.object method)
    else emitReturn "call" (.object forged)
  let falseHook : BodyHook platform := fun ref _ _ =>
    if ref = getter then emitReturn "get" (.object method)
    else emitReturn "call" (.primitive (.boolean false))
  let getterThrow : BodyHook platform := fun ref _ _ current =>
    let event := if ref = getter then "get" else "call"
    JSM.throwJS (bigint 72) (current.emit (.emitted (JSString.ofLeanString event)))
  let methodThrow : BodyHook platform := fun ref _ _ current =>
    if ref = getter then emitReturn "get" (.object method) current
    else JSM.throwJS (bigint 73)
      (current.emit (.emitted (JSString.ofLeanString "call")))
  let nonCallableHeap ← define customHeap constructor (.symbol (.wellKnown .hasInstance)) {
    value := .present (bigint 1) }
  let primitivePrototypeHeap ← define baseMachine.heap constructor (key "prototype") {
    value := .present (bigint 1) }
  pure [
    observeBool (Instanceof.instanceofOperator customHook (.object forged) (.object constructor))
      customMachine,
    observeBool (Instanceof.instanceofOperator falseHook (.object forged) (.object constructor))
      customMachine,
    observeBool (Instanceof.instanceofOperator getterThrow (.object forged) (.object constructor))
      customMachine,
    observeBool (Instanceof.instanceofOperator methodThrow (.object forged) (.object constructor))
      customMachine,
    observeBool (Instanceof.instanceofOperator fallthrough (.object forged) (.object constructor))
      (machine.setHeap nonCallableHeap),
    observeBool (Instanceof.instanceofOperator fallthrough (.object instanceRef) (.object constructor))
      baseMachine,
    observeBool (Instanceof.instanceofOperator fallthrough (.object forged) (.object constructor))
      baseMachine,
    observeBool (Instanceof.instanceofOperator fallthrough (.object forged) (.object ordinary))
      baseMachine,
    observeBool (Instanceof.instanceofOperator fallthrough (.object forged) (.object constructor))
      (baseMachine.setHeap primitivePrototypeHeap),
    observeBool (Instanceof.instanceofOperator fallthrough (.object forged) (bigint 1)) baseMachine]

private def ownString (heap : Heap) (ref : RefId) (name : String) : Option JSString :=
  match heap.getOwnProperty ref (key name) with
  | .ok (some (.data { value := .primitive (.string value), .. })) => some value
  | _ => none

private def realmAndCopyScenarios : IO (List String) := do
  let fixture ← match RealmTestSupport.bootstrap (Machine.initial platform 10000) with
    | .ok fixture => pure fixture
    | .error _ => throw (IO.userError "realm bootstrap failed")
  let hook := fixture.bodyHook
  let machine := fixture.machine
  let box (primitive : Primitive) : IO (RefId × Machine platform) :=
    match AbstractOperations.toObject (.primitive primitive) machine with
    | .done (.normal ref) next => pure (ref, next)
    | _ => throw (IO.userError "boxing failed")
  let (booleanRef, booleanMachine) ← box (.boolean true)
  let (numberRef, numberMachine) ← box (.number JSNumber.one)
  let (stringRef, stringMachine) ← box (.string (JSString.ofLeanString "box"))
  let (bigintRef, bigintMachine) ← box (.bigint 9)
  let (symbolRef, symbolMachine) ← box (.symbol (.allocated 5))
  let prototypeResult (next : Machine platform) (ref expected : RefId) :=
    match next.heap.get? ref with
    | .ok object => "boolean:" ++ toString (decide (object.prototype = some expected)) ++ "|"
    | _ => "invalid"
  let (target, targetHeap) ← allocateObject machine.heap
  let targetMachine := machine.setHeap targetHeap
  let assignedString := match Copy.objectAssign hook (.object target)
      [.primitive (.string (JSString.ofLeanString "ab"))] targetMachine with
    | .done (.normal (.object ref)) next =>
        let value := (ownString next.heap ref "0").getD (JSString.ofLeanString "?") |>.append
          ((ownString next.heap ref "1").getD (JSString.ofLeanString "?"))
        withTrace ("string:" ++ value.toLeanString?.getD "malformed") next
    | _ => "invalid"
  let spreadString := match Copy.objectSpread hook
      [.primitive (.string (JSString.ofLeanString "xy"))] [] machine with
    | .done (.normal ref) next =>
        let value := (ownString next.heap ref "0").getD (JSString.ofLeanString "?") |>.append
          ((ownString next.heap ref "1").getD (JSString.ofLeanString "?"))
        withTrace ("string:" ++ value.toLeanString?.getD "malformed") next
    | _ => "invalid"
  let emptySpread := match Copy.objectSpread hook
      [.primitive .null, .primitive .undefined, .primitive (.symbol (.allocated 9))] [] machine with
    | .done (.normal ref) next =>
        match next.heap.ownPropertyKeys ref with
        | .ok keys => withTrace ("number:" ++ keys.length.repr) next
        | _ => "invalid"
    | _ => "invalid"
  let assignedBoolean := match Copy.objectAssign hook (.primitive (.boolean true)) [] machine with
    | .done (.normal (.object ref)) next => prototypeResult next ref fixture.intrinsics.booleanPrototype
    | _ => "invalid"
  let mutatedIntrinsic := match machine.heap.setPrototypeOf fixture.intrinsics.booleanPrototype none with
    | .ok (true, heap) =>
        let mutated := machine.setHeap heap
        match AbstractOperations.toObject (.primitive (.boolean true)) mutated with
        | .done (.normal ref) next => prototypeResult next ref fixture.intrinsics.booleanPrototype
        | _ => "invalid"
    | _ => "invalid"
  let mutatedWrapper := match AbstractOperations.toObject (.primitive (.boolean true)) machine with
    | .done (.normal ref) next =>
        match next.heap.setPrototypeOf ref none with
        | .ok (true, heap) =>
            match heap.get? ref with
            | .ok object => "boolean:" ++ toString object.prototype.isNone ++ "|"
            | _ => "invalid"
        | _ => "invalid"
    | _ => "invalid"
  pure [
    observe (fun value => "number:" ++ value.bits.toNat.repr)
      (AbstractOperations.toNumber hook (.object booleanRef)) booleanMachine,
    observePrimitive (AbstractOperations.toPrimitive hook (.object numberRef) .number) numberMachine,
    observePrimitive (AbstractOperations.toPrimitive hook (.object numberRef) .string) numberMachine,
    observePrimitive (AbstractOperations.toPrimitive hook (.object stringRef) .number) stringMachine,
    observePrimitive (AbstractOperations.toPrimitive hook (.object stringRef) .string) stringMachine,
    observePrimitive (AbstractOperations.toPrimitive hook (.object bigintRef) .number) bigintMachine,
    observePrimitive (AbstractOperations.toPrimitive hook (.object bigintRef) .string) bigintMachine,
    observePrimitive (AbstractOperations.toPrimitive hook (.object symbolRef) .number) symbolMachine,
    observePrimitive (AbstractOperations.toPrimitive hook (.object symbolRef) .string) symbolMachine,
    observeBool (AbstractEquality.looseEqual hook (.object numberRef)
      (.primitive (.number JSNumber.one))) numberMachine,
    prototypeResult booleanMachine booleanRef fixture.intrinsics.booleanPrototype,
    prototypeResult numberMachine numberRef fixture.intrinsics.numberPrototype,
    prototypeResult stringMachine stringRef fixture.intrinsics.stringPrototype,
    prototypeResult bigintMachine bigintRef fixture.intrinsics.bigintPrototype,
    prototypeResult symbolMachine symbolRef fixture.intrinsics.symbolPrototype,
    assignedBoolean, assignedString, spreadString, emptySpread,
    observePrimitive (AbstractOperations.toPrimitive hook
      (.object fixture.intrinsics.booleanPrototype) .number) machine,
    observePrimitive (AbstractOperations.toPrimitive hook
      (.object fixture.intrinsics.booleanPrototype) .string) machine,
    observePrimitive (AbstractOperations.toPrimitive hook
      (.object fixture.intrinsics.numberPrototype) .number) machine,
    observePrimitive (AbstractOperations.toPrimitive hook
      (.object fixture.intrinsics.numberPrototype) .string) machine,
    observePrimitive (AbstractOperations.toPrimitive hook
      (.object fixture.intrinsics.stringPrototype) .number) machine,
    observePrimitive (AbstractOperations.toPrimitive hook
      (.object fixture.intrinsics.stringPrototype) .string) machine,
    observePrimitive (AbstractOperations.toPrimitive hook
      (.object fixture.intrinsics.bigintPrototype) .number) machine,
    observePrimitive (AbstractOperations.toPrimitive hook
      (.object fixture.intrinsics.bigintPrototype) .string) machine,
    observePrimitive (AbstractOperations.toPrimitive hook
      (.object fixture.intrinsics.symbolPrototype) .number) machine,
    observePrimitive (AbstractOperations.toPrimitive hook
      (.object fixture.intrinsics.symbolPrototype) .string) machine,
    mutatedIntrinsic, mutatedWrapper]

private def realmFuzzScenarios : IO (List String) := do
  let fixture ← match RealmTestSupport.bootstrap (Machine.initial platform 10000) with
    | .ok fixture => pure fixture
    | .error _ => throw (IO.userError "realm bootstrap failed")
  let samples : List Primitive := [
    .boolean false,
    .number JSNumber.positiveZero,
    .string (JSString.ofLeanString "0"),
    .bigint 0,
    .boolean true,
    .number JSNumber.one,
    .string (JSString.ofLeanString "1"),
    .bigint 1,
    .symbol (.allocated 91)]
  let successors := samples.drop 1 ++ [samples.head?.getD (.boolean false)]
  let mut results := #[]
  for pair in samples.zip successors do
    let primitive := pair.1
    let nextPrimitive := pair.2
    match AbstractOperations.toObject (.primitive primitive) fixture.machine with
    | .done (.normal ref) machine =>
        results := results.push (observeBool
          (AbstractEquality.looseEqual fixture.bodyHook (.object ref) (.primitive primitive)) machine)
        results := results.push (observeBool
          (AbstractEquality.looseEqual fixture.bodyHook (.object ref) (.primitive nextPrimitive)) machine)
    | _ => throw (IO.userError "fuzz boxing failed")
  pure results.toList

/-- Complete deterministic scenario set consumed by the Node differential test. -/
def scenarios : IO (List String) := do
  pure ((← primitiveAndOperatorScenarios) ++ (← getAndOrdinaryScenarios) ++
    (← hasInstanceScenarios) ++ (← realmAndCopyScenarios) ++ (← realmFuzzScenarios))

end TSLean.JS.AbstractOperationsOracleTests

def main (_ : List String) : IO UInt32 := do
  for result in ← TSLean.JS.AbstractOperationsOracleTests.scenarios do IO.println result
  pure 0
