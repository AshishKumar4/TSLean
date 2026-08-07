import TSLean.JS.AbstractEquality
import TSLean.JS.Copy
import TSLean.JS.HasInstance
import TSLean.JS.RealmTestSupportTests

namespace TSLean.JS.AbstractOperationsTests

private def platform : Platform := ScriptedPlatform.make {
  times := #[], randoms := #[], fetches := #[]
}

private def key (text : String) : PropertyKey := .string (JSString.ofLeanString text)
private def text (value : String) : Value := .primitive (.string (JSString.ofLeanString value))
private def bigint (value : Int) : Value := .primitive (.bigint value)
private def undefined : Value := .primitive .undefined
private def fallthrough : BodyHook platform := fun _ _ _ => pure ()

private def runNormal (action : JSM platform α) (machine : Machine platform) : IO (α × Machine platform) :=
  match action machine with
  | .done (.normal value) next => pure (value, next)
  | _ => throw (IO.userError "expected normal completion")

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

private def emitReturn (event : String) (value : Value) : JSM platform Unit := fun machine =>
  JSM.returnJS value (machine.emit (.emitted (JSString.ofLeanString event)))

private def emitted (machine : Machine platform) : List String :=
  machine.trace.map fun
    | .emitted value => value.toLeanString?.getD "malformed"
    | _ => "platform"

private def callableValue (heap : Heap) : Value → Bool
  | .object ref => match heap.isCallable ref with
      | .ok callable => callable
      | .error _ => false
  | .primitive _ => false

private def testOrdinaryToPrimitive : IO Unit := do
  let machine := Machine.initial platform 10000
  let (prototype, heap) ← allocateObject machine.heap
  let (receiver, heap) ← allocateObject heap (some prototype)
  let machine := machine.setHeap heap
  let (valueOf, machine) ← allocateFunction machine
  let (toString, machine) ← allocateFunction machine
  let heap ← data machine.heap prototype (key "valueOf") (.object valueOf)
  let heap ← data heap prototype (key "toString") (.object toString)
  let hook : BodyHook platform := fun ref actual _ =>
    if actual != .object receiver then JSM.throwJS (bigint 99)
    else if ref = valueOf then emitReturn "valueOf" (.object receiver)
    else if ref = toString then emitReturn "toString" (text "ordinary")
    else pure ()
  let machine := machine.setHeap heap
  let (numberHint, numberMachine) ← runNormal
    (AbstractOperations.toPrimitive hook (.object receiver) .number) machine
  assert! numberHint = .string (JSString.ofLeanString "ordinary")
  assert! emitted numberMachine = ["valueOf", "toString"]
  let (stringHint, stringMachine) ← runNormal
    (AbstractOperations.toPrimitive hook (.object receiver) .string) machine
  assert! stringHint = .string (JSString.ofLeanString "ordinary")
  assert! emitted stringMachine = ["toString"]

  let objectHook : BodyHook platform := fun ref _ _ =>
    emitReturn (if ref = valueOf then "valueOf" else "toString") (.object receiver)
  match AbstractOperations.toPrimitive objectHook (.object receiver) .default machine with
  | .done (.thrown _) next => assert! emitted next = ["valueOf", "toString"]
  | _ => assert! false

  let (ordinaryGetter, getterMachine) ← allocateFunction machine
  let getterHeap ← define getterMachine.heap receiver (key "valueOf") {
    get := .present (some ordinaryGetter) }
  let getterHook : BodyHook platform := fun ref _ _ current =>
    if ref = ordinaryGetter then JSM.throwJS (bigint 23)
      (current.emit (.emitted (JSString.ofLeanString "valueOf-getter")))
    else .done (.normal ()) current
  match AbstractOperations.ordinaryToPrimitive getterHook receiver .number
      (getterMachine.setHeap getterHeap) with
  | .done (.thrown value) next =>
      assert! value = bigint 23
      assert! emitted next = ["valueOf-getter"]
  | _ => assert! false

private def testExoticToPrimitiveAndConversions : IO Unit := do
  let machine := Machine.initial platform 10000
  let (receiver, heap) ← allocateObject machine.heap
  let machine := machine.setHeap heap
  let (exotic, machine) ← allocateFunction machine
  let heap ← data machine.heap receiver (.symbol (.wellKnown .toPrimitive)) (.object exotic)
  let hook : BodyHook platform := fun ref actual arguments =>
    if ref != exotic || actual != .object receiver then JSM.throwJS (bigint 90)
    else match arguments[0]? with
      | some (Value.primitive (.string hint)) =>
          let name := hint.toLeanString?.getD "malformed"
          emitReturn name (text (if name = "number" then "7" else name))
      | _ => JSM.throwJS (bigint 91)
  let machine := machine.setHeap heap
  let (_, machine) ← runNormal (AbstractOperations.toPrimitive hook (.object receiver)) machine
  let (_, machine) ← runNormal
    (AbstractOperations.toPrimitive hook (.object receiver) .string) machine
  let (number, machine) ← runNormal (AbstractOperations.toNumber hook (.object receiver)) machine
  assert! number.strictEqual (JSNumber.parse (JSString.ofLeanString "7"))
  assert! emitted machine = ["default", "string", "number"]
  let (stringValue, _) ← runNormal (AbstractOperations.toString hook (.object receiver)) machine
  assert! stringValue.equal (JSString.ofLeanString "string")

  let symbolHook : BodyHook platform := fun _ _ _ =>
    JSM.returnJS (.primitive (.symbol (.allocated 42)))
  let (propertyKey, _) ← runNormal
    (AbstractOperations.toPropertyKey symbolHook (.object receiver)) machine
  assert! propertyKey = .symbol (.allocated 42)

  let objectHook : BodyHook platform := fun _ _ _ => JSM.returnJS (.object receiver)
  match (AbstractOperations.toPrimitive objectHook (.object receiver)) machine with
  | .done (.thrown _) _ => pure ()
  | _ => assert! false

  let throwingHook : BodyHook platform := fun _ _ _ current =>
    JSM.throwJS (bigint 19) (current.emit (.emitted (JSString.ofLeanString "call-throw")))
  match (AbstractOperations.toPrimitive throwingHook (.object receiver)) machine with
  | .done (.thrown value) next =>
      assert! value = bigint 19
      assert! emitted next = emitted machine ++ ["call-throw"]
  | _ => assert! false

  let badHeap ← define heap receiver (.symbol (.wellKnown .toPrimitive)) {
    value := .present (bigint 1) }
  match (AbstractOperations.toPrimitive hook (.object receiver)) (machine.setHeap badHeap) with
  | .done (.thrown _) _ => pure ()
  | _ => assert! false

private def testGetterThrowsAndGetMethod : IO Unit := do
  let machine := Machine.initial platform 10000
  let (receiver, heap) ← allocateObject machine.heap
  let machine := machine.setHeap heap
  let (getter, machine) ← allocateFunction machine
  let heap ← define machine.heap receiver (.symbol (.wellKnown .toPrimitive)) {
    get := .present (some getter) }
  let hook : BodyHook platform := fun ref actual _ machine =>
    if ref = getter && actual = .object receiver then
      JSM.throwJS (bigint 17) (machine.emit (.emitted (JSString.ofLeanString "getter")))
    else JSM.throwJS (bigint 18) machine
  match (AbstractOperations.toPrimitive hook (.object receiver)) (machine.setHeap heap) with
  | .done (.thrown value) next =>
      assert! value = bigint 17
      assert! emitted next = ["getter"]
  | _ => assert! false

private def testToObject : IO Unit := do
  let unconfigured := Machine.initial platform 100
  match AbstractOperations.toObject (.primitive (.boolean true)) unconfigured with
  | .fault (.runtime .realmNotInitialized) next => assert! next.heap.size = 0
  | _ => assert! false
  let fixture ← match RealmTestSupport.bootstrap unconfigured with
    | .ok fixture => pure fixture
    | .error _ => throw (IO.userError "realm bootstrap failed")
  let machine := fixture.machine
  let (object, heap) ← allocateObject machine.heap
  let machine := machine.setHeap heap
  let (same, unchanged) ← runNormal (AbstractOperations.toObject (.object object)) machine
  assert! same = object
  assert! unchanged.heap.size = machine.heap.size
  let (wrapper, boxed) ← runNormal
    (AbstractOperations.toObject (.primitive (.boolean true))) machine
  match boxed.heap.get? wrapper with
  | .ok record =>
      match record.kind with
      | .primitiveWrapper slots =>
          assert! slots.value = .boolean true
          assert! record.prototype = some fixture.intrinsics.booleanPrototype
      | _ => assert! false
  | _ => assert! false
  for nullish in [Value.primitive .undefined, .primitive .null] do
    match AbstractOperations.toObject nullish machine with
    | .done (.thrown _) next => assert! next.heap.size = machine.heap.size
    | _ => assert! false

  let hook := fixture.bodyHook
  let (booleanWrapper, machine) ← runNormal
    (AbstractOperations.toObject (.primitive (.boolean true))) machine
  let (booleanNumber, machine) ← runNormal
    (AbstractOperations.toNumber hook (.object booleanWrapper)) machine
  assert! booleanNumber = JSNumber.one
  let samples : List (Primitive × RefId) := [
    (.number JSNumber.one, fixture.intrinsics.numberPrototype),
    (.string (JSString.ofLeanString "box"), fixture.intrinsics.stringPrototype),
    (.bigint 9, fixture.intrinsics.bigintPrototype),
    (.symbol (.allocated 5), fixture.intrinsics.symbolPrototype)]
  let mut machine := machine
  for sample in samples do
    let (ref, next) ← runNormal (AbstractOperations.toObject (.primitive sample.1)) machine
    machine := next
    match machine.heap.get? ref with
    | .ok record => assert! record.prototype = some sample.2
    | _ => assert! false
    let (valueOf, next) ← runNormal
      (AbstractOperations.toPrimitive hook (.object ref) .number) machine
    machine := next
    assert! valueOf = sample.1
    let (stringValue, next) ← runNormal
      (AbstractOperations.toPrimitive hook (.object ref) .string) machine
    machine := next
    match sample.1, stringValue with
    | .number _, .string value => assert! value.equal (JSString.ofLeanString "1")
    | .string expected, .string actual => assert! actual.equal expected
    | .bigint _, .string value => assert! value.equal (JSString.ofLeanString "9")
    | .symbol _, .string value => assert! value.equal (JSString.ofLeanString "Symbol()")
    | _, _ => assert! false
  let (numberWrapper, nextMachine) ← runNormal
    (AbstractOperations.toObject (.primitive (.number JSNumber.one))) machine
  let (boxedEqual, _) ← runNormal
    (AbstractEquality.looseEqual hook (.object numberWrapper)
      (.primitive (.number JSNumber.one))) nextMachine
  assert! boxedEqual
  assert! nextMachine.isWellFormed

private def testRealmConfiguration : IO Unit := do
  let initial := Machine.initial platform 100
  assert! initial.isWellFormed
  let fixture ← match RealmTestSupport.bootstrap initial with
    | .ok fixture => pure fixture
    | .error _ => throw (IO.userError "realm bootstrap failed")
  assert! fixture.machine.isWellFormed
  assert! fixture.intrinsics.intrinsicsRefsValid fixture.machine.heap
  assert! fixture.intrinsics.bootstrapTopologyValid fixture.machine.heap
  let duplicate := { fixture.intrinsics with
    symbolPrototype := fixture.intrinsics.bigintPrototype }
  assert! fixture.machine.installRealmIntrinsics duplicate matches
    .error .invalidRealmIntrinsics
  let detachedHeap ← match fixture.machine.heap.setPrototypeOf
      fixture.intrinsics.booleanPrototype none with
    | .ok (true, heap) => pure heap
    | _ => throw (IO.userError "intrinsic prototype detach failed")
  let detachedMachine := fixture.machine.setHeap detachedHeap
  assert! detachedMachine.isWellFormed
  assert! fixture.intrinsics.intrinsicsRefsValid detachedHeap
  assert! !fixture.intrinsics.bootstrapTopologyValid detachedHeap
  assert! (fixture.machine.setHeap detachedHeap).installRealmIntrinsics fixture.intrinsics matches
    .error .invalidRealmIntrinsics
  let (afterMutationWrapper, afterMutationMachine) ← runNormal
    (AbstractOperations.toObject (.primitive (.boolean true))) detachedMachine
  match afterMutationMachine.heap.get? afterMutationWrapper with
  | .ok object => assert! object.prototype = some fixture.intrinsics.booleanPrototype
  | _ => assert! false
  assert! afterMutationMachine.isWellFormed
  let dangling := { fixture.intrinsics with objectPrototype := ⟨9999⟩ }
  assert! fixture.machine.installRealmIntrinsics dangling matches
    .error .invalidRealmIntrinsics
  let wrongWrapperHeap ← match fixture.machine.heap.allocatePrimitiveWrapper
      (.boolean true) (some fixture.intrinsics.numberPrototype) with
    | .ok (_, heap) => pure heap
    | .error _ => throw (IO.userError "wrong wrapper allocation failed")
  assert! wrongWrapperHeap.isWellFormed
  assert! (fixture.machine.setHeap wrongWrapperHeap).isWellFormed
  assert! (fixture.machine.setHeap wrongWrapperHeap).installRealmIntrinsics fixture.intrinsics matches
    .ok _
  let (ordinaryRef, ordinaryHeap) ← allocateObject fixture.machine.heap
  let wrongKind := { fixture.intrinsics with booleanPrototype := ordinaryRef }
  assert! !(wrongKind.intrinsicsRefsValid ordinaryHeap)
  assert! (fixture.machine.setHeap ordinaryHeap).installRealmIntrinsics wrongKind matches
    .error .invalidRealmIntrinsics

  let (boxedBoolean, boxedMachine) ← runNormal
    (AbstractOperations.toObject (.primitive (.boolean true))) fixture.machine
  let mutatedBoxHeap ← match boxedMachine.heap.setPrototypeOf boxedBoolean none with
    | .ok (true, heap) => pure heap
    | _ => throw (IO.userError "boxed Boolean prototype mutation failed")
  assert! (boxedMachine.setHeap mutatedBoxHeap).isWellFormed

  let hook := fixture.bodyHook
  let (booleanValue, _) ← runNormal
    (AbstractOperations.toPrimitive hook (.object fixture.intrinsics.booleanPrototype) .number)
    fixture.machine
  let (booleanString, _) ← runNormal
    (AbstractOperations.toPrimitive hook (.object fixture.intrinsics.booleanPrototype) .string)
    fixture.machine
  let (numberValue, _) ← runNormal
    (AbstractOperations.toPrimitive hook (.object fixture.intrinsics.numberPrototype) .number)
    fixture.machine
  let (stringValue, _) ← runNormal
    (AbstractOperations.toPrimitive hook (.object fixture.intrinsics.stringPrototype) .string)
    fixture.machine
  assert! booleanValue = .boolean false
  assert! booleanString = .string (JSString.ofLeanString "false")
  assert! numberValue = .number JSNumber.positiveZero
  assert! stringValue = .string (JSString.ofLeanString "")
  for prototype in [fixture.intrinsics.bigintPrototype, fixture.intrinsics.symbolPrototype] do
    match AbstractOperations.toPrimitive hook (.object prototype) .number fixture.machine with
    | .done (.thrown _) _ => pure ()
    | _ => assert! false
    match AbstractOperations.toPrimitive hook (.object prototype) .string fixture.machine with
    | .done (.thrown _) _ => pure ()
    | _ => assert! false
  for prototype in [fixture.intrinsics.booleanPrototype, fixture.intrinsics.numberPrototype,
      fixture.intrinsics.stringPrototype, fixture.intrinsics.bigintPrototype,
      fixture.intrinsics.symbolPrototype] do
    for name in ["valueOf", "toString"] do
      match fixture.machine.heap.getOwnProperty prototype (key name) with
      | .ok (some (.data descriptor)) =>
          assert! descriptor.writable && !descriptor.enumerable && descriptor.configurable
          assert! callableValue fixture.machine.heap descriptor.value
      | _ => assert! false

private def testEqualityAndOperators : IO Unit := do
  let machine := Machine.initial platform 10000
  let (left, heap) ← allocateObject machine.heap
  let (right, heap) ← allocateObject heap
  let machine := machine.setHeap heap
  let (leftMethod, machine) ← allocateFunction machine
  let (rightMethod, machine) ← allocateFunction machine
  let heap ← data machine.heap left (.symbol (.wellKnown .toPrimitive)) (.object leftMethod)
  let heap ← data heap right (.symbol (.wellKnown .toPrimitive)) (.object rightMethod)
  let hook : BodyHook platform := fun ref _ arguments =>
    let hint := match arguments[0]? with
      | some (Value.primitive (.string value)) => value.toLeanString?.getD "?"
      | _ => "?"
    if ref = leftMethod then emitReturn ("left:" ++ hint) (text "5")
    else if ref = rightMethod then emitReturn ("right:" ++ hint) (text "7")
    else pure ()
  let machine := machine.setHeap heap
  let (equalString, equalMachine) ← runNormal
    (AbstractEquality.looseEqual hook (.object left) (text "5")) machine
  assert! equalString
  assert! emitted equalMachine = ["left:default"]
  let (equalNumber, _) ← runNormal
    (AbstractEquality.looseEqual hook (.object left)
      (.primitive (.number (JSNumber.parse (JSString.ofLeanString "5"))))) machine
  assert! equalNumber
  let (equalBool, _) ← runNormal
    (AbstractEquality.looseEqual hook (.object left) (.primitive (.boolean true))) machine
  assert! !equalBool
  let (nullObject, _) ← runNormal
    (AbstractEquality.looseEqual hook (.object left) (.primitive .null)) machine
  assert! !nullObject
  let (bigintString, _) ← runNormal
    (AbstractEquality.looseEqual hook (bigint 5) (text "5")) machine
  assert! bigintString
  let (objectBigint, _) ← runNormal
    (AbstractEquality.looseEqual hook (.object left) (bigint 5)) machine
  assert! objectBigint
  let (sameObject, _) ← runNormal
    (AbstractEquality.looseEqual hook (.object left) (.object left)) machine
  let (otherObject, _) ← runNormal
    (AbstractEquality.looseEqual hook (.object left) (.object right)) machine
  assert! sameObject && !otherObject

  let (sum, sumMachine) ← runNormal
    (AbstractEquality.add hook (.object left) (.object right)) machine
  assert! sum = text "57"
  assert! emitted sumMachine = ["left:default", "right:default"]
  let (ordered, orderedMachine) ← runNormal
    (AbstractEquality.lessThan hook (.object left) (.object right)) machine
  assert! ordered
  assert! emitted orderedMachine = ["left:number", "right:number"]
  let (greater, greaterMachine) ← runNormal
    (AbstractEquality.greaterThan hook (.object right) (.object left)) machine
  assert! greater
  assert! emitted greaterMachine = ["right:number", "left:number"]

  let throwingHook : BodyHook platform := fun ref _ arguments machine =>
    let event := if ref = leftMethod then "left" else "right"
    let next := machine.emit (.emitted (JSString.ofLeanString event))
    if ref = rightMethod then JSM.throwJS (bigint 88) next
    else JSM.returnJS (arguments[0]?.getD undefined) next
  match AbstractEquality.add throwingHook (.object left) (.object right) machine with
  | .done (.thrown value) next =>
      assert! value = bigint 88
      assert! emitted next = ["left", "right"]
  | _ => assert! false
  match AbstractEquality.lessThan throwingHook (.object left) (.object right) machine with
  | .done (.thrown value) next =>
      assert! value = bigint 88
      assert! emitted next = ["left", "right"]
  | _ => assert! false

private def testHasInstance : IO Unit := do
  let machine := Machine.initial platform 10000
  let (objectPrototype, heap) ← allocateObject machine.heap
  let (constructor, prototype, heap) ← match heap.allocateConstructorPair
      machine.globalEnv none (some objectPrototype) with
    | .ok result => pure result
    | _ => throw (IO.userError "constructor allocation failed")
  let (instanceRef, heap) ← allocateObject heap (some prototype)
  let (forged, heap) ← allocateObject heap (some objectPrototype)
  let machine := machine.setHeap heap
  let (fallback, _) ← runNormal
    (Instanceof.instanceofOperator fallthrough (.object instanceRef) (.object constructor)) machine
  let (forgedResult, _) ← runNormal
    (Instanceof.instanceofOperator fallthrough (.object forged) (.object constructor)) machine
  assert! fallback && !forgedResult

  let (method, machine) ← allocateFunction machine
  let (getter, machine) ← allocateFunction machine
  let heap ← define machine.heap constructor (.symbol (.wellKnown .hasInstance)) {
    get := .present (some getter), configurable := .present true }
  let hook : BodyHook platform := fun ref actual arguments =>
    if ref = getter then
      if actual = .object constructor then emitReturn "get" (.object method)
      else JSM.throwJS (bigint 70)
    else if ref = method then
      if actual = .object constructor && arguments[0]? = some (.object forged) then
        emitReturn "call" (.object forged)
      else JSM.throwJS (bigint 71)
    else pure ()
  let (custom, customMachine) ← runNormal
    (Instanceof.instanceofOperator hook (.object forged) (.object constructor))
    (machine.setHeap heap)
  assert! custom
  assert! emitted customMachine = ["get", "call"]

  let falseHook : BodyHook platform := fun ref _ _ =>
    if ref = getter then JSM.returnJS (.object method)
    else JSM.returnJS (.primitive (.boolean false))
  let (customFalse, _) ← runNormal
    (Instanceof.instanceofOperator falseHook (.object forged) (.object constructor))
    (machine.setHeap heap)
  assert! !customFalse

  let throwingMethodHook : BodyHook platform := fun ref _ _ current =>
    if ref = getter then emitReturn "get" (.object method) current
    else JSM.throwJS (bigint 73)
      (current.emit (.emitted (JSString.ofLeanString "call-throw")))
  match Instanceof.instanceofOperator throwingMethodHook (.object forged) (.object constructor)
      (machine.setHeap heap) with
  | .done (.thrown value) next =>
      assert! value = bigint 73
      assert! emitted next = ["get", "call-throw"]
  | _ => assert! false

  let throwingGetter : BodyHook platform := fun ref _ _ machine =>
    if ref = getter then JSM.throwJS (bigint 72)
      (machine.emit (.emitted (JSString.ofLeanString "get-throw")))
    else .done (.normal ()) machine
  match Instanceof.instanceofOperator throwingGetter (.object forged) (.object constructor)
      (machine.setHeap heap) with
  | .done (.thrown value) next =>
      assert! value = bigint 72
      assert! emitted next = ["get-throw"]
  | _ => assert! false
  let nonCallableHeap ← define heap constructor (.symbol (.wellKnown .hasInstance)) {
    value := .present (bigint 1) }
  match Instanceof.instanceofOperator fallthrough (.object forged) (.object constructor)
      (machine.setHeap nonCallableHeap) with
  | .done (.thrown _) _ => pure ()
  | _ => assert! false
  match Instanceof.instanceofOperator fallthrough (.object forged) (bigint 1) machine with
  | .done (.thrown _) _ => pure ()
  | _ => assert! false

private def testPrototypeDepth : IO Unit := do
  let machine := Machine.initial platform 100000
  let (root, heap) ← allocateObject machine.heap
  let mut heap := heap
  let mut leaf := root
  for _ in [0:200] do
    let (next, nextHeap) ← allocateObject heap (some leaf)
    heap := nextHeap
    leaf := next
  let (constructor, _, withConstructor) ← match heap.allocateConstructorPair machine.globalEnv none none with
    | .ok result => pure result
    | _ => throw (IO.userError "constructor allocation failed")
  let finalHeap ← define withConstructor constructor (key "prototype") {
    value := .present (.object root) }
  let (result, _) ← runNormal
    (Instanceof.ordinaryHasInstance fallthrough constructor (.object leaf)) (machine.setHeap finalHeap)
  assert! result

def run : IO Unit := do
  testOrdinaryToPrimitive
  testExoticToPrimitiveAndConversions
  testGetterThrowsAndGetMethod
  testToObject
  testRealmConfiguration
  testEqualityAndOperators
  testHasInstance
  testPrototypeDepth

#eval run

end TSLean.JS.AbstractOperationsTests
