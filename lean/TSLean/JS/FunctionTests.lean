import TSLean.JS.Construct
import TSLean.JS.Instanceof
import TSLean.JS.Typeof

namespace TSLean.JS.FunctionTests

private def platform : Platform := ScriptedPlatform.make {
  times := #[], randoms := #[], fetches := #[]
}

private def key (text : String) : PropertyKey := .string (JSString.ofLeanString text)
private def bigint (value : Nat) : Value := .primitive (.bigint value)
private def undefined : Value := .primitive .undefined
private def fallthrough : BodyHook platform := fun _ _ _ => pure ()

private def initial : IO (RefId × RefId × Machine platform) := do
  let machine := Machine.initial platform 100000
  let (objectPrototype, heap) ← match machine.heap.allocate with
    | .ok result => pure result
    | .error _ => throw (IO.userError "object prototype allocation failed")
  let (functionPrototype, heap) ← match heap.allocate (some objectPrototype) with
    | .ok result => pure result
    | .error _ => throw (IO.userError "function prototype allocation failed")
  pure (objectPrototype, functionPrototype, machine.setHeap heap)

private def runNormal (action : JSM platform α) (machine : Machine platform) :
    IO (α × Machine platform) :=
  match action machine with
  | .done (.normal value) next => pure (value, next)
  | _ => throw (IO.userError "expected normal completion")

private def allocateObject (heap : Heap) (prototype : Option RefId := none) : IO (RefId × Heap) :=
  match heap.allocate prototype with
  | .ok result => pure result
  | .error _ => throw (IO.userError "object allocation failed")

private def own (heap : Heap) (ref : RefId) (name : String) : Option PropertyDescriptor :=
  match OrdinaryObject.getOwnProperty heap ref (key name) with
  | .ok descriptor => descriptor
  | .error _ => none

private def define (heap : Heap) (ref : RefId) (name : String) (update : DescriptorUpdate) : IO Heap :=
  match heap.defineOwnProperty ref (key name) update with
  | .ok (true, next) => pure next
  | _ => throw (IO.userError s!"property definition failed: {name}")

private def testFunctionMetadata : IO Unit := do
  let (objectPrototype, functionPrototype, machine) ← initial
  let (first, machine) ← runNormal
    (Function.allocateOrdinary machine.globalEnv (some functionPrototype)) machine
  let (second, machine) ← runNormal
    (Function.allocateOrdinary machine.globalEnv (some functionPrototype)) machine
  let (arrow, machine) ← runNormal
    (Function.allocateArrow machine.globalEnv (some functionPrototype) undefined) machine
  let ((constructor, prototype), machine) ← runNormal
    (Function.allocateConstructor machine.globalEnv (some functionPrototype) (some objectPrototype)) machine
  assert! first != second
  match machine.heap.functionSlots? first, machine.heap.functionSlots? second with
  | .ok (some left), .ok (some right) =>
      assert! left.functionId != right.functionId
      assert! left.environment = machine.globalEnv
  | _, _ => assert! false
  assert! machine.heap.isCallable arrow matches .ok true
  assert! machine.heap.isConstructor arrow matches .ok false
  assert! (own machine.heap arrow "prototype").isNone
  match own machine.heap constructor "prototype", own machine.heap prototype "constructor" with
  | some (.data forward), some (.data backward) =>
      assert! forward.value = .object prototype
      assert! forward.writable && !forward.enumerable && !forward.configurable
      assert! backward.value = .object constructor
      assert! backward.writable && !backward.enumerable && backward.configurable
  | _, _ => assert! false
  assert! machine.isWellFormed

private def testArrowLexicalThis : IO Unit := do
  let (_, functionPrototype, machine) ← initial
  let (capturedObject, heap) ← allocateObject machine.heap
  let machine := machine.setHeap heap
  let (primitiveArrow, machine) ← runNormal
    (Function.allocateArrow machine.globalEnv (some functionPrototype) (bigint 41)) machine
  let (objectArrow, machine) ← runNormal
    (Function.allocateArrow machine.globalEnv (some functionPrototype) (.object capturedObject)) machine
  let hook : BodyHook platform := fun _ actual _ => JSM.returnJS actual
  let (primitiveThis, machine) ← runNormal
    (Call.call hook primitiveArrow (.primitive (.boolean false)) #[]) machine
  let (objectThis, machine) ← runNormal
    (Call.call hook objectArrow (bigint 99) #[]) machine
  assert! primitiveThis = bigint 41
  assert! objectThis = .object capturedObject
  assert! machine.isWellFormed
  match machine.heap.functionSlots? objectArrow with
  | .ok (some slots) => assert! slots.lexicalThis = some (.object capturedObject)
  | _ => assert! false
  match Function.allocateArrow machine.globalEnv (some functionPrototype) (.object ⟨999⟩) machine with
  | .fault (.runtime (.heap (.invalidRef ref))) next =>
      assert! ref = ⟨999⟩
      assert! next.heap.size = machine.heap.size
  | _ => assert! false

private def testDanglingBodyValues : IO Unit := do
  let (_, functionPrototype, machine) ← initial
  let (returner, machine) ← runNormal
    (Function.allocateOrdinary machine.globalEnv (some functionPrototype)) machine
  let (thrower, machine) ← runNormal
    (Function.allocateOrdinary machine.globalEnv (some functionPrototype)) machine
  let hook : BodyHook platform := fun ref _ _ current =>
    let next := current.emit (.emitted (JSString.ofLeanString "body-effect"))
    if ref = returner then JSM.returnJS (.object ⟨999⟩) next
    else JSM.throwJS (.object ⟨998⟩) next
  match Call.call hook returner undefined #[] machine with
  | .fault (.runtime (.danglingEscapingValue ref)) next =>
      assert! ref = ⟨999⟩
      assert! next.trace = [.emitted (JSString.ofLeanString "body-effect")]
  | _ => assert! false
  match Call.call hook thrower undefined #[] machine with
  | .fault (.runtime (.danglingEscapingValue ref)) next =>
      assert! ref = ⟨998⟩
      assert! next.trace = [.emitted (JSString.ofLeanString "body-effect")]
  | _ => assert! false

private def testCheckedCallCompletions : IO Unit := do
  let (_, functionPrototype, machine) ← initial
  let (fallthroughRef, machine) ← runNormal
    (Function.allocateOrdinary machine.globalEnv (some functionPrototype)) machine
  let (returnRef, machine) ← runNormal
    (Function.allocateOrdinary machine.globalEnv (some functionPrototype)) machine
  let (throwRef, machine) ← runNormal
    (Function.allocateOrdinary machine.globalEnv (some functionPrototype)) machine
  let (breakRef, machine) ← runNormal
    (Function.allocateOrdinary machine.globalEnv (some functionPrototype)) machine
  let hook : BodyHook platform := fun ref _ _ =>
    if ref = returnRef then JSM.returnJS (bigint 7)
    else if ref = throwRef then JSM.throwJS (bigint 8)
    else if ref = breakRef then JSM.breakJS
    else pure ()
  let (fellThrough, machine) ← runNormal (Call.call hook fallthroughRef undefined #[]) machine
  let (returned, machine) ← runNormal (Call.call hook returnRef undefined #[]) machine
  assert! fellThrough = undefined
  assert! returned = bigint 7
  match Call.call hook throwRef undefined #[] machine with
  | .done (.thrown value) _ => assert! value = bigint 8
  | _ => assert! false
  match Call.call hook breakRef undefined #[] machine with
  | .fault (.runtime .escapingFunctionControl) _ => pure ()
  | _ => assert! false

private def testClassElementsAndCallRejection : IO Unit := do
  let (objectPrototype, functionPrototype, machine) ← initial
  let definitions := #[
    { key := key "method", placement := .instance, kind := .method },
    { key := key "value", placement := .instance, kind := .getter },
    { key := key "value", placement := .instance, kind := .setter },
    { key := key "staticMethod", placement := .static, kind := .method }]
  let (allocation, machine) ← runNormal
    (Function.allocateClass fallthrough machine.globalEnv functionPrototype objectPrototype
      .base definitions) machine
  match own machine.heap allocation.constructor "prototype" with
  | some (.data descriptor) =>
      assert! !descriptor.writable && !descriptor.enumerable && !descriptor.configurable
  | _ => assert! false
  match own machine.heap allocation.prototype "method", own machine.heap allocation.prototype "value" with
  | some (.data method), some (.accessor accessor) =>
      assert! method.writable && !method.enumerable && method.configurable
      assert! accessor.get.isSome && accessor.set.isSome
      assert! !accessor.enumerable && accessor.configurable
  | _, _ => assert! false
  match allocation.elements[1]?, allocation.elements[2]? with
  | some getter, some setter =>
      let hook : BodyHook platform := fun ref _ _ =>
        if ref = getter then JSM.returnJS (bigint 12)
        else if ref = setter then JSM.returnJS (bigint 13)
        else pure ()
      let (got, machine) ← runNormal
        (ObjectAccess.get hook allocation.prototype (key "value") (.object allocation.prototype)) machine
      let (set, _) ← runNormal
        (ObjectAccess.set hook allocation.prototype (key "value") (bigint 2)
          (.object allocation.prototype)) machine
      assert! got = bigint 12
      assert! set
  | _, _ => assert! false
  match allocation.elements[0]?, allocation.elements[3]? with
  | some instanceMethod, some staticMethod =>
      match machine.heap.functionSlots? instanceMethod, machine.heap.functionSlots? staticMethod with
      | .ok (some instanceSlots), .ok (some staticSlots) =>
          assert! instanceSlots.homeObject = some allocation.prototype
          assert! staticSlots.homeObject = some allocation.constructor
      | _, _ => assert! false
  | _, _ => assert! false
  assert! Value.typeof machine.heap (.object allocation.constructor) matches .ok .function
  assert! machine.isWellFormed
  match Call.call fallthrough allocation.constructor undefined #[] machine with
  | .done (.thrown _) next => assert! next.heap.size = machine.heap.size
  | _ => assert! false
  let (target, heap) ← allocateObject machine.heap
  let heap ← define heap target "classGetter" {
    get := .present (some allocation.constructor) }
  match ObjectAccess.get fallthrough target (key "classGetter") (.object target) (machine.setHeap heap) with
  | .done (.thrown _) next => assert! next.heap.size = heap.size
  | _ => assert! false

private def heritageHook (getter objectPrototype : RefId) (returnsNull : Bool) : BodyHook platform :=
  fun ref _ _ =>
    if ref = getter then
      if returnsNull then JSM.returnJS (.primitive .null)
      else JSM.returnJS (.object objectPrototype)
    else pure ()

private def testHeritageAccessorsAndNull : IO Unit := do
  let (objectPrototype, functionPrototype, machine) ← initial
  let (getter, machine) ← runNormal
    (Function.allocateOrdinary machine.globalEnv (some functionPrototype)) machine
  let (superclass, machine) ← runNormal
    (Function.allocateBareConstructor machine.globalEnv (some functionPrototype)) machine
  let heap ← define machine.heap superclass "prototype" { get := .present (some getter) }
  let hook := heritageHook getter objectPrototype false
  let (derived, machine) ← runNormal
    (Function.allocateClass hook machine.globalEnv functionPrototype objectPrototype
      (.extends superclass)) (machine.setHeap heap)
  match machine.heap.get? derived.prototype with
  | .ok prototype => assert! prototype.prototype = some objectPrototype
  | _ => assert! false

  let (inheritedSuperclass, machine) ← runNormal
    (Function.allocateBareConstructor machine.globalEnv (some functionPrototype)) machine
  let inheritedHeap ← define machine.heap functionPrototype "prototype" { get := .present (some getter) }
  let (nullDerived, machine) ← runNormal
    (Function.allocateClass (heritageHook getter objectPrototype true) machine.globalEnv
      functionPrototype objectPrototype (.extends inheritedSuperclass)) (machine.setHeap inheritedHeap)
  match machine.heap.get? nullDerived.prototype with
  | .ok prototype => assert! prototype.prototype = none
  | _ => assert! false
  let (explicitNull, machine) ← runNormal
    (Function.allocateClass fallthrough machine.globalEnv functionPrototype objectPrototype .null) machine
  match machine.heap.get? explicitNull.prototype with
  | .ok prototype => assert! prototype.prototype = none
  | _ => assert! false
  let (base, machine) ← runNormal
    (Function.allocateClass fallthrough machine.globalEnv functionPrototype objectPrototype .base) machine
  let (childClass, machine) ← runNormal
    (Function.allocateClass fallthrough machine.globalEnv functionPrototype objectPrototype
      (.extends base.constructor)) machine
  let (instanceRef, heap) ← allocateObject machine.heap (some childClass.prototype)
  let (isChild, machine) ← runNormal
    (Instanceof.ordinaryHasInstance fallthrough childClass.constructor (.object instanceRef))
    (machine.setHeap heap)
  let (isBase, _) ← runNormal
    (Instanceof.ordinaryHasInstance fallthrough base.constructor (.object instanceRef)) machine
  assert! isChild && isBase

private def testHeritagePrimitiveRejection : IO Unit := do
  let (objectPrototype, functionPrototype, machine) ← initial
  let (getter, machine) ← runNormal
    (Function.allocateOrdinary machine.globalEnv (some functionPrototype)) machine
  let (superclass, machine) ← runNormal
    (Function.allocateBareConstructor machine.globalEnv (some functionPrototype)) machine
  let heap ← define machine.heap superclass "prototype" { get := .present (some getter) }
  let hook : BodyHook platform := fun ref _ _ =>
    if ref = getter then JSM.returnJS (bigint 1) else pure ()
  match (Function.allocateClass hook machine.globalEnv functionPrototype objectPrototype
      (.extends superclass)) (machine.setHeap heap) with
  | .done (.thrown _) next => assert! next.heap.size = heap.size
  | _ => assert! false

private def constructHook (constructor overrideObject throwRef breakRef : RefId) : BodyHook platform :=
  fun ref thisValue _ =>
    if ref = constructor then
      match thisValue with
      | .object _ => pure ()
      | _ => JSM.throwJS (bigint 99)
    else if ref = overrideObject then JSM.returnJS (.object overrideObject)
    else if ref = throwRef then JSM.throwJS (bigint 4)
    else if ref = breakRef then JSM.continueJS
    else pure ()

private def testConstructionDispatch : IO Unit := do
  let (objectPrototype, functionPrototype, machine) ← initial
  let ((constructor, _), machine) ← runNormal
    (Function.allocateConstructor machine.globalEnv (some functionPrototype) (some objectPrototype)) machine
  let (arrow, machine) ← runNormal
    (Function.allocateArrow machine.globalEnv (some functionPrototype) undefined) machine
  let (overrideConstructor, machine) ← runNormal
    (Function.allocateBareConstructor machine.globalEnv (some functionPrototype)) machine
  let (throwConstructor, machine) ← runNormal
    (Function.allocateBareConstructor machine.globalEnv (some functionPrototype)) machine
  let (breakConstructor, machine) ← runNormal
    (Function.allocateBareConstructor machine.globalEnv (some functionPrototype)) machine
  let (primitiveConstructor, machine) ← runNormal
    (Function.allocateBareConstructor machine.globalEnv (some functionPrototype)) machine
  let (danglingReturn, machine) ← runNormal
    (Function.allocateBareConstructor machine.globalEnv (some functionPrototype)) machine
  let (danglingThrow, machine) ← runNormal
    (Function.allocateBareConstructor machine.globalEnv (some functionPrototype)) machine
  let (rollbackFallthrough, machine) ← runNormal
    (Function.allocateBareConstructor machine.globalEnv (some functionPrototype)) machine
  let (rollbackPrimitive, machine) ← runNormal
    (Function.allocateBareConstructor machine.globalEnv (some functionPrototype)) machine
  let rollbackHeap := machine.heap
  let baseHook := constructHook constructor overrideConstructor throwConstructor breakConstructor
  let hook : BodyHook platform := fun ref thisValue arguments =>
    if ref = primitiveConstructor then JSM.returnJS (bigint 5)
    else if ref = danglingReturn then fun current =>
      JSM.returnJS (.object ⟨999⟩)
        (current.emit (.emitted (JSString.ofLeanString "construct-return-effect")))
    else if ref = danglingThrow then fun current =>
      JSM.throwJS (.object ⟨998⟩)
        (current.emit (.emitted (JSString.ofLeanString "construct-throw-effect")))
    else if ref = rollbackFallthrough then fun current =>
      .done (.normal ()) ((current.setHeap rollbackHeap).emit
        (.emitted (JSString.ofLeanString "rollback-fallthrough")))
    else if ref = rollbackPrimitive then fun current =>
      JSM.returnJS (bigint 6) ((current.setHeap rollbackHeap).emit
        (.emitted (JSString.ofLeanString "rollback-primitive")))
    else baseHook ref thisValue arguments
  let (instanceValue, machine) ← runNormal
    (Construct.construct hook constructor objectPrototype #[]) machine
  assert! instanceValue matches .object _
  let (override, machine) ← runNormal
    (Construct.construct hook overrideConstructor objectPrototype #[]) machine
  assert! override = .object overrideConstructor
  let (primitiveOverride, machine) ← runNormal
    (Construct.construct hook primitiveConstructor objectPrototype #[]) machine
  assert! primitiveOverride matches .object _
  match Construct.construct hook throwConstructor objectPrototype #[] machine with
  | .done (.thrown value) _ => assert! value = bigint 4
  | _ => assert! false
  match Construct.construct hook breakConstructor objectPrototype #[] machine with
  | .fault (.runtime .escapingFunctionControl) _ => pure ()
  | _ => assert! false
  match Construct.construct hook danglingReturn objectPrototype #[] machine with
  | .fault (.runtime (.danglingEscapingValue ref)) next =>
      assert! ref = ⟨999⟩
      assert! next.heap.size = machine.heap.size + 1
      assert! next.trace = [.emitted (JSString.ofLeanString "construct-return-effect")]
  | _ => assert! false
  match Construct.construct hook danglingThrow objectPrototype #[] machine with
  | .fault (.runtime (.danglingEscapingValue ref)) next =>
      assert! ref = ⟨998⟩
      assert! next.heap.size = machine.heap.size + 1
      assert! next.trace = [.emitted (JSString.ofLeanString "construct-throw-effect")]
  | _ => assert! false
  match Construct.construct hook rollbackFallthrough objectPrototype #[] machine with
  | .fault (.runtime (.danglingEscapingValue _)) next =>
      assert! next.heap.size = rollbackHeap.size
      assert! next.trace = [.emitted (JSString.ofLeanString "rollback-fallthrough")]
  | _ => assert! false
  match Construct.construct hook rollbackPrimitive objectPrototype #[] machine with
  | .fault (.runtime (.danglingEscapingValue _)) next =>
      assert! next.heap.size = rollbackHeap.size
      assert! next.trace = [.emitted (JSString.ofLeanString "rollback-primitive")]
  | _ => assert! false
  match Construct.construct hook arrow objectPrototype #[] machine with
  | .done (.thrown _) _ => pure ()
  | _ => assert! false
  let (baseClass, machine) ← runNormal
    (Function.allocateClass fallthrough machine.globalEnv functionPrototype objectPrototype .base) machine
  let (_, machine) ← runNormal
    (Construct.construct fallthrough baseClass.constructor objectPrototype #[]) machine
  let (derivedClass, machine) ← runNormal
    (Function.allocateClass fallthrough machine.globalEnv functionPrototype objectPrototype
      (.extends baseClass.constructor)) machine
  match Construct.construct fallthrough derivedClass.constructor objectPrototype #[] machine with
  | .fault (.runtime (.unsupportedDerivedConstruction ref)) _ => assert! ref = derivedClass.constructor
  | _ => assert! false

private def testConstructionPrototypeSelection : IO Unit := do
  let (objectPrototype, functionPrototype, machine) ← initial
  let ((constructor, _), machine) ← runNormal
    (Function.allocateConstructor machine.globalEnv (some functionPrototype) (some objectPrototype)) machine
  let (replacement, heap) ← allocateObject machine.heap (some objectPrototype)
  let heap ← define heap constructor "prototype" { value := .present (.object replacement) }
  let (instanceValue, machine) ← runNormal
    (Construct.construct fallthrough constructor objectPrototype #[]) (machine.setHeap heap)
  match instanceValue with
  | .object instanceRef =>
      match machine.heap.get? instanceRef with
      | .ok object => assert! object.prototype = some replacement
      | _ => assert! false
  | _ => assert! false
  let primitiveHeap ← define machine.heap constructor "prototype" { value := .present (.primitive .null) }
  let (fallbackValue, machine) ← runNormal
    (Construct.construct fallthrough constructor objectPrototype #[]) (machine.setHeap primitiveHeap)
  match fallbackValue with
  | .object instanceRef =>
      match machine.heap.get? instanceRef with
      | .ok object => assert! object.prototype = some objectPrototype
      | _ => assert! false
  | _ => assert! false
  let (getter, machine) ← runNormal
    (Function.allocateOrdinary machine.globalEnv (some functionPrototype)) machine
  let (accessorConstructor, machine) ← runNormal
    (Function.allocateBareConstructor machine.globalEnv (some functionPrototype)) machine
  let accessorHeap ← define machine.heap accessorConstructor "prototype" {
    get := .present (some getter) }
  let (throwingConstructor, machine) ← runNormal
    (Function.allocateBareConstructor machine.globalEnv (some functionPrototype)) (machine.setHeap accessorHeap)
  let accessorHeap ← define machine.heap throwingConstructor "prototype" {
    get := .present (some getter) }
  let hook : BodyHook platform := fun ref actual _ current =>
    if ref = getter then
      let next := current.emit (.emitted (JSString.ofLeanString "prototype-getter"))
      if actual = .object accessorConstructor then JSM.returnJS (.object replacement) next
      else JSM.throwJS (bigint 77) next
    else .done (.normal ()) current
  let (accessorValue, machine) ← runNormal
    (Construct.construct hook accessorConstructor ⟨999⟩ #[]) (machine.setHeap accessorHeap)
  match accessorValue with
  | .object instanceRef =>
      match machine.heap.get? instanceRef with
      | .ok object => assert! object.prototype = some replacement
      | _ => assert! false
  | _ => assert! false
  assert! machine.trace = [.emitted (JSString.ofLeanString "prototype-getter")]
  match Construct.construct hook throwingConstructor ⟨999⟩ #[] machine with
  | .done (.thrown value) next =>
      assert! value = bigint 77
      assert! next.trace = [
        .emitted (JSString.ofLeanString "prototype-getter"),
        .emitted (JSString.ofLeanString "prototype-getter")]
  | _ => assert! false

private def accessorHook (getter setter target receiver : RefId) : BodyHook platform :=
  fun ref actual arguments machine =>
    if ref = getter then
      let event := if actual = .object receiver then "get:receiver" else "get:wrong"
      match machine.heap.createDataProperty target (key "getterState") (bigint 1) with
      | .ok (true, heap) => JSM.returnJS (bigint 7) ((machine.setHeap heap).emit
          (.emitted (JSString.ofLeanString event)))
      | _ => .fault (.runtime (.heap .cycleOrFuelExhausted)) machine
    else if ref = setter then
      let argument := arguments[0]?.getD undefined
      let event := if actual = .object receiver then "set:receiver" else "set:wrong"
      match machine.heap.createDataProperty target (key "setterState") argument with
      | .ok (true, heap) => JSM.returnJS (bigint 100) ((machine.setHeap heap).emit
          (.emitted (JSString.ofLeanString event)))
      | _ => .fault (.runtime (.heap .cycleOrFuelExhausted)) machine
    else .done (.normal ()) machine

private def testAccessorReceiverAndOrder : IO Unit := do
  let (_, functionPrototype, machine) ← initial
  let (target, heap) ← allocateObject machine.heap
  let (receiver, heap) ← allocateObject heap (some target)
  let machine := machine.setHeap heap
  let (getter, machine) ← runNormal
    (Function.allocateOrdinary machine.globalEnv (some functionPrototype)) machine
  let (setter, machine) ← runNormal
    (Function.allocateOrdinary machine.globalEnv (some functionPrototype)) machine
  let heap ← define machine.heap target "accessor" {
    get := .present (some getter), set := .present (some setter), configurable := .present true }
  let hook := accessorHook getter setter target receiver
  let (got, machine) ← runNormal
    (ObjectAccess.get hook receiver (key "accessor") (.object receiver)) (machine.setHeap heap)
  let (set, machine) ← runNormal
    (ObjectAccess.set hook receiver (key "accessor") (bigint 9) (.object receiver)) machine
  assert! got = bigint 7
  assert! set
  match own machine.heap target "setterState" with
  | some (.data descriptor) => assert! descriptor.value = bigint 9
  | _ => assert! false
  assert! machine.trace = [
    .emitted (JSString.ofLeanString "get:receiver"),
    .emitted (JSString.ofLeanString "set:receiver")]

private def testThrowingAccessorsPreserveState : IO Unit := do
  let (_, functionPrototype, machine) ← initial
  let (target, heap) ← allocateObject machine.heap
  let machine := machine.setHeap heap
  let (getter, machine) ← runNormal
    (Function.allocateOrdinary machine.globalEnv (some functionPrototype)) machine
  let (setter, machine) ← runNormal
    (Function.allocateOrdinary machine.globalEnv (some functionPrototype)) machine
  let heap ← define machine.heap target "x" {
    get := .present (some getter), set := .present (some setter) }
  let hook : BodyHook platform := fun ref _ _ current =>
    let stateKey := if ref = getter then "getterBeforeThrow" else "setterBeforeThrow"
    match current.heap.createDataProperty target (key stateKey) (bigint 1) with
    | .ok (true, nextHeap) => JSM.throwJS (bigint 99) (current.setHeap nextHeap)
    | _ => .fault (.runtime (.heap .cycleOrFuelExhausted)) current
  match ObjectAccess.get hook target (key "x") (.object target) (machine.setHeap heap) with
  | .done (.thrown _) next => assert! (own next.heap target "getterBeforeThrow" matches some (.data _))
  | _ => assert! false
  match ObjectAccess.set hook target (key "x") (bigint 2) (.object target) (machine.setHeap heap) with
  | .done (.thrown _) next => assert! (own next.heap target "setterBeforeThrow" matches some (.data _))
  | _ => assert! false

private def testReceiverOwnConflicts : IO Unit := do
  let (_, functionPrototype, machine) ← initial
  let (parent, heap) ← allocateObject machine.heap
  let (child, heap) ← allocateObject heap (some parent)
  let heap ← define heap parent "x" { value := .present (bigint 1), writable := .present true }
  let heap ← define heap child "x" {
    value := .present (bigint 2), writable := .present false, configurable := .present true }
  let (blocked, machine) ← runNormal
    (ObjectAccess.set fallthrough child (key "x") (bigint 3) (.object child)) (machine.setHeap heap)
  assert! !blocked
  let heap ← match machine.heap.deleteProperty child (key "x") with
    | .ok (true, next) => pure next
    | _ => throw (IO.userError "conflict delete failed")
  let (getter, machine) ← runNormal
    (Function.allocateOrdinary machine.globalEnv (some functionPrototype)) (machine.setHeap heap)
  let heap ← define machine.heap child "x" { get := .present (some getter) }
  let (accessorBlocked, _) ← runNormal
    (ObjectAccess.set fallthrough child (key "x") (bigint 3) (.object child)) (machine.setHeap heap)
  assert! !accessorBlocked

private def testTypeofInstanceofAndFaults : IO Unit := do
  let (objectPrototype, functionPrototype, machine) ← initial
  let ((constructor, prototype), machine) ← runNormal
    (Function.allocateConstructor machine.globalEnv (some functionPrototype) (some objectPrototype)) machine
  let (instanceRef, heap) ← allocateObject machine.heap (some prototype)
  let machine := machine.setHeap heap
  let (yes, machine) ← runNormal
    (Instanceof.ordinaryHasInstance fallthrough constructor (.object instanceRef)) machine
  let (forged, heap) ← allocateObject machine.heap (some objectPrototype)
  let (no, machine) ← runNormal
    (Instanceof.ordinaryHasInstance fallthrough constructor (.object forged)) (machine.setHeap heap)
  assert! yes && !no
  assert! Value.typeof machine.heap (.object constructor) matches .ok .function
  assert! Value.typeof machine.heap (.object objectPrototype) matches .ok .object
  assert! Value.typeof machine.heap (.primitive .undefined) matches .ok .undefined
  assert! Value.typeof machine.heap (.primitive .null) matches .ok .object
  assert! Value.typeof machine.heap (.primitive (.boolean true)) matches .ok .boolean
  assert! Value.typeof machine.heap (.primitive (.number JSNumber.positiveZero)) matches .ok .number
  assert! Value.typeof machine.heap (.primitive (.string (JSString.ofLeanString "x"))) matches .ok .string
  assert! Value.typeof machine.heap (.primitive (.bigint 1)) matches .ok .bigint
  assert! Value.typeof machine.heap (.primitive (.symbol (.allocated 1))) matches .ok .symbol
  assert! Value.typeof machine.heap (.object ⟨999⟩) matches .error (.invalidRef _)
  match Function.allocateArrow ⟨999⟩ (some functionPrototype) undefined machine with
  | .fault (.runtime (.invalidEnvironment _)) next => assert! next.heap.size = machine.heap.size
  | _ => assert! false

private def testValidityChecks : IO Unit := do
  let (_, functionPrototype, machine) ← initial
  let (functionRef, machine) ← runNormal
    (Function.allocateOrdinary machine.globalEnv (some functionPrototype)) machine
  assert! machine.heap.isWellFormed
  assert! machine.isWellFormed
  let slots := machine.heap.functionSlotList
  assert! slots.length = machine.heap.functionCount
  assert! decide (slots.map (·.functionId)).Nodup
  match machine.heap.allocateFunction ⟨999⟩ .ordinary false (some functionPrototype) with
  | .ok (_, heap) =>
      assert! heap.isWellFormed
      assert! !(machine.setHeap heap).isWellFormed
      assert! (heap.functionSlots? functionRef matches .ok (some _))
  | .error _ => assert! false

private def testFunctionModeMatrix : IO Unit := do
  let (_, _, machine) ← initial
  let (captured, heap) ← allocateObject machine.heap
  assert! heap.isWellFormed
  for kind in [FunctionKind.ordinary, .arrow, .classConstructor] do
    for constructible in [false, true] do
      for lexicalThis in [none, some undefined] do
        let supported := kind = .classConstructor && constructible && lexicalThis.isNone
        if !supported then
          match heap.allocateFunction machine.globalEnv kind constructible none none .derived lexicalThis with
          | .error .invalidFunctionMetadata => pure ()
          | _ => throw (IO.userError "invalid derived function mode accepted")
  assert! heap.isWellFormed
  let valid : List (FunctionKind × Bool × ConstructorMode × Option Value) := [
    (.ordinary, false, .base, none),
    (.ordinary, true, .base, none),
    (.classConstructor, true, .base, none),
    (.arrow, false, .base, some (bigint 1)),
    (.arrow, false, .base, some (.object captured)),
    (.classConstructor, true, .derived, none)]
  let mut heap := heap
  for entry in valid do
    heap ← match heap.allocateFunction machine.globalEnv entry.1 entry.2.1 none none
        entry.2.2.1 entry.2.2.2 with
      | .ok (_, next) => pure next
      | .error _ => throw (IO.userError "valid function mode rejected")
    assert! heap.isWellFormed

private def run : IO Unit := do
  testFunctionMetadata
  testArrowLexicalThis
  testDanglingBodyValues
  testCheckedCallCompletions
  testClassElementsAndCallRejection
  testHeritageAccessorsAndNull
  testHeritagePrimitiveRejection
  testConstructionDispatch
  testConstructionPrototypeSelection
  testAccessorReceiverAndOrder
  testThrowingAccessorsPreserveState
  testReceiverOwnConflicts
  testTypeofInstanceofAndFaults
  testValidityChecks
  testFunctionModeMatrix

#eval run

end TSLean.JS.FunctionTests
