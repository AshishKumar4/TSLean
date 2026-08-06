import TSLean.JS.Copy
import TSLean.JS.Typeof

namespace TSLean.JS.CopyTests

private def platform : Platform := ScriptedPlatform.make { times := #[], randoms := #[], fetches := #[] }
private def key (text : String) : PropertyKey := .string (JSString.ofLeanString text)
private def bigint (value : Nat) : Value := .primitive (.bigint value)

private def runNormal (action : JSM platform α) (machine : Machine platform) : IO (α × Machine platform) :=
  match action machine with
  | .done (.normal value) next => pure (value, next)
  | _ => throw (IO.userError "expected normal completion")

private def allocateObject (heap : Heap) (prototype : Option RefId := none) : IO (RefId × Heap) :=
  match heap.allocate prototype with
  | .ok result => pure result
  | _ => throw (IO.userError "object allocation failed")

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

private def ownValue (heap : Heap) (ref : RefId) (propertyKey : PropertyKey) : Option Value :=
  match heap.getOwnProperty ref propertyKey with
  | .ok (some (.data descriptor)) => some descriptor.value
  | _ => none

private structure Fixture where
  target : RefId
  source : RefId
  getter : RefId
  throwingGetter : RefId
  setter : RefId
  nested : RefId
  machine : Machine platform

private def fixture : IO Fixture := do
  let machine := Machine.initial platform 10000
  let (prototype, heap) ← allocateObject machine.heap
  let heap ← data heap prototype (key "inherited") (bigint 99)
  let (target, heap) ← allocateObject heap
  let (source, heap) ← allocateObject heap (some prototype)
  let (nested, heap) ← allocateObject heap
  let (getter, heap) ← match heap.allocateFunction machine.globalEnv .ordinary false none with
    | .ok result => pure result | _ => throw (IO.userError "getter allocation failed")
  let (throwingGetter, heap) ← match heap.allocateFunction machine.globalEnv .ordinary false none with
    | .ok result => pure result | _ => throw (IO.userError "throwing getter allocation failed")
  let (setter, heap) ← match heap.allocateFunction machine.globalEnv .ordinary false none with
    | .ok result => pure result | _ => throw (IO.userError "setter allocation failed")
  let heap ← define heap source (key "fromGetter") {
    get := .present (some getter)
    enumerable := .present true
    configurable := .present true }
  let heap ← define heap source (key "throws") {
    get := .present (some throwingGetter)
    enumerable := .present false
    configurable := .present true }
  let heap ← data heap source (.symbol (.allocated 4)) (.object nested)
  let heap ← define heap target (key "fromGetter") {
    set := .present (some setter)
    enumerable := .present true
    configurable := .present true }
  pure ⟨target, source, getter, throwingGetter, setter, nested, machine.setHeap heap⟩

private def hook (fixture : Fixture) : BodyHook platform := fun function receiver arguments =>
  if function = fixture.getter then JSM.returnJS (bigint 7)
  else if function = fixture.throwingGetter then JSM.throwJS (bigint 500)
  else if function = fixture.setter then
    match receiver, arguments[0]? with
    | .object target, some value => fun machine =>
        match machine.heap.createDataProperty target (key "setterSeen") value with
        | .ok (true, heap) => .done (.returned (.primitive .undefined)) (machine.setHeap heap)
        | _ => .fault (.runtime (.heap .cycleOrFuelExhausted)) machine
    | _, _ => JSM.throwJS (bigint 501)
  else pure ()

private def testAssign : IO Unit := do
  let fixture ← fixture
  let source2Pair ← allocateObject fixture.machine.heap
  let source2 := source2Pair.1
  let heap ← data source2Pair.2 fixture.source (key "order") (bigint 1)
  let heap ← data heap source2 (key "order") (bigint 2)
  let machine := fixture.machine.setHeap heap
  let (result, machine) ← runNormal
    (Copy.objectAssign (hook fixture) (.object fixture.target)
      [.object fixture.source, .primitive .null, .primitive .undefined, .object source2]) machine
  assert! result = .object fixture.target
  assert! ownValue machine.heap fixture.target (key "setterSeen") = some (bigint 7)
  assert! ownValue machine.heap fixture.target (key "order") = some (bigint 2)
  assert! ownValue machine.heap fixture.target (.symbol (.allocated 4)) = some (.object fixture.nested)
  assert! ownValue machine.heap fixture.target (key "inherited") = none
  assert! machine.isWellFormed

private def testSpreadAndExclusions : IO Unit := do
  let fixture ← fixture
  let (spread, machine) ← runNormal
    (Copy.objectSpread (hook fixture) [.primitive .null, .object fixture.source]
      [.symbol (.allocated 4)]) fixture.machine
  assert! spread != fixture.target && spread != fixture.source
  assert! ownValue machine.heap spread (key "fromGetter") = some (bigint 7)
  assert! ownValue machine.heap spread (.symbol (.allocated 4)) = none
  assert! ownValue machine.heap spread (key "inherited") = none
  match machine.heap.get? spread with
  | .ok object => assert! object.prototype.isNone
  | _ => assert! false
  assert! machine.isWellFormed

private def testThrows : IO Unit := do
  let fixture ← fixture
  let heap ← define fixture.machine.heap fixture.source (key "throws") { enumerable := .present true }
  match Copy.objectAssign (hook fixture) (.object fixture.target) [.object fixture.source]
      (fixture.machine.setHeap heap) with
  | .done (.thrown value) _ => assert! value = bigint 500
  | _ => assert! false
  match Copy.objectAssign (hook fixture) (.primitive .undefined) [] fixture.machine with
  | .done (.thrown (.primitive (.string message))) _ =>
      assert! message.equal (JSString.ofLeanString "TypeError: cannot convert nullish target to object")
  | _ => assert! false
  match Copy.objectAssign (hook fixture) (.primitive .null) [] fixture.machine with
  | .done (.thrown (.primitive (.string message))) _ =>
      assert! message.equal (JSString.ofLeanString "TypeError: cannot convert nullish target to object")
  | _ => assert! false

private def testPrimitiveBoxing : IO Unit := do
  let fixture ← fixture
  let (boxedTarget, machine) ← runNormal
    (Copy.objectAssign (hook fixture) (.primitive (.boolean true))
      [.primitive (.string (JSString.ofLeanString "AZ")), .primitive (.number JSNumber.positiveZero),
        .primitive (.bigint 1), .primitive (.symbol (.allocated 8))]) fixture.machine
  let boxedRef ← match boxedTarget with
    | .object ref => pure ref
    | _ => throw (IO.userError "primitive target was not boxed")
  match machine.heap.get? boxedRef with
  | .ok object =>
      match object.kind with
      | .primitiveWrapper slots => assert! slots.value = .boolean true
      | _ => assert! false
  | _ => assert! false
  assert! ownValue machine.heap boxedRef (key "0") =
    some (.primitive (.string (JSString.ofLeanString "A")))
  assert! ownValue machine.heap boxedRef (key "1") =
    some (.primitive (.string (JSString.ofLeanString "Z")))
  match Value.typeof machine.heap (.object boxedRef) with
  | .ok .object => pure ()
  | _ => assert! false

  let (spread, machine) ← runNormal
    (Copy.objectSpread (hook fixture)
      [.primitive (.boolean false), .primitive (.string (JSString.ofLeanString "xy")),
        .primitive (.number JSNumber.positiveZero), .primitive (.bigint 2),
        .primitive (.symbol (.allocated 9)), .primitive .null, .primitive .undefined]) machine
  assert! ownValue machine.heap spread (key "0") =
    some (.primitive (.string (JSString.ofLeanString "x")))
  assert! ownValue machine.heap spread (key "1") =
    some (.primitive (.string (JSString.ofLeanString "y")))
  match machine.heap.ownPropertyKeys spread with
  | .ok keys => assert! keys = [key "0", key "1"]
  | _ => assert! false
  let mut machine := machine
  for primitive in [Primitive.string (JSString.ofLeanString "q"),
      .number JSNumber.positiveZero, .boolean false, .bigint 4, .symbol (.allocated 10)] do
    let (boxed, next) ← runNormal (Copy.objectAssign (hook fixture) (.primitive primitive) []) machine
    machine := next
    match boxed with
    | .object ref =>
        match machine.heap.get? ref with
        | .ok object =>
            match object.kind with
            | .primitiveWrapper slots => assert! slots.value = primitive
            | _ => assert! false
        | _ => assert! false
    | _ => assert! false
  assert! machine.isWellFormed

private def testStringWrapperDescriptors : IO Unit := do
  let machine := Machine.initial platform 10
  let (wrapper, heap) ← match machine.heap.allocatePrimitiveWrapper
      (.string (JSString.ofLeanString "ab")) with
    | .ok result => pure result
    | _ => throw (IO.userError "string wrapper allocation failed")
  match heap.ownPropertyKeys wrapper with
  | .ok keys => assert! keys = [key "0", key "1", key "length"]
  | _ => assert! false
  match heap.getOwnProperty wrapper (key "0"), heap.getOwnProperty wrapper (key "length") with
  | .ok (some (.data index)), .ok (some (.data length)) =>
      assert! !index.writable && index.enumerable && !index.configurable
      assert! !length.writable && !length.enumerable && !length.configurable
      assert! length.value = .primitive (.number (Heap.arrayLengthNumber 2))
  | _, _ => assert! false
  let astral : JSString := ⟨[UInt16.ofNat 0xd83d, UInt16.ofNat 0xde00]⟩
  let (astralWrapper, heap) ← match heap.allocatePrimitiveWrapper (.string astral) with
    | .ok result => pure result
    | _ => throw (IO.userError "astral string wrapper allocation failed")
  assert! ownValue heap astralWrapper (key "0") =
    some (.primitive (.string ⟨[UInt16.ofNat 0xd83d]⟩))
  assert! ownValue heap astralWrapper (key "1") =
    some (.primitive (.string ⟨[UInt16.ofNat 0xde00]⟩))
  assert! heap.isWellFormed

private def testCopyEntryValidation : IO Unit := do
  let machine := Machine.initial platform 10
  let (target, heap) ← allocateObject machine.heap
  let (source, heap) ← allocateObject heap
  let machine := machine.setHeap heap
  match Copy.copyDataProperties (fun _ _ _ => pure ()) ⟨99⟩ source [] machine with
  | .fault (.runtime (.heap (.invalidRef ref))) _ => assert! ref = ⟨99⟩
  | _ => assert! false
  match Copy.copyDataProperties (fun _ _ _ => pure ()) target ⟨98⟩ [key "excluded"] machine with
  | .fault (.runtime (.heap (.invalidRef ref))) _ => assert! ref = ⟨98⟩
  | _ => assert! false

private def testArrayTargetErrors : IO Unit := do
  let machine := Machine.initial platform 10
  let (target, heap) ← match machine.heap.allocateArray [] with
    | .ok result => pure result | _ => throw (IO.userError "array allocation failed")
  let (source, heap) ← allocateObject heap
  let heap ← data heap source (key "length")
    (.primitive (.number JSNumber.canonicalNaN))
  match Copy.copyDataProperties (fun _ _ _ => pure ()) target source [] (machine.setHeap heap) with
  | .done (.thrown (.primitive (.string message))) _ =>
      assert! message.equal (JSString.ofLeanString "RangeError: invalid array length")
  | _ => assert! false
  let heap ← define heap source (key "length") { value := .present (bigint 3) }
  match Copy.objectAssign (fun _ _ _ => pure ()) (.object target) [.object source]
      (machine.setHeap heap) with
  | .done (.thrown (.primitive (.string message))) _ =>
      assert! message.equal (JSString.ofLeanString "TypeError: array length must be a number")
  | _ => assert! false
  let (fixedTarget, heap) ← match heap.allocateArray [] with
    | .ok result => pure result | _ => throw (IO.userError "fixed array allocation failed")
  let heap ← match heap.defineOwnProperty fixedTarget (key "length") { writable := .present false } with
    | .ok (true, next) => pure next | _ => throw (IO.userError "fixed length failed")
  let (indexSource, heap) ← allocateObject heap
  let heap ← data heap indexSource (key "0") (bigint 1)
  match Copy.copyDataProperties (fun _ _ _ => pure ()) fixedTarget indexSource []
      (machine.setHeap heap) with
  | .done (.thrown (.primitive (.string message))) _ =>
      assert! message.equal (JSString.ofLeanString "TypeError: CreateDataProperty rejected")
  | _ => assert! false

private def testInvalidReferences : IO Unit := do
  let machine := Machine.initial platform 10
  match Copy.objectAssign (fun _ _ _ => pure ()) (.object ⟨9⟩) [] machine with
  | .fault (.runtime (.heap (.invalidRef ref))) _ => assert! ref = ⟨9⟩
  | _ => assert! false
  let (target, heap) ← allocateObject machine.heap
  match Copy.objectAssign (fun _ _ _ => pure ()) (.object target) [.object ⟨8⟩]
      (machine.setHeap heap) with
  | .fault (.runtime (.heap (.invalidRef ref))) _ => assert! ref = ⟨8⟩
  | _ => assert! false

private def run : IO Unit := do
  testAssign
  testSpreadAndExclusions
  testThrows
  testPrimitiveBoxing
  testStringWrapperDescriptors
  testCopyEntryValidation
  testArrayTargetErrors
  testInvalidReferences

#eval run

end TSLean.JS.CopyTests
