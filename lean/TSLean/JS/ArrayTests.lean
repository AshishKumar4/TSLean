import TSLean.JS.ArrayCopy

namespace TSLean.JS.ArrayTests

private def platform : Platform := ScriptedPlatform.make { times := #[], randoms := #[], fetches := #[] }
private def fallthrough : BodyHook platform := fun _ _ _ => pure ()
private def key (text : String) : PropertyKey := .string (JSString.ofLeanString text)
private def indexKey (index : Nat) : PropertyKey := .string (PropertyKey.arrayIndexString index)
private def bigint (value : Nat) : Value := .primitive (.bigint value)
private def undefined : Value := .primitive .undefined

private def runNormal (action : JSM platform α) (machine : Machine platform) : IO (α × Machine platform) :=
  match action machine with
  | .done (.normal value) next => pure (value, next)
  | _ => throw (IO.userError "expected normal completion")

private def allocateArray (heap : Heap) (values : List (Option Value))
    (prototype : Option RefId := none) : IO (RefId × Heap) :=
  match heap.allocateArray values prototype with
  | .ok result => pure result
  | _ => throw (IO.userError "array allocation failed")

private def define (heap : Heap) (ref : RefId) (propertyKey : PropertyKey)
    (update : DescriptorUpdate) : IO (Bool × Heap) :=
  match heap.defineOwnProperty ref propertyKey update with
  | .ok result => pure result
  | _ => throw (IO.userError "property definition faulted")

private def ownValue (heap : Heap) (ref : RefId) (propertyKey : PropertyKey) : Option Value :=
  match heap.getOwnProperty ref propertyKey with
  | .ok (some (.data descriptor)) => some descriptor.value
  | _ => none

private def testLengthsAndIndices : IO Unit := do
  for length in [0, 1, 4294967294, 4294967295] do
    assert! Heap.validArrayLength? (Heap.arrayLengthNumber length) = some length
  for invalid in [JSNumber.canonicalNaN, JSNumber.positiveInfinity,
      JSNumber.negativeInfinity, (⟨0x3ff8000000000000⟩ : JSNumber),
      (⟨0xbff0000000000000⟩ : JSNumber), (⟨0x41f0000000000000⟩ : JSNumber)] do
    assert! Heap.validArrayLength? invalid = none

  let (array, heap) ← allocateArray Heap.empty []
  let (success, heap) ← define heap array (indexKey 4294967294) { value := .present (bigint 1) }
  assert! success
  match heap.arrayLength array with | .ok length => assert! length = 4294967295 | _ => assert! false
  let (success, heap) ← define heap array (key "4294967295") { value := .present (bigint 2) }
  assert! success
  match heap.arrayLength array with | .ok length => assert! length = 4294967295 | _ => assert! false
  let (success, heap) ← define heap array (key "length") { writable := .present false }
  assert! success
  let (success, unchanged) ← define heap array (indexKey 0) { value := .present (bigint 3) }
  assert! success
  let (success, unchanged) ← define unchanged array (indexKey 4294967294)
    { value := .present (bigint 4) }
  assert! !success
  let (success, unchangedAgain) ← define unchanged array (indexKey 4294967293)
    { value := .present (bigint 5) }
  assert! success
  match unchangedAgain.arrayLength array with
  | .ok length => assert! length = 4294967295
  | _ => assert! false
  let (success, _) ← define unchangedAgain array (key "length") { writable := .present true }
  assert! !success
  assert! unchangedAgain.deleteProperty array (key "length") matches .ok (false, _)
  assert! unchangedAgain.isWellFormed

  let (small, heap) ← allocateArray unchangedAgain []
  let (_, heap) ← define heap small (key "length") { writable := .present false }
  let (success, _) ← define heap small (indexKey 0) { value := .present (bigint 1) }
  assert! !success
  match heap.defineOwnProperty small (key "length")
      { value := .present (.primitive (.number ⟨0x3ff8000000000000⟩)) } with
  | .error (.invalidArrayLength _) => pure ()
  | _ => assert! false

private def testShrinkAndKeys : IO Unit := do
  let (array, heap) ← allocateArray Heap.empty [some (bigint 0), some (bigint 1),
    some (bigint 2), some (bigint 3)]
  let (_, heap) ← define heap array (indexKey 2) { configurable := .present false }
  let (success, heap) ← define heap array (key "length")
    { value := .present (.primitive (.number (Heap.arrayLengthNumber 1))) }
  assert! !success
  match heap.arrayLength array with | .ok length => assert! length = 3 | _ => assert! false
  assert! ownValue heap array (indexKey 3) = none
  assert! ownValue heap array (indexKey 2) = some (bigint 2)
  let (_, heap) ← define heap array (key "z") {
    value := .present (bigint 9)
    writable := .present true
    enumerable := .present true
    configurable := .present true }
  let (_, heap) ← define heap array (.symbol (.allocated 7)) {
    value := .present (bigint 7)
    writable := .present true
    enumerable := .present true
    configurable := .present true }
  match heap.ownPropertyKeys array with
  | .ok keys => assert! keys = [indexKey 0, indexKey 1, indexKey 2, key "length", key "z",
      .symbol (.allocated 7)]
  | _ => assert! false
  assert! heap.isWellFormed

private def testBlockedShrinkProperty : IO Unit := do
  for blocked in [1:17] do
    let values := (List.range 20).map fun index => some (bigint index)
    let (array, heap) ← allocateArray Heap.empty values
    let (_, heap) ← define heap array (indexKey blocked) { configurable := .present false }
    let (success, heap) ← define heap array (key "length") {
      value := .present (.primitive (.number (Heap.arrayLengthNumber 0)))
      writable := .present false }
    assert! !success
    match heap.arrayLength array with
    | .ok length => assert! length = blocked + 1
    | _ => assert! false
    for index in [0:20] do
      if index ≤ blocked then assert! ownValue heap array (indexKey index) = some (bigint index)
      else assert! (ownValue heap array (indexKey index)).isNone
    match heap.getOwnProperty array (key "length") with
    | .ok (some (.data descriptor)) => assert! !descriptor.writable
    | _ => assert! false
    assert! heap.isWellFormed

private def testInheritedHoleAndIterator : IO Unit := do
  let (parent, heap) ← match Heap.empty.allocate with
    | .ok result => pure result | _ => throw (IO.userError "parent allocation failed")
  let (_, heap) ← define heap parent (indexKey 0) {
    value := .present (bigint 8)
    writable := .present true
    enumerable := .present true
    configurable := .present true }
  let (array, heap) ← allocateArray heap [none] (some parent)
  let machine := (Machine.initial platform 1000).setHeap heap
  let (inherited, machine) ← runNormal
    (ObjectAccess.get fallthrough array (indexKey 0) (.object array)) machine
  assert! inherited = bigint 8
  let (firstIterator, machine) ← runNormal (Iterator.arrayValues array) machine
  let (secondIterator, machine) ← runNormal (Iterator.arrayValues array) machine
  assert! firstIterator != secondIterator
  let (first, machine) ← runNormal (Iterator.next fallthrough firstIterator) machine
  assert! first = ⟨bigint 8, false⟩
  let (_, heap) ← define machine.heap array (indexKey 1) {
    value := .present (.object parent)
    writable := .present true
    enumerable := .present true
    configurable := .present true }
  let (appended, machine) ← runNormal (Iterator.next fallthrough firstIterator) (machine.setHeap heap)
  assert! appended = ⟨.object parent, false⟩
  let (done, machine) ← runNormal (Iterator.next fallthrough firstIterator) machine
  let (doneAgain, _) ← runNormal (Iterator.next fallthrough firstIterator) machine
  assert! done = ⟨undefined, true⟩ && doneAgain = done

private def testSliceAndSpread : IO Unit := do
  let (nested, heap) ← match Heap.empty.allocate with
    | .ok result => pure result | _ => throw (IO.userError "nested allocation failed")
  let (source, heap) ← allocateArray heap [none, some (.object nested)]
  let machine := (Machine.initial platform 1000).setHeap heap
  let (sliced, machine) ← runNormal (ArrayCopy.slice fallthrough source) machine
  let (spread, machine) ← runNormal (ArrayCopy.spread fallthrough source) machine
  assert! sliced != source && spread != source && sliced != spread
  assert! ownValue machine.heap sliced (indexKey 0) = none
  assert! ownValue machine.heap spread (indexKey 0) = some undefined
  assert! ownValue machine.heap sliced (indexKey 1) = some (.object nested)
  assert! ownValue machine.heap spread (indexKey 1) = some (.object nested)
  assert! machine.isWellFormed

private def testSpreadObservesGetterAppend : IO Unit := do
  let machine := Machine.initial platform 1000
  let (getter, heap) ← match machine.heap.allocateFunction machine.globalEnv .ordinary false none with
    | .ok result => pure result | _ => throw (IO.userError "getter allocation failed")
  let (source, heap) ← allocateArray heap [none]
  let (_, heap) ← define heap source (indexKey 0) {
    get := .present (some getter)
    enumerable := .present true
    configurable := .present true }
  let appendingHook : BodyHook platform := fun function _ _ =>
    if function = getter then fun current =>
      match current.heap.createDataProperty source (indexKey 1) (bigint 9) with
      | .ok (true, next) => .done (.returned (bigint 1)) (current.setHeap next)
      | _ => .fault (.runtime (.heap .cycleOrFuelExhausted)) current
    else pure ()
  let (spread, machine) ← runNormal (ArrayCopy.spread appendingHook source) (machine.setHeap heap)
  match machine.heap.arrayLength spread with | .ok length => assert! length = 2 | _ => assert! false
  assert! ownValue machine.heap spread (indexKey 0) = some (bigint 1)
  assert! ownValue machine.heap spread (indexKey 1) = some (bigint 9)

private def testInvalidReferences : IO Unit := do
  assert! Heap.empty.allocateArray [some (.object ⟨9⟩)] matches .error (.invalidValueRef _)
  assert! Heap.empty.allocateArray [] (some ⟨9⟩) matches .error (.heap (.invalidPrototype _))
  assert! Heap.empty.allocateArrayIterator ⟨9⟩ matches .error (.invalidRef _)

private def testWrongObjectKinds : IO Unit := do
  let (ordinary, heap) ← match Heap.empty.allocate with
    | .ok result => pure result | _ => throw (IO.userError "ordinary allocation failed")
  let (array, heap) ← allocateArray heap []
  match heap.arrayLength ordinary with
  | .error (.wrongObjectKind ref .array .ordinary) => assert! ref = ordinary
  | _ => assert! false
  match heap.allocateArrayIterator ordinary with
  | .error (.wrongObjectKind ref .array .ordinary) => assert! ref = ordinary
  | _ => assert! false
  match heap.advanceArrayIterator array with
  | .error (.wrongObjectKind ref .arrayIterator .array) => assert! ref = array
  | _ => assert! false

private def testCatchableLengthErrors : IO Unit := do
  let (array, heap) ← allocateArray Heap.empty []
  let machine := (Machine.initial platform 10).setHeap heap
  match ObjectAccess.defineOwnProperty array (key "length")
      { value := .present (.primitive (.number JSNumber.canonicalNaN)) } machine with
  | .done (.thrown (.primitive (.string message))) _ =>
      assert! message.equal (JSString.ofLeanString "RangeError: invalid array length")
  | _ => assert! false
  match ObjectAccess.defineOwnProperty array (key "length")
      { value := .present (bigint 1) } machine with
  | .done (.thrown (.primitive (.string message))) _ =>
      assert! message.equal (JSString.ofLeanString "TypeError: array length must be a number")
  | _ => assert! false

private def run : IO Unit := do
  testLengthsAndIndices
  testShrinkAndKeys
  testBlockedShrinkProperty
  testInheritedHoleAndIterator
  testSliceAndSpread
  testSpreadObservesGetterAppend
  testInvalidReferences
  testWrongObjectKinds
  testCatchableLengthErrors

#eval run

end TSLean.JS.ArrayTests
