import TSLean.JS.Prototype

namespace TSLean.JS.HeapTests

private def key (value : String) : PropertyKey := .string (JSString.ofLeanString value)
private def value (n : Nat) : Value := .primitive (.bigint n)
private def keysEqual : List PropertyKey → List PropertyKey → Bool
  | [], [] => true
  | left :: leftRest, right :: rightRest =>
      PropertyKey.equal left right && keysEqual leftRest rightRest
  | _, _ => false

private def allocate (heap : Heap) (prototype : Option RefId := none)
    (extensible : Bool := true) : IO (RefId × Heap) :=
  match heap.allocate prototype extensible with
  | .ok result => pure result
  | .error _ => throw (IO.userError "allocation failed")

private def defineData (heap : Heap) (ref : RefId) (propertyKey : PropertyKey)
    (propertyValue : Value) : IO Heap :=
  match heap.createDataProperty ref propertyKey propertyValue with
  | .ok (true, next) => pure next
  | _ => throw (IO.userError "createDataProperty failed")

private def testArrayIndexRecognition : IO Unit := do
  assert! PropertyKey.arrayIndex? (JSString.ofLeanString "0") == some 0
  assert! PropertyKey.arrayIndex? (JSString.ofLeanString "4294967294") == some 4294967294
  for rejected in ["", "00", "-0", "1.0", "4294967295"] do
    assert! PropertyKey.arrayIndex? (JSString.ofLeanString rejected) == none
  assert! PropertyKey.arrayIndex? ⟨[UInt16.ofNat 0xff11]⟩ == none
  assert! (PropertyKey.arrayIndexString 4294967294).equal (JSString.ofLeanString "4294967294")

private def testHeapIdentity : IO Unit := do
  let (first, heap) ← allocate Heap.empty
  let (second, heap) ← allocate heap
  assert! first != second
  let updated ←
    match heap.preventExtensions first with
    | .ok next => pure next
    | .error _ => throw (IO.userError "preventExtensions failed")
  let updatedAgain ←
    match updated.preventExtensions first with
    | .ok next => pure next
    | .error _ => throw (IO.userError "repeated preventExtensions failed")
  match updatedAgain.get? first, updatedAgain.get? second with
  | .ok firstObject, .ok secondObject =>
      assert! !firstObject.extensible
      assert! secondObject.extensible
  | _, _ => assert! false
  match updatedAgain.createDataProperty first (key "bypass") (value 1) with
  | .ok (false, unchanged) =>
      match unchanged.get? first with
      | .ok object => assert! !object.extensible
      | .error _ => assert! false
  | _ => assert! false
  assert! Heap.empty.allocate (some ⟨0⟩) matches .error (.invalidPrototype _)

private def testOwnKeyOrder : IO Unit := do
  let (ref, heap) ← allocate Heap.empty
  let heap ← defineData heap ref (key "10") (value 10)
  let heap ← defineData heap ref (key "2") (value 2)
  let heap ← defineData heap ref (key "00") (value 0)
  let heap ← defineData heap ref (key "-0") (value 1)
  let heap ← defineData heap ref (key "4294967295") (value 2)
  let heap ← defineData heap ref (.symbol (.allocated 2)) (value 3)
  let heap ← defineData heap ref (.symbol (.allocated 1)) (value 4)
  match OrdinaryObject.ownPropertyKeys heap ref with
  | .ok keys =>
      assert! keysEqual keys [key "2", key "10", key "00", key "-0", key "4294967295",
        .symbol (.allocated 2), .symbol (.allocated 1)]
  | .error _ => assert! false
  let heap ← defineData heap ref (key "00") (value 9)
  let heap ← match heap.deleteProperty ref (key "00") with
    | .ok (true, next) => pure next | _ => throw (IO.userError "delete failed")
  let heap ← defineData heap ref (key "00") (value 10)
  let heap ← match heap.deleteProperty ref (.symbol (.allocated 2)) with
    | .ok (true, next) => pure next | _ => throw (IO.userError "delete failed")
  let heap ← defineData heap ref (.symbol (.allocated 2)) (value 11)
  match OrdinaryObject.ownPropertyKeys heap ref with
  | .ok keys =>
      assert! keysEqual keys [key "2", key "10", key "-0", key "4294967295", key "00",
        .symbol (.allocated 1), .symbol (.allocated 2)]
      assert! keys.Nodup
      match heap.get? ref with
      | .ok object =>
          assert! keys.length = object.properties.size
          assert! object.properties.isWellFormed
      | .error _ => assert! false
  | .error _ => assert! false
  match Prototype.lookup heap ref (key "missing") with
  | .ok none => pure ()
  | _ => assert! false

private def testDescriptors : IO Unit := do
  let fixed : PropertyDescriptor := .data ⟨value 1, false, true, false⟩
  assert! ({ value := .present (value 1), get := .present none } : DescriptorUpdate).validateSyntax
    matches .error .mixedDescriptor
  let kind ← match ({} : DescriptorUpdate).validateSyntax with
    | .ok kind => pure kind | _ => throw (IO.userError "syntax validation failed")
  match ({} : DescriptorUpdate).applyValidatedDescriptor (some fixed) true kind with
  | .ok (.data current) => assert! sameValue current.value (value 1)
  | _ => assert! false
  let dataKind ← match ({ value := .present (value 2) } : DescriptorUpdate).validateSyntax with
    | .ok kind => pure kind | _ => throw (IO.userError "syntax validation failed")
  assert! ({ value := .present (value 2) } : DescriptorUpdate).applyValidatedDescriptor
    (some fixed) true dataKind matches .error .nonWritable

  let (target, heap) ← allocate Heap.empty
  let (accessor, heap) ← allocate heap
  match heap.defineOwnProperty target (key "mixed") {
      value := .present (value 1), get := .present none } with
  | .error (.syntax .mixedDescriptor) => pure ()
  | _ => assert! false
  match heap.defineOwnProperty target (key "invalid") {
      get := .present (some ⟨999⟩) } with
  | .error (.invalidAccessor _) => pure ()
  | _ => assert! false
  match heap.defineOwnProperty target (key "ordinary") {
      get := .present (some accessor) } with
  | .error (.nonCallableAccessor ref) => assert! ref = accessor
  | _ => assert! false
  match heap.createDataProperty target (key "dangling") (.object ⟨999⟩) with
  | .error (.invalidValueRef ref) => assert! ref = ⟨999⟩
  | _ => assert! false
  match heap.createDataProperty target (key "live") (.object accessor) with
  | .ok (true, next) =>
      match OrdinaryObject.getOwnProperty next target (key "live") with
      | .ok (some (.data property)) => assert! (property.value matches .object _)
      | _ => assert! false
  | _ => assert! false

private def testPrototypeBehavior : IO Unit := do
  let (parent, heap) ← allocate Heap.empty
  let (child, heap) ← allocate heap (some parent)
  let heap ← defineData heap parent (key "x") (value 1)
  match Prototype.lookup heap child (key "x") with
  | .ok (some (owner, .data property)) =>
      assert! owner = parent
      assert! sameValue property.value (value 1)
  | _ => assert! false
  let heap ← defineData heap child (key "x") (value 2)
  match Prototype.lookup heap child (key "x") with
  | .ok (some (owner, .data property)) =>
      assert! owner = child
      assert! sameValue property.value (value 2)
  | _ => assert! false
  match heap.setPrototypeOf parent (some child) with
  | .ok (false, unchanged) => assert! unchanged.size = heap.size
  | _ => assert! false
  match heap.setPrototypeOf child (some ⟨999⟩) with
  | .error (.invalidPrototype _) => pure ()
  | _ => assert! false

  let nonextensible ← match heap.preventExtensions child with
    | .ok next => pure next | _ => throw (IO.userError "preventExtensions failed")
  match nonextensible.setPrototypeOf child (some parent) with
  | .ok (true, unchanged) => assert! unchanged.size = nonextensible.size
  | _ => assert! false
  match nonextensible.setPrototypeOf child (some ⟨999⟩) with
  | .ok (false, unchanged) => assert! unchanged.size = nonextensible.size
  | _ => assert! false

  let detached ← match heap.setPrototypeOf child none with
    | .ok (true, next) => pure next | _ => throw (IO.userError "prototype detach failed")
  let reversed ← match detached.setPrototypeOf parent (some child) with
    | .ok (true, next) => pure next | _ => throw (IO.userError "valid prototype set failed")
  match Prototype.lookup reversed parent (key "missing") with
  | .ok none => pure ()
  | _ => assert! false

private def testFaults : IO Unit := do
  let invalid : RefId := ⟨9⟩
  assert! Heap.empty.get? invalid matches .error (.invalidRef _)
  assert! Heap.empty.preventExtensions invalid matches .error (.invalidRef _)
  assert! OrdinaryObject.getOwnProperty Heap.empty invalid (key "x") matches .error (.invalidRef _)
  let (ref, heap) ← allocate Heap.empty none false
  match heap.createDataProperty ref (key "x") (value 1) with
  | .ok (false, unchanged) => assert! unchanged.size = heap.size
  | _ => assert! false
  match heap.setPrototypeOf ref (some ⟨999⟩) with
  | .ok (false, unchanged) => assert! unchanged.size = heap.size
  | _ => assert! false

private def assertScale (name : String) (heap : Heap) (ref : RefId) (constructionMs : Nat) : IO Unit := do
  let properties ← match heap.get? ref with
    | .ok object => pure object.properties
    | .error _ => throw (IO.userError "scale object missing")
  let enumerationStart ← IO.monoMsNow
  let mut enumeratedKeys := 0
  for _ in [0:10] do enumeratedKeys := enumeratedKeys + properties.ownKeys.length
  let enumerationMs := (← IO.monoMsNow) - enumerationStart
  let keys := properties.ownKeys
  assert! properties.size = 10000
  assert! keys.length = 10000
  assert! enumeratedKeys = 100000
  assert! keys.Nodup
  assert! constructionMs < 2500
  assert! enumerationMs < 1500
  IO.println s!"heap-scale {name} keys={keys.length} buildMs={constructionMs} ownKeys10Ms={enumerationMs}"

private def scalingSmoke : IO Unit := do
  let (stringsRef, stringsHeap) ← allocate Heap.empty
  let start ← IO.monoMsNow
  let mut stringsHeap := stringsHeap
  for index in [0:10000] do
    stringsHeap ← defineData stringsHeap stringsRef (key s!"k{index}") (value index)
  let elapsed := (← IO.monoMsNow) - start
  assertScale "strings" stringsHeap stringsRef elapsed

  let (symbolsRef, symbolsHeap) ← allocate Heap.empty
  let start ← IO.monoMsNow
  let mut symbolsHeap := symbolsHeap
  for index in [0:10000] do
    symbolsHeap ← defineData symbolsHeap symbolsRef (.symbol (.allocated index)) (value index)
  let elapsed := (← IO.monoMsNow) - start
  assertScale "symbols" symbolsHeap symbolsRef elapsed

  let (indicesRef, indicesHeap) ← allocate Heap.empty
  let start ← IO.monoMsNow
  let mut indicesHeap := indicesHeap
  for index in [0:10000] do
    indicesHeap ← defineData indicesHeap indicesRef (key (10000 - index - 1).repr) (value index)
  let elapsed := (← IO.monoMsNow) - start
  assertScale "indices" indicesHeap indicesRef elapsed
  match OrdinaryObject.ownPropertyKeys indicesHeap indicesRef with
  | .ok (.string first :: _) => assert! first.equal (JSString.ofLeanString "0")
  | _ => assert! false

private def churnSmoke : IO Unit := do
  let (ref, initialHeap) ← allocate Heap.empty
  let stringAnchor := key "string-anchor"
  let stringChurn := key "string-churn"
  let symbolAnchor : PropertyKey := .symbol (.allocated 100001)
  let symbolChurn : PropertyKey := .symbol (.allocated 100002)
  let heap ← defineData initialHeap ref stringAnchor (value 0)
  let heap ← defineData heap ref stringChurn (value 1)
  let heap ← defineData heap ref symbolAnchor (value 2)
  let mut heap ← defineData heap ref symbolChurn (value 3)
  for index in [0:128] do
    heap ← match heap.deleteProperty ref stringChurn with
      | .ok (true, next) => pure next | _ => throw (IO.userError "validity string delete failed")
    match heap.get? ref with
    | .ok object => assert! object.properties.isWellFormed
    | _ => assert! false
    heap ← defineData heap ref stringChurn (value index)
    heap ← match heap.deleteProperty ref symbolChurn with
      | .ok (true, next) => pure next | _ => throw (IO.userError "validity symbol delete failed")
    match heap.get? ref with
    | .ok object =>
        assert! object.properties.metadataConsistent
        assert! object.properties.ownKeys.Nodup
        assert! object.properties.ownKeys.length = object.properties.size
        assert! object.properties.isWellFormed
    | _ => assert! false
    heap ← defineData heap ref symbolChurn (value index)
    match heap.get? ref with
    | .ok object => assert! object.properties.isWellFormed
    | _ => assert! false
  let start ← IO.monoMsNow
  for index in [0:100000] do
    heap ← match heap.deleteProperty ref stringChurn with
      | .ok (true, next) => pure next | _ => throw (IO.userError "string churn delete failed")
    heap ← defineData heap ref stringChurn (value index)
    heap ← match heap.deleteProperty ref symbolChurn with
      | .ok (true, next) => pure next | _ => throw (IO.userError "symbol churn delete failed")
    heap ← defineData heap ref symbolChurn (value index)
  let elapsed := (← IO.monoMsNow) - start
  assert! elapsed < 7000
  let properties ← match heap.get? ref with
    | .ok object => pure object.properties | _ => throw (IO.userError "churn object missing")
  assert! properties.metadataSlots.1 ≤ OrderedProps.compactionThreshold
  assert! properties.metadataSlots.2 ≤ OrderedProps.compactionThreshold
  assert! keysEqual properties.ownKeys [stringAnchor, stringChurn, symbolAnchor, symbolChurn]
  assert! properties.ownKeys.Nodup
  assert! properties.isWellFormed
  IO.println s!"heap-churn cycles=100000 stringSlots={properties.metadataSlots.1} symbolSlots={properties.metadataSlots.2} ms={elapsed}"

private def run : IO Unit := do
  assert! OrderedProps.adversarialMetadataRejected
  testArrayIndexRecognition
  testHeapIdentity
  testOwnKeyOrder
  testDescriptors
  testPrototypeBehavior
  testFaults

def runScale : IO Unit := do
  scalingSmoke
  churnSmoke

#eval run

end TSLean.JS.HeapTests
