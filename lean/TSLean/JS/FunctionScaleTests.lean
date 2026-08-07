import TSLean.JS.Instanceof
import TSLean.JS.RealmTestSupportTests

namespace TSLean.JS.FunctionScaleTests

private def platform : Platform := ScriptedPlatform.make {
  times := #[], randoms := #[], fetches := #[]
}

private def call : BodyHook platform := fun _ _ _ => pure ()

private def run : IO Unit := do
  let functionStart ← IO.monoMsNow
  let mut functionHeap := Heap.empty
  for _ in [0:100000] do
    functionHeap ← match functionHeap.allocateFunction ⟨0⟩ .arrow false none none .base
        (some (.primitive .undefined)) with
      | .ok (_, next) => pure next
      | .error _ => throw (IO.userError "function scale allocation failed")
  let functionMs := (← IO.monoMsNow) - functionStart
  assert! functionHeap.size = 100000
  assert! functionHeap.functionCount = 100000
  assert! functionMs < 5000
  let functionValidityStart ← IO.monoMsNow
  assert! functionHeap.isWellFormed
  let functionValidityMs := (← IO.monoMsNow) - functionValidityStart
  assert! functionValidityMs < 5000

  let realm ← match RealmTestSupport.bootstrap (Machine.initial platform 0) with
    | .ok fixture => pure fixture
    | .error _ => throw (IO.userError "realm bootstrap failed")
  let machine := realm.machine
  let objectPrototype := realm.intrinsics.objectPrototype
  let heap := machine.heap
  let (functionPrototype, heap) ← match heap.allocate (some objectPrototype) with
    | .ok result => pure result
    | .error _ => throw (IO.userError "function prototype allocation failed")
  let (constructor, prototype, heap) ←
    match heap.allocateConstructorPair ⟨0⟩ (some functionPrototype) (some objectPrototype) with
    | .ok result => pure result
    | .error _ => throw (IO.userError "constructor scale allocation failed")
  let chainStart ← IO.monoMsNow
  let mut heap := heap
  let mut leaf := prototype
  for _ in [0:10000] do
    match heap.allocate (some leaf) with
    | .ok (nextLeaf, nextHeap) =>
        leaf := nextLeaf
        heap := nextHeap
    | .error _ => throw (IO.userError "prototype chain allocation failed")
  let chainBuildMs := (← IO.monoMsNow) - chainStart
  let lookupStart ← IO.monoMsNow
  let result := Instanceof.ordinaryHasInstance call constructor (.object leaf) (machine.setHeap heap)
  let lookupMs := (← IO.monoMsNow) - lookupStart
  let chainValidityStart ← IO.monoMsNow
  assert! heap.isWellFormed
  assert! (machine.setHeap heap).isWellFormed
  let chainValidityMs := (← IO.monoMsNow) - chainValidityStart
  match result with
  | .done (.normal true) _ => pure ()
  | _ => throw (IO.userError "prototype chain lookup failed")
  assert! chainBuildMs < 3000
  assert! lookupMs < 1000
  assert! chainValidityMs < 2000
  IO.println s!"function-scale allocations=100000 buildMs={functionMs} validityMs={functionValidityMs}"
  IO.println s!"prototype-scale depth=10000 buildMs={chainBuildMs} lookupMs={lookupMs} validityMs={chainValidityMs}"

#eval run

end TSLean.JS.FunctionScaleTests
