import TSLean.JS.ArrayCopy
import TSLean.JS.Copy

namespace TSLean.JS.ArrayScaleTests

private def platform : Platform := ScriptedPlatform.make { times := #[], randoms := #[], fetches := #[] }
private def fallthrough : BodyHook platform := fun _ _ _ => pure ()
private def undefined : Value := .primitive .undefined

/-- The hook used by the 100,001-step iterator scale run satisfies its formal preservation premise. -/
private theorem iteratorScaleHookPreservesWellFormed :
    BodyHookPreservesWellFormed fallthrough ∧
      JSM.PreservesWellFormed (Iterator.next fallthrough ⟨0⟩) := by
  have hookValid : BodyHookPreservesWellFormed fallthrough := by
    intro ref receiver arguments
    exact ⟨fun machine valid inputs => JSM.pure_preservesWellFormed () machine valid,
      by intro machine valid inputs; trivial⟩
  exact ⟨hookValid, Iterator.next_preservesWellFormed fallthrough ⟨0⟩ hookValid⟩

private def allocateArray (heap : Heap) (values : Array (Option Value)) : IO (RefId × Heap) :=
  match heap.allocateArrayFromArray values with
  | .ok result => pure result
  | _ => throw (IO.userError "scale array allocation failed")

private def arrayScale : IO Unit := do
  let totalStart ← IO.monoMsNow
  let constructionStart ← IO.monoMsNow
  let denseValues := Array.mkArray 100000 (some undefined)
  let (dense, heap) ← allocateArray Heap.empty denseValues
  let sparseValues := (Array.mkArray 100000 none)
    |>.setIfInBounds 0 (some undefined)
    |>.setIfInBounds 99999 (some undefined)
  let (sparse, heap) ← allocateArray heap sparseValues
  let constructionMs := (← IO.monoMsNow) - constructionStart
  assert! heap.arrayLength dense matches .ok 100000
  assert! heap.arrayLength sparse matches .ok 100000
  match heap.get? sparse with
  | .ok object => assert! object.properties.size = 2
  | _ => assert! false
  let validationStart ← IO.monoMsNow
  assert! heap.isWellFormed
  let validationMs := (← IO.monoMsNow) - validationStart
  let ownKeysStart ← IO.monoMsNow
  match heap.ownPropertyKeys dense, heap.ownPropertyKeys sparse with
  | .ok denseKeys, .ok sparseKeys =>
      assert! denseKeys.length = 100001
      assert! sparseKeys.length = 3
  | _, _ => assert! false
  let ownKeysMs := (← IO.monoMsNow) - ownKeysStart
  let totalMs := (← IO.monoMsNow) - totalStart
  IO.println s!"array-scale dense=100000 sparseLength=100000 constructionMs={constructionMs} wellFormedMs={validationMs} ownKeysMs={ownKeysMs} totalMs={totalMs}"
  assert! constructionMs < 5000
  assert! validationMs < 5000
  assert! ownKeysMs < 5000
  assert! totalMs < 12000

private def iteratorScale : IO Unit := do
  let totalStart ← IO.monoMsNow
  let constructionStart ← IO.monoMsNow
  let (array, heap) ← allocateArray Heap.empty (Array.mkArray 100000 (some undefined))
  let machine := (Machine.initial platform 10).setHeap heap
  let (iterator, machine) ← match Iterator.arrayValues array machine with
    | .done (.normal iterator) next => pure (iterator, next)
    | _ => throw (IO.userError "iterator allocation failed")
  let mut machine := machine
  let constructionMs := (← IO.monoMsNow) - constructionStart
  let iterationStart ← IO.monoMsNow
  let mut count := 0
  let mut done := false
  while !done do
    if count = 99999 then
      match machine.heap.createDataProperty array (.string (PropertyKey.arrayIndexString 100000))
          undefined with
      | .ok (true, heap) => machine := machine.setHeap heap
      | _ => throw (IO.userError "live append failed")
    match Iterator.next fallthrough iterator machine with
    | .done (.normal result) next =>
        machine := next
        done := result.done
        if !done then count := count + 1
    | _ => throw (IO.userError "iterator step failed")
  let iterationMs := (← IO.monoMsNow) - iterationStart
  assert! count = 100001
  let validationStart ← IO.monoMsNow
  assert! machine.isWellFormed
  let validationMs := (← IO.monoMsNow) - validationStart
  let totalMs := (← IO.monoMsNow) - totalStart
  assert! constructionMs < 5000
  assert! iterationMs < 5000
  assert! validationMs < 5000
  assert! totalMs < 12000
  IO.println s!"iterator-scale steps={count} liveAppends=1 constructionMs={constructionMs} iterationMs={iterationMs} wellFormedMs={validationMs} totalMs={totalMs}"

private def copyScale : IO Unit := do
  let totalStart ← IO.monoMsNow
  let constructionStart ← IO.monoMsNow
  let (source, initialHeap) ← match Heap.empty.allocate with
    | .ok result => pure result | _ => throw (IO.userError "copy source allocation failed")
  let mut heap := initialHeap
  for index in [0:10000] do
    match heap.createDataProperty source (.string (JSString.ofLeanString s!"k{index}")) undefined with
    | .ok (true, next) => heap := next
    | _ => throw (IO.userError "copy source property failed")
  let machine := (Machine.initial platform 10).setHeap heap
  let constructionMs := (← IO.monoMsNow) - constructionStart
  let copyStart ← IO.monoMsNow
  let (spread, machine) ← match Copy.objectSpread fallthrough [.object source] [] machine with
    | .done (.normal spread) next => pure (spread, next)
    | _ => throw (IO.userError "copy scale failed")
  let copyMs := (← IO.monoMsNow) - copyStart
  let ownKeysStart ← IO.monoMsNow
  match machine.heap.ownPropertyKeys spread with
  | .ok keys => assert! keys.length = 10000
  | _ => assert! false
  let ownKeysMs := (← IO.monoMsNow) - ownKeysStart
  let validationStart ← IO.monoMsNow
  assert! machine.isWellFormed
  let validationMs := (← IO.monoMsNow) - validationStart
  let totalMs := (← IO.monoMsNow) - totalStart
  assert! constructionMs < 5000
  assert! copyMs < 5000
  assert! ownKeysMs < 5000
  assert! validationMs < 5000
  assert! totalMs < 12000
  IO.println s!"copy-scale keys=10000 constructionMs={constructionMs} copyMs={copyMs} ownKeysMs={ownKeysMs} wellFormedMs={validationMs} totalMs={totalMs}"

private def run : IO Unit := do
  arrayScale
  iteratorScale
  copyScale

end TSLean.JS.ArrayScaleTests

def main : IO Unit := TSLean.JS.ArrayScaleTests.run
