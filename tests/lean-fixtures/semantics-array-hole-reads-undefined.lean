import TSLean.LeanToTypeScript.Semantics.Preservation

/-!
Negative fixture: an array hole read as `undefined`.

An emitted array is dense. `Target.readIndices` refuses an index whose own key holds no data
property rather than reading it as `undefined`, because a hole and a stored `undefined` are different
observations and only one of them is a shape the emitter produces. This file claims the absent index
answers `undefined`. The proof offered is the direct reduction a dense read uses, so the model itself
must reject it.

`scripts/check-semantics-registry.mjs --self-test` requires this file to fail.
-/

namespace TSLean.LeanToTypeScript.Semantics.SemanticsFixture

open TSLean.JS

theorem holeReadsUndefined (heap : Heap) (ref : RefId) (index : Nat)
    (absent : heap.getOwnProperty ref (.string (PropertyKey.arrayIndexString index)) = .ok none) :
    Target.readIndices heap ref index 1 = .ok [.primitive .undefined] := by
  simp only [Target.readIndices, absent]

end TSLean.LeanToTypeScript.Semantics.SemanticsFixture
