import TSLean.JS.Theorems
import TSLean.JS.Prototype

namespace TSLean.JS

/-- A successful allocation returns the former heap size. -/
theorem Heap.allocate_fresh (heap next : Heap) (prototype : Option RefId)
    (extensible : Bool) (ref : RefId)
    (allocated : heap.allocate prototype extensible = .ok (ref, next)) :
    ref.value = heap.size := by
  unfold Heap.allocate at allocated
  split at allocated
  · rcases allocated with ⟨rfl, rfl⟩
    rfl
  · cases prototype <;> simp_all

/-- A successful allocation adds exactly one stable slot. -/
theorem Heap.allocate_size (heap next : Heap) (prototype : Option RefId)
    (extensible : Bool) (ref : RefId)
    (allocated : heap.allocate prototype extensible = .ok (ref, next)) :
    next.size = heap.size + 1 := by
  unfold Heap.allocate at allocated
  split at allocated
  · rcases allocated with ⟨rfl, rfl⟩
    simp [Heap.size]
  · cases prototype <;> simp_all

/-- Successful allocation preserves every previously valid lookup. -/
theorem Heap.allocate_stable (heap next : Heap) (prototype : Option RefId)
    (extensible : Bool) (allocatedRef ref : RefId)
    (allocated : heap.allocate prototype extensible = .ok (allocatedRef, next))
    (valid : ref.value < heap.size) : next.get? ref = heap.get? ref := by
  unfold Heap.allocate at allocated
  split at allocated
  · rcases allocated with ⟨rfl, rfl⟩
    have notLast : ref.value ≠ heap.objects.size := Nat.ne_of_lt valid
    simp [Heap.get?, Array.getElem?_push, notLast]
  · cases prototype <;> simp_all

/-- Object equality remains reference identity. -/
theorem Heap.object_equality_is_reference_identity (left right : RefId) :
    strictEqual (.object left) (.object right) = decide (left = right) :=
  strictEqual_object left right

/-- A nonextensible change is rejected before an invalid candidate is traversed. -/
theorem Heap.nonextensible_rejects_before_candidate
    (heap : Heap) (ref : RefId) (object : ObjectRecord) (candidate : Option RefId)
    (found : heap.get? ref = .ok object) (changed : object.prototype ≠ candidate)
    (fixed : object.extensible = false) :
    heap.setPrototypeOf ref candidate = .ok (false, heap) := by
  simp [Heap.setPrototypeOf, found, changed, fixed]

-- TODO(theorem): prove private `OrderedProps.insert/delete`, including threshold-crossing and
-- deletion compaction, preserve exact bidirectional metadata `WellFormed`; derive duplicate-free
-- partitioned `ownKeys`; and prove ordinary plus array mutation preserve complete `Heap.WellFormed`.
-- Array shrink rejection is deliberately excluded from the old heap-preservation claim because a
-- blocked shrink commits all configurable higher-index deletions before returning `false`.

end TSLean.JS
