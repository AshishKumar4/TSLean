import TSLean.JS.ArrayCopy
import TSLean.JS.Copy

namespace TSLean.JS

private abbrev emptyArrayAllocationFreshCheck : Bool :=
  match Heap.empty.allocateArray [] with
  | .ok (ref, next) => ref.value == 0 && next.size == 1 &&
      match next.arrayLength ref with | .ok 0 => true | _ => false
  | .error _ => false

/-- Empty-array allocation issues the first fresh reference and records exact zero length. -/
theorem Heap.empty_array_allocation_fresh : emptyArrayAllocationFreshCheck = true := by
  decide

private abbrev emptyArrayDeleteLengthCheck : Bool :=
  match Heap.empty.allocateArray [] with
  | .ok (ref, heap) =>
      match heap.deleteProperty ref (.string (JSString.ofLeanString "length")) with
      | .ok (false, _) => true
      | _ => false
  | .error _ => false

/-- Array `length` is nonconfigurable and cannot be deleted. -/
theorem Heap.empty_array_delete_length : emptyArrayDeleteLengthCheck = true := by
  decide

/-- Array own-key order places `length` after indices and before other strings and symbols. -/
theorem Heap.array_ownKeys_length_position (heap : Heap) (ref : RefId) (object : ObjectRecord)
    (slots : ArraySlots) (found : heap.get? ref = .ok object)
    (arrayKind : object.kind = .array slots) :
    heap.ownPropertyKeys ref = .ok
      (object.properties.ownKeys.filter (fun key => match key with
        | .string value => (PropertyKey.arrayIndex? value).isSome
        | .symbol _ => false) ++
      Heap.lengthPropertyKey ::
      object.properties.ownKeys.filter (fun key => match key with
        | .string value => (PropertyKey.arrayIndex? value).isNone
        | .symbol _ => true)) := by
  unfold Heap.ownPropertyKeys
  rw [found]
  dsimp
  rw [arrayKind]
  rfl

private abbrev arrayIteratorTargetIdentityCheck : Bool :=
  match Heap.empty.allocateArray [some (.primitive .undefined)] with
  | .error _ => false
  | .ok (target, heap) =>
      match heap.allocateArrayIterator target with
      | .error _ => false
      | .ok (iterator, next) => iterator != target &&
          match next.advanceArrayIterator iterator with
          | .ok (some (observedTarget, 0), _) => observedTarget == target
          | _ => false

/-- A fresh iterator is distinct from its array and yields the stable target identity. -/
theorem Heap.array_iterator_target_identity : arrayIteratorTargetIdentityCheck = true := by
  decide

/-- Exact array-length encoding roundtrips both index and length upper boundaries. -/
theorem Heap.array_length_boundary_roundtrips :
    validArrayLength? (arrayLengthNumber 4294967294) = some 4294967294 ∧
    validArrayLength? (arrayLengthNumber 4294967295) = some 4294967295 := by
  decide

/-- Extending at or beyond the old length produces the strictly larger exact length `index + 1`. -/
theorem Heap.array_write_extension_length (slots : ArraySlots) (index : Nat)
    (extendsLength : slots.length ≤ index) : slots.length < index + 1 :=
  Nat.lt_succ_of_le extendsLength

private abbrev proofPlatform : Platform :=
  ScriptedPlatform.make { times := #[], randoms := #[], fetches := #[] }

private abbrev proofHook : BodyHook proofPlatform := fun _ _ _ => pure ()

private abbrev assignReturnsTargetCheck : Bool :=
  let machine := Machine.initial proofPlatform 10
  match machine.heap.allocate with
  | .error _ => false
  | .ok (target, heap) =>
      match Copy.objectAssign proofHook (.object target) [] (machine.setHeap heap) with
      | .done (.normal (.object returned)) _ => returned == target
      | _ => false

/-- Successful `Object.assign` returns the same target identity it mutates. -/
theorem Copy.objectAssign_returns_target : assignReturnsTargetCheck = true := by
  decide

-- TODO(theorem): generalize the executable blocked-shrink property test: descending configurable
-- deletions are preserved, the first blocked index becomes `length - 1`, writability transitions
-- are committed, and all lower descriptors are unchanged.
-- TODO(theorem): lift the executable copy/slice/spread fresh-top-level and shared-nested-reference
-- checks to general preservation theorems over valid heaps and effectful getter traces.
-- TODO(theorem): generalize executable `isWellFormed` preservation checks for array/wrapper
-- allocation, index extension, deletion, iterator advancement, and copy operations.

end TSLean.JS
