import TSLean.JS.OrdinaryObject

namespace TSLean.JS

/-- Failures while traversing a prototype chain. -/
inductive PrototypeFault where
  | heap (fault : HeapFault)
  | cycleOrFuelExhausted
  deriving DecidableEq

namespace Prototype

private def lookupWithFuel (heap : Heap) (key : PropertyKey) : Nat → RefId →
    Except PrototypeFault (Option (RefId × PropertyDescriptor))
  | 0, _ => .error .cycleOrFuelExhausted
  | fuel + 1, ref =>
      match heap.get? ref with
      | .error fault => .error (.heap fault)
      | .ok object =>
          match heap.getOwnProperty ref key with
          | .error fault => .error (.heap fault)
          | .ok (some descriptor) => .ok (some (ref, descriptor))
          | .ok none =>
              match object.prototype with
              | none => .ok none
              | some parent => lookupWithFuel heap key fuel parent

/-- Finds the nearest property; absence and exhausted malformed traversal are distinct. -/
def lookup (heap : Heap) (ref : RefId) (key : PropertyKey) :
    Except PrototypeFault (Option (RefId × PropertyDescriptor)) :=
  lookupWithFuel heap key (heap.size + 1) ref

private theorem lookupWithFuel_data_valueValid (heap : Heap) (key : PropertyKey)
    (fuel : Nat) (ref owner : RefId) (descriptor : DataDescriptor)
    (valid : heap.WellFormed)
    (found : lookupWithFuel heap key fuel ref = .ok (some (owner, .data descriptor))) :
    heap.valueValid descriptor.value = true := by
  induction fuel generalizing ref with
  | zero => simp [lookupWithFuel] at found
  | succ fuel ih =>
      unfold lookupWithFuel at found
      cases objectFound : heap.get? ref with
      | error fault => simp [objectFound] at found
      | ok object =>
          simp only [objectFound] at found
          cases ownFound : heap.getOwnProperty ref key with
          | error fault => simp [ownFound] at found
          | ok own =>
              simp only [ownFound] at found
              cases own with
              | some ownDescriptor =>
                  simp at found
                  obtain ⟨rfl, rfl⟩ := found
                  exact Heap.wellFormed_getOwnProperty_data_valueValid heap ref key descriptor valid
                    ownFound
              | none =>
                  cases parentEq : object.prototype with
                  | none => simp [parentEq] at found
                  | some parent => exact ih parent (by simpa [ownFound, parentEq] using found)

/-- Prototype lookup returns only heap-valid data descriptor values on a valid heap. -/
theorem lookup_data_valueValid (heap : Heap) (ref : RefId) (key : PropertyKey)
    (owner : RefId) (descriptor : DataDescriptor) (valid : heap.WellFormed)
    (found : lookup heap ref key = .ok (some (owner, .data descriptor))) :
    heap.valueValid descriptor.value = true :=
  lookupWithFuel_data_valueValid heap key (heap.size + 1) ref owner descriptor valid found

/-- Validity and acyclicity of all prototype chains. -/
def WellFormed (heap : Heap) : Prop := heap.WellFormed

end Prototype
end TSLean.JS
