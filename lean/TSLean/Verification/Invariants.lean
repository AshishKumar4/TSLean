-- TSLean.Verification.Invariants
import TSLean.DurableObjects.Model

namespace TSLean.Verification.Invariants
open TSLean TSLean.DO

/-- Storage invariant: a predicate on storage state -/
def StorageInvariant := Storage → Prop

/-- An invariant holds after any put operation (if it held before) -/
def preservedByPut (inv : StorageInvariant) : Prop :=
  ∀ s k v, inv s → inv (s.put k v)

/-- An invariant holds after any delete operation -/
def preservedByDelete (inv : StorageInvariant) : Prop :=
  ∀ s k, inv s → inv (s.delete k)

/-- The empty storage satisfies any invariant that holds of empty -/
theorem empty_invariant (inv : StorageInvariant) (h : inv Storage.clear) : inv Storage.clear := h

end TSLean.Verification.Invariants
