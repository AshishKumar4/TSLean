-- TSLean.DurableObjects.Storage
-- Clean API over Model.lean, batch ops.
import TSLean.DurableObjects.Model

namespace TSLean.DO.StorageAPI
open TSLean TSLean.DO TSLean.Stdlib.HashMap

def batch_get (s : Storage) (ks : List StorageKey) : List (StorageKey × Option StorageValue) :=
  ks.map fun k => (k, s.get k)

def batch_put (s : Storage) (pairs : List (StorageKey × StorageValue)) : Storage :=
  pairs.foldl (fun acc (k, v) => acc.put k v) s

def batch_delete (s : Storage) (ks : List StorageKey) : Storage :=
  ks.foldl (fun acc k => acc.delete k) s

theorem batch_put_get (s : Storage) (k : StorageKey) (v : StorageValue) :
    (batch_put s [(k, v)]).get k = some v := by
  simp [batch_put, Storage.get_put_same]

theorem batch_put_preserves_other (s : Storage) (k k' : StorageKey) (v : StorageValue) (hne : k ≠ k') :
    (batch_put s [(k, v)]).get k' = s.get k' := by
  simp [batch_put, Storage.get_put_diff _ _ _ _ hne]

theorem batch_get_length (s : Storage) (ks : List StorageKey) :
    (batch_get s ks).length = ks.length := by
  simp [batch_get, List.length_map]

theorem batch_put_empty (s : Storage) :
    batch_put s [] = s := by simp [batch_put]

theorem batch_delete_empty (s : Storage) :
    batch_delete s [] = s := by simp [batch_delete]

theorem batch_put_single (s : Storage) (k : StorageKey) (v : StorageValue) :
    batch_put s [(k, v)] = s.put k v := by simp [batch_put]

theorem batch_delete_single (s : Storage) (k : StorageKey) :
    batch_delete s [k] = s.delete k := by simp [batch_delete]

theorem batch_put_append (s : Storage) (l1 l2 : List (StorageKey × StorageValue)) :
    batch_put s (l1 ++ l2) = batch_put (batch_put s l1) l2 := by
  simp [batch_put, List.foldl_append]

-- Helper: if k is absent in s, it remains absent after any further deletions
private theorem batch_delete_preserves_absent (s : Storage) (k : StorageKey) (ks : List StorageKey)
    (habs : s.contains k = false) : (batch_delete s ks).contains k = false := by
  induction ks generalizing s with
  | nil => exact habs
  | cons hd tl ih =>
    simp only [batch_delete, List.foldl_cons]
    apply ih
    by_cases heq : hd = k
    · -- hd = k: after deleting k, it's absent
      rw [heq]; exact Storage.not_contains_delete_same s k
    · -- hd ≠ k: deleting hd doesn't affect k
      simp only [Storage.contains, Storage.delete, Storage.get]
      rw [AssocMap.get?_erase_ne s hd k heq]
      exact habs

-- batch_delete_contains_false: after batch_delete including k, k is not contained.
theorem batch_delete_contains_false (s : Storage) (k : StorageKey) (ks : List StorageKey)
    (h : k ∈ ks) : (batch_delete s ks).contains k = false := by
  induction ks generalizing s with
  | nil => exact absurd h List.not_mem_nil
  | cons hd tl ih =>
    simp only [batch_delete, List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | ht
    · exact batch_delete_preserves_absent (s.delete k) k tl (Storage.not_contains_delete_same s k)
    · exact ih (s.delete hd) ht

theorem batch_get_covers (s : Storage) (k : StorageKey) (ks : List StorageKey)
    (h : k ∈ ks) : ∃ pair ∈ batch_get s ks, pair.1 = k := by
  simp only [batch_get]
  exact ⟨(k, s.get k), List.mem_map.mpr ⟨k, h, rfl⟩, rfl⟩

end TSLean.DO.StorageAPI
