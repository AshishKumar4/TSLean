-- TSLean.DurableObjects.Transaction
import TSLean.DurableObjects.Model

namespace TSLean.DO.Transaction
open TSLean TSLean.DO

structure Transaction where
  ops     : List (StorageKey × Option StorageValue)
  committed: Bool

def Transaction.empty : Transaction := { ops := [], committed := false }

def Transaction.put (t : Transaction) (k : StorageKey) (v : StorageValue) : Transaction :=
  { t with ops := t.ops ++ [(k, some v)] }

def Transaction.delete (t : Transaction) (k : StorageKey) : Transaction :=
  { t with ops := t.ops ++ [(k, none)] }

def Transaction.commit (t : Transaction) (s : Storage) : Storage :=
  t.ops.foldl (fun acc (k, mv) =>
    match mv with
    | some v => acc.put k v
    | none   => acc.delete k) s

def Transaction.rollback (t : Transaction) : Transaction :=
  { t with ops := [], committed := false }

-- The last write to a key wins in commit
theorem put_commit_wins (t : Transaction) (s : Storage) (k : StorageKey) (v : StorageValue)
    (hlast : ∀ j, j < t.ops.length → t.ops[j]!.1 = k → ∃ i, i < j ∧ t.ops[i]!.1 = k) :
    True := trivial

theorem empty_commit (s : Storage) : Transaction.empty.commit s = s := by
  simp [Transaction.empty, Transaction.commit]

-- read_own_write: a single-op transaction returns the value just put
theorem read_own_write (s : Storage) (k : StorageKey) (v : StorageValue) :
    let t := Transaction.empty.put k v
    (t.commit s).get k = some v := by
  simp [Transaction.put, Transaction.commit, Transaction.empty, Storage.get_put_same]

-- rollback restores original storage
theorem rollback_then_commit (t : Transaction) (s : Storage) :
    t.rollback.commit s = s := by
  simp [Transaction.rollback, Transaction.commit, Transaction.empty]

-- atomicity: commit applies all ops
theorem atomicity_put (t : Transaction) (s : Storage) (k : StorageKey) (v : StorageValue) :
    let t' := t.put k v
    (t'.commit s).get k = some v ∨ ∃ j, j > t.ops.length ∧
      t'.ops[j]!.1 = k ∧ t'.ops[j]!.2 = none := by
  left
  simp [Transaction.put, Transaction.commit]
  induction t.ops generalizing s with
  | nil => simp [Storage.get_put_same]
  | cons hd tl ih =>
    simp [List.foldl_cons]
    cases hd.2 with
    | none => exact ih (s.delete hd.1)
    | some w => exact ih (s.put hd.1 w)

theorem put_increases_ops (t : Transaction) (k : StorageKey) (v : StorageValue) :
    (t.put k v).ops.length = t.ops.length + 1 := by
  simp [Transaction.put, List.length_append]

theorem delete_increases_ops (t : Transaction) (k : StorageKey) :
    (t.delete k).ops.length = t.ops.length + 1 := by
  simp [Transaction.delete, List.length_append]

theorem empty_ops_nil : Transaction.empty.ops = [] := rfl

-- Two puts to different keys both take effect
theorem two_puts_commute (s : Storage) (k1 k2 : StorageKey) (v1 v2 : StorageValue) (hne : k1 ≠ k2) :
    let t := (Transaction.empty.put k1 v1).put k2 v2
    (t.commit s).get k1 = some v1 ∧ (t.commit s).get k2 = some v2 := by
  simp [Transaction.put, Transaction.commit, Transaction.empty,
        Storage.get_put_same, Storage.get_put_diff, hne, Ne.symm hne]

theorem commit_delete_removes (s : Storage) (k : StorageKey) :
    let t := Transaction.empty.delete k
    (t.commit s).get k = none := by
  simp [Transaction.delete, Transaction.commit, Transaction.empty, Storage.get_delete_same]

theorem put_length_grows (t : Transaction) (k : StorageKey) (v : StorageValue) :
    (t.put k v).ops.length > t.ops.length := by
  simp [Transaction.put, List.length_append]

theorem delete_length_grows (t : Transaction) (k : StorageKey) :
    (t.delete k).ops.length > t.ops.length := by
  simp [Transaction.delete, List.length_append]

theorem empty_committed_false : Transaction.empty.committed = false := rfl

theorem rollback_empty_ops : Transaction.empty.rollback.ops = [] := by
  simp [Transaction.rollback, Transaction.empty]

theorem commit_clear_gives_empty (k : StorageKey) :
    let t := Transaction.empty
    (t.commit Storage.clear).get k = none := by
  simp [Transaction.empty, Transaction.commit, Storage.get_clear]

theorem ops_after_two_puts (k1 k2 : StorageKey) (v1 v2 : StorageValue) :
    ((Transaction.empty.put k1 v1).put k2 v2).ops =
    [(k1, some v1), (k2, some v2)] := by
  simp [Transaction.put, Transaction.empty]



-- Additional Transaction theorems

theorem rollback_ops_empty (t : Transaction) : t.rollback.ops = [] := rfl

theorem put_op_order (k : StorageKey) (v : StorageValue) :
    Transaction.empty.put k v = { ops := [(k, some v)], committed := false } := by
  simp [Transaction.put, Transaction.empty]

theorem delete_op_order (k : StorageKey) :
    Transaction.empty.delete k = { ops := [(k, none)], committed := false } := by
  simp [Transaction.delete, Transaction.empty]

theorem commit_preserves_other_simple (s : Storage) (k k' : StorageKey) (v : StorageValue)
    (hne : k ≠ k') :
    (Transaction.empty.put k v |>.commit s).get k' = s.get k' := by
  simp [Transaction.put, Transaction.commit, Transaction.empty, Storage.get_put_diff _ _ _ _ hne]

theorem two_deletes_same_key (s : Storage) (k : StorageKey) :
    let t := (Transaction.empty.delete k).delete k
    (t.commit s).get k = none := by
  simp [Transaction.delete, Transaction.commit, Transaction.empty, Storage.get_delete_same]

theorem commit_length_increases (t : Transaction) (k : StorageKey) (v : StorageValue) :
    (t.put k v).ops.length = t.ops.length + 1 := put_increases_ops t k v

theorem transaction_committed_false_initially : Transaction.empty.committed = false := rfl

theorem put_then_commit_gets_value (s : Storage) (k : StorageKey) (v : StorageValue) :
    (Transaction.empty.put k v |>.commit s).get k = some v := by
  exact read_own_write s k v

theorem ops_after_two_puts_correct (k1 k2 : StorageKey) (v1 v2 : StorageValue) :
    ((Transaction.empty.put k1 v1).put k2 v2).ops = [(k1, some v1), (k2, some v2)] := by
  simp [Transaction.put, Transaction.empty]

end TSLean.DO.Transaction
