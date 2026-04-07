-- TSLean.DurableObjects.Model
import TSLean.Runtime.Basic
import TSLean.Runtime.Monad
import TSLean.Stdlib.HashMap

namespace TSLean.DO
open TSLean TSLean.Stdlib.HashMap

inductive StorageValue where
  | svNull  : StorageValue
  | svBool  : Bool → StorageValue
  | svNum   : Float → StorageValue
  | svStr   : String → StorageValue
  | svBytes : ByteArray → StorageValue
  deriving BEq

abbrev StorageKey := String
abbrev Storage := AssocMap StorageKey StorageValue

inductive StorageOp where
  | get    : StorageKey → StorageOp
  | put    : StorageKey → StorageValue → StorageOp
  | delete : StorageKey → StorageOp
  | list   : StorageOp
  | clear  : StorageOp

inductive StorageResult where
  | gotValue : Option StorageValue → StorageResult
  | listed   : List StorageKey → StorageResult
  | modified : StorageResult
  | failed   : TSError → StorageResult

structure DOState (σ : Type) where
  appState : σ
  storage  : Storage

inductive DOEvent where
  | fetch   : String → DOEvent
  | alarm   : Nat → DOEvent
  | message : String → DOEvent
  | rpc     : String → String → DOEvent
  deriving Repr

inductive DOAction where
  | respond   : String → DOAction
  | schedule  : Nat → DOAction
  | emit      : String → DOAction
  | storageOp : StorageOp → DOAction
  | noOp      : DOAction

def Storage.get (s : Storage) (k : StorageKey) : Option StorageValue := s.get? k
def Storage.put (s : Storage) (k : StorageKey) (v : StorageValue) : Storage := s.insert k v
def Storage.delete (s : Storage) (k : StorageKey) : Storage := s.erase k
def Storage.keys (s : Storage) : List StorageKey := AssocMap.keys s
def Storage.clear : Storage := AssocMap.empty
def Storage.contains (s : Storage) (k : StorageKey) : Bool := (s.get? k).isSome

theorem Storage.get_put_same (s : Storage) (k : StorageKey) (v : StorageValue) :
    (s.put k v).get k = some v := AssocMap.get?_insert_same s k v

theorem Storage.get_put_diff (s : Storage) (k k' : StorageKey) (v : StorageValue) (hne : k ≠ k') :
    (s.put k v).get k' = s.get k' := AssocMap.get?_insert_diff s k k' v hne

theorem Storage.get_delete_same (s : Storage) (k : StorageKey) :
    (s.delete k).get k = none := AssocMap.get?_erase s k

theorem Storage.get_clear (k : StorageKey) : Storage.clear.get k = none := AssocMap.get?_empty k
theorem Storage.keys_nodup (s : Storage) : (Storage.keys s).Nodup := AssocMap.keys_nodup s
theorem Storage.contains_iff_get_isSome (s : Storage) (k : StorageKey) :
    s.contains k = (s.get k).isSome := rfl
theorem Storage.contains_put_same (s : Storage) (k : StorageKey) (v : StorageValue) :
    (s.put k v).contains k = true := by
  simp [Storage.contains, Storage.put, AssocMap.get?_insert_same]
theorem Storage.not_contains_delete_same (s : Storage) (k : StorageKey) :
    (s.delete k).contains k = false := by
  simp [Storage.contains, Storage.delete, AssocMap.get?_erase]

-- Additional Storage theorems

-- put_put_same: second put to same key wins
theorem Storage.put_put_same (s : Storage) (k : StorageKey) (v1 v2 : StorageValue) :
    (s.put k v1).put k v2 = s.put k v2 :=
  AssocMap.insert_insert_same s k v1 v2

-- delete_put_same: delete after put for same key = delete before put
theorem Storage.delete_put_same (s : Storage) (k : StorageKey) (v : StorageValue) :
    (s.put k v).delete k = s.delete k :=
  AssocMap.erase_insert_same s k v

theorem Storage.get_put_same_val (s : Storage) (k : StorageKey) (v : StorageValue) :
    (s.put k v).get k = some v := Storage.get_put_same s k v

theorem Storage.put_preserves_other_keys (s : Storage) (k k' : StorageKey) (v : StorageValue)
    (hne : k ≠ k') (h : s.get k' = some v) :
    (s.put k v).get k' = some v := by
  rw [Storage.get_put_diff _ _ _ _ hne]; exact h

theorem Storage.clear_contains_false (k : StorageKey) :
    Storage.clear.contains k = false := by
  simp [Storage.contains, Storage.clear, AssocMap.get?_empty]

-- keys_after_put: after putting k, k is in the key list
theorem Storage.keys_after_put (s : Storage) (k : StorageKey) (v : StorageValue) :
    k ∈ (s.put k v).keys := by
  simp only [Storage.keys, AssocMap.keys, Storage.put]
  -- Use contains ↔ get? isSome
  have hc : (s.insert k v).contains k = true := by
    simp [AssocMap.contains, AssocMap.get?_insert_same]
  simp only [AssocMap.contains, AssocMap.get?] at hc
  -- contains = true means k is in entries.map Prod.fst (via findSome?)
  simp only [List.mem_map]
  -- Extract member from findSome? = isSome result
  rw [List.findSome?_isSome_iff] at hc
  obtain ⟨p, hp, hpk⟩ := hc
  exact ⟨p, hp, by
    simp only [Option.isSome_iff_ne_none] at hpk
    split at hpk
    · exact LawfulBEq.eq_of_beq ‹_›
    · simp at hpk⟩

theorem DOEvent.fetch_ne_alarm : ∀ (s : String) (n : Nat), DOEvent.fetch s ≠ DOEvent.alarm n := by
  intro s n h; cases h

theorem DOEvent.alarm_ne_message : ∀ (n : Nat) (s : String), DOEvent.alarm n ≠ DOEvent.message s := by
  intro n s h; cases h

-- Additional Storage theorems (non-duplicate)
-- put is idempotent on same key (alias)
theorem Storage.put_put_idempotent (s : Storage) (k : StorageKey) (v1 v2 : StorageValue) :
    (s.put k v1).put k v2 = s.put k v2 :=
  Storage.put_put_same s k v1 v2

-- delete then get same key returns none (alias)
theorem Storage.delete_get_none (s : Storage) (k : StorageKey) :
    (s.delete k).get? k = none :=
  Storage.get_delete_same s k

-- put doesn't affect other keys
theorem Storage.put_other_key (s : Storage) (k k' : StorageKey) (v : StorageValue)
    (hne : k ≠ k') :
    (s.put k v).get? k' = s.get? k' :=
  Storage.get_put_diff s k k' v hne

-- clear has no keys
theorem Storage.clear_no_keys : Storage.clear.keys = [] := by
  simp [Storage.clear, Storage.keys, AssocMap.empty, AssocMap.keys]

-- A key after put is in the keys list
theorem Storage.key_in_keys_after_put (s : Storage) (k : StorageKey) (v : StorageValue) :
    k ∈ (s.put k v).keys :=
  Storage.keys_after_put s k v

-- StorageValue equality: null ≠ bool
theorem StorageValue.null_ne_bool (b : Bool) : StorageValue.svNull ≠ StorageValue.svBool b :=
  fun h => by cases h

-- StorageValue bool ≠ null
theorem StorageValue.bool_ne_null (b : Bool) : StorageValue.svBool b ≠ StorageValue.svNull :=
  fun h => by cases h

-- Storage: contains implies get is some
theorem Storage.get_of_contains (s : Storage) (k : StorageKey) (h : s.contains k = true) :
    ∃ v, s.get? k = some v := by
  simp only [Storage.contains, Option.isSome_iff_ne_none] at h
  exact ⟨_, (Option.ne_none_iff_exists.mp h).choose_spec.symm⟩

-- StorageValue equality: num ≠ str
theorem StorageValue.num_ne_str (f : Float) (s : String) :
    StorageValue.svNum f ≠ StorageValue.svStr s := by
  intro h; cases h

end TSLean.DO
