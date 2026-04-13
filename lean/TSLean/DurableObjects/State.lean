-- TSLean.DurableObjects.State
import TSLean.DurableObjects.Model

namespace TSLean.DO.State
open TSLean TSLean.DO

structure Env where
  bindings : List (String × String)
  deriving Repr

def Env.get (env : Env) (key : String) : Option String :=
  (env.bindings.find? (fun (k, _) => k == key)).map Prod.snd

structure DurableObjectState (σ : Type) where
  id      : String
  storage : Storage
  appState: σ
  env     : Env

def DurableObjectState.get {σ} (dos : DurableObjectState σ) (k : StorageKey) :=
  dos.storage.get k
def DurableObjectState.put {σ} (dos : DurableObjectState σ) (k : StorageKey) (v : StorageValue) :=
  { dos with storage := dos.storage.put k v }
def DurableObjectState.delete {σ} (dos : DurableObjectState σ) (k : StorageKey) :=
  { dos with storage := dos.storage.delete k }

theorem DurableObjectState.get_put {σ} (dos : DurableObjectState σ) (k : StorageKey) (v : StorageValue) :
    (dos.put k v).get k = some v := Storage.get_put_same dos.storage k v

theorem DurableObjectState.get_put_diff {σ} (dos : DurableObjectState σ) (k k' : StorageKey)
    (v : StorageValue) (hne : k ≠ k') :
    (dos.put k v).get k' = dos.get k' := Storage.get_put_diff dos.storage k k' v hne

theorem DurableObjectState.get_delete {σ} (dos : DurableObjectState σ) (k : StorageKey) :
    (dos.delete k).get k = none := Storage.get_delete_same dos.storage k

-- put_put_same: second put wins (follows from Storage.put_put_same)
theorem DurableObjectState.put_put_same {σ} (dos : DurableObjectState σ) (k : StorageKey)
    (v1 v2 : StorageValue) :
    (dos.put k v1).put k v2 = dos.put k v2 := by
  simp only [DurableObjectState.put]
  congr 1
  exact Storage.put_put_same dos.storage k v1 v2

theorem Env.get_empty (key : String) : (Env.mk []).get key = none := by simp [Env.get]

theorem Env.get_cons_same (k : String) (v : String) (rest : List (String × String)) :
    (Env.mk ((k, v) :: rest)).get k = some v := by
  simp [Env.get, List.find?, beq_self_eq_true]

theorem Env.get_cons_diff (k k' : String) (v : String) (rest : List (String × String))
    (hne : k ≠ k') :
    (Env.mk ((k, v) :: rest)).get k' = (Env.mk rest).get k' := by
  simp [Env.get, List.find?, show (k == k') = false from beq_false_of_ne hne]

theorem DurableObjectState.id_preserved_after_put {σ} (dos : DurableObjectState σ)
    (k : StorageKey) (v : StorageValue) :
    (dos.put k v).id = dos.id := rfl

theorem DurableObjectState.appState_preserved_after_put {σ} (dos : DurableObjectState σ)
    (k : StorageKey) (v : StorageValue) :
    (dos.put k v).appState = dos.appState := rfl

theorem DurableObjectState.env_preserved_after_put {σ} (dos : DurableObjectState σ)
    (k : StorageKey) (v : StorageValue) :
    (dos.put k v).env = dos.env := rfl

-- put then delete at different key: the get? values agree for all keys.
-- The two operations commute on get? since they touch different keys.
theorem DurableObjectState.put_delete_diff_get {σ} (dos : DurableObjectState σ)
    (k k' key : StorageKey) (v : StorageValue) (hne : k ≠ k') :
    ((dos.put k v).delete k').get key = ((dos.delete k').put k v).get key := by
  simp only [DurableObjectState.put, DurableObjectState.delete, DurableObjectState.get,
             Storage.get, Storage.put, Storage.delete]
  by_cases hk1 : key = k
  · -- key = k: both sides return some v (erase k' doesn't touch k since k ≠ k')
    rw [hk1, TSLean.Stdlib.HashMap.AssocMap.get?_erase_ne _ k' k (Ne.symm hne),
        TSLean.Stdlib.HashMap.AssocMap.get?_insert_same,
        TSLean.Stdlib.HashMap.AssocMap.get?_insert_same]
  · by_cases hk2 : key = k'
    · -- key = k': both sides return none (erase removes k'; insert k v doesn't touch k')
      rw [hk2, TSLean.Stdlib.HashMap.AssocMap.get?_erase,
          TSLean.Stdlib.HashMap.AssocMap.get?_insert_diff _ k k' v hne,
          TSLean.Stdlib.HashMap.AssocMap.get?_erase]
    · -- key ≠ k and key ≠ k': both sides equal original get
      rw [TSLean.Stdlib.HashMap.AssocMap.get?_erase_ne _ k' key (Ne.symm hk2),
          TSLean.Stdlib.HashMap.AssocMap.get?_insert_diff _ k key v (Ne.symm hk1),
          TSLean.Stdlib.HashMap.AssocMap.get?_insert_diff _ k key v (Ne.symm hk1),
          TSLean.Stdlib.HashMap.AssocMap.get?_erase_ne _ k' key (Ne.symm hk2)]

theorem DurableObjectState.get_after_delete {σ} (dos : DurableObjectState σ) (k : StorageKey) :
    (dos.delete k).get k = none := Storage.get_delete_same dos.storage k

theorem DurableObjectState.storage_put_contains {σ} (dos : DurableObjectState σ)
    (k : StorageKey) (v : StorageValue) :
    (dos.put k v).storage.contains k = true := Storage.contains_put_same dos.storage k v

theorem DurableObjectState.storage_delete_not_contains {σ} (dos : DurableObjectState σ)
    (k : StorageKey) :
    (dos.delete k).storage.contains k = false := Storage.not_contains_delete_same dos.storage k

theorem Env.get_nonempty (env : Env) (key : String) (h : env.get key = some v) :
    (env.bindings.find? (fun (k, _) => k == key)).isSome = true := by
  simp [Env.get] at h
  exact Option.isSome_iff_ne_none.mpr (fun hn => by simp [hn] at h)

theorem DurableObjectState.sequential_puts {σ} (dos : DurableObjectState σ)
    (k : StorageKey) (v1 v2 : StorageValue) :
    ((dos.put k v1).put k v2).get k = some v2 := by
  simp [DurableObjectState.put, DurableObjectState.get, Storage.get_put_same]

end TSLean.DO.State
