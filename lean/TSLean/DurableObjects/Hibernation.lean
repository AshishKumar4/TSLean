-- TSLean.DurableObjects.Hibernation
import TSLean.DurableObjects.Model

namespace TSLean.DO.Hibernation
open TSLean TSLean.DO

structure Snapshot (σ : Type) where
  appState : σ
  storage  : Storage
  version  : Nat
  -- no Repr: Storage doesn't have Repr due to ByteArray

def Snapshot.take {σ} (state : DOState σ) (v : Nat) : Snapshot σ :=
  { appState := state.appState, storage := state.storage, version := v }

def Snapshot.restore {σ} (snap : Snapshot σ) : DOState σ :=
  { appState := snap.appState, storage := snap.storage }

theorem snapshot_restore_identity {σ} (state : DOState σ) (v : Nat) :
    (Snapshot.take state v).restore = state := rfl

theorem snapshot_storage_preserved {σ} (state : DOState σ) (v : Nat) (k : StorageKey) :
    ((Snapshot.take state v).restore.storage.get k) = state.storage.get k := rfl

theorem snapshot_version (state : DOState σ) (v : Nat) :
    (Snapshot.take state v).version = v := rfl

theorem snapshot_appState (state : DOState σ) (v : Nat) :
    (Snapshot.take state v).appState = state.appState := rfl

theorem restore_appState {σ} (snap : Snapshot σ) :
    snap.restore.appState = snap.appState := rfl

theorem restore_storage {σ} (snap : Snapshot σ) :
    snap.restore.storage = snap.storage := rfl

theorem snapshot_monotone_version {σ} (state : DOState σ) (v₁ v₂ : Nat) (h : v₁ ≤ v₂) :
    (Snapshot.take state v₁).version ≤ (Snapshot.take state v₂).version := h

theorem snapshot_content_eq {σ} (state : DOState σ) (v₁ v₂ : Nat) :
    (Snapshot.take state v₁).restore = (Snapshot.take state v₂).restore := rfl

theorem snapshot_roundtrip {σ} (snap : Snapshot σ) (v : Nat) :
    Snapshot.take snap.restore v = { snap with version := v } := rfl

theorem snapshot_put_get {σ} (state : DOState σ) (v : Nat) (k : StorageKey) (val : StorageValue) :
    ((Snapshot.take { state with storage := state.storage.put k val } v).restore.storage.get k) =
    some val := Storage.get_put_same state.storage k val

theorem two_snapshots_same_content {σ} (s1 s2 : DOState σ) (v : Nat)
    (h : s1.appState = s2.appState) (hs : s1.storage = s2.storage) :
    (Snapshot.take s1 v).restore = (Snapshot.take s2 v).restore := by
  simp [Snapshot.take, Snapshot.restore, h, hs]

-- Versioned snapshot comparison
theorem snapshot_version_lt_iff {σ} (state : DOState σ) (v₁ v₂ : Nat) :
    (Snapshot.take state v₁).version < (Snapshot.take state v₂).version ↔ v₁ < v₂ :=
  Iff.rfl

-- Snapshot equality: same state and version ↔ equal snapshots
theorem snapshot_eq_iff {σ} (state : DOState σ) (v1 v2 : Nat) :
    Snapshot.take state v1 = Snapshot.take state v2 ↔ v1 = v2 := by
  simp [Snapshot.take]

-- Restore is idempotent (restore ∘ take = id on DOState)
theorem take_restore_id {σ} (state : DOState σ) (v : Nat) :
    (Snapshot.take state v).restore = state := rfl

-- Snapshot preserves storage delete
theorem snapshot_delete_get {σ} (state : DOState σ) (v : Nat) (k : StorageKey) :
    ((Snapshot.take { state with storage := state.storage.delete k } v).restore.storage.get k) =
    none := Storage.get_delete_same state.storage k

-- Snapshots preserve key absence
theorem snapshot_absent_key {σ} (state : DOState σ) (v : Nat) (k : StorageKey)
    (h : state.storage.get k = none) :
    (Snapshot.take state v).restore.storage.get k = none := h

-- Multiple snapshot versions are independent
theorem snapshot_versions_independent {σ} (state : DOState σ) (v₁ v₂ : Nat) :
    (Snapshot.take state v₁).appState = (Snapshot.take state v₂).appState := rfl

-- Snapshot of updated state
theorem snapshot_after_put {σ} (state : DOState σ) (v : Nat) (k : StorageKey) (val : StorageValue) :
    (Snapshot.take state v).restore.storage.put k val =
    (Snapshot.take { state with storage := state.storage.put k val } v).restore.storage := rfl

end TSLean.DO.Hibernation
