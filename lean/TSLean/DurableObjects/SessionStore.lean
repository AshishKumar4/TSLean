-- TSLean.DurableObjects.SessionStore
import TSLean.Runtime.BrandedTypes
import TSLean.Runtime.Monad
import TSLean.Stdlib.HashMap

namespace TSLean.DO.SessionStore
open TSLean TSLean.Stdlib.HashMap

structure Session where
  userId    : UserId
  token     : SessionToken
  data      : List (String × String)
  createdAt : Nat
  expiresAt : Nat
  deriving Repr, BEq

def Session.isFresh (s : Session) (now : Nat) : Bool := now < s.expiresAt
def Session.extend  (s : Session) (ttlMs now : Nat) : Session := { s with expiresAt := now + ttlMs }
def Session.ttlRemaining (s : Session) (now : Nat) : Nat := if now < s.expiresAt then s.expiresAt - now else 0

abbrev SessionStore := AssocMap SessionToken Session

def SessionStore.empty : SessionStore := AssocMap.empty
def SessionStore.get (store : SessionStore) (tok : SessionToken) : Option Session := store.get? tok
def SessionStore.put (store : SessionStore) (s : Session) : SessionStore := store.insert s.token s
def SessionStore.delete (store : SessionStore) (tok : SessionToken) : SessionStore := store.erase tok

def SessionStore.getFresh (store : SessionStore) (tok : SessionToken) (now : Nat) : Option Session :=
  match store.get tok with
  | none   => none
  | some s => if s.isFresh now then some s else none

def SessionStore.prune (store : SessionStore) (now : Nat) : SessionStore :=
  { entries := store.entries.filter (fun (_, s) => s.isFresh now),
    nodup   := by apply List.Nodup.sublist _ store.nodup; apply List.Sublist.map; exact List.filter_sublist }

theorem no_stale_reads (store : SessionStore) (tok : SessionToken) (now : Nat)
    (s : Session) (h : store.getFresh tok now = some s) : s.isFresh now = true := by
  simp only [SessionStore.getFresh, SessionStore.get] at h
  split at h; · simp at h
  · split at h
    · next hf => simp only [Option.some.injEq] at h; rw [← h]; exact hf
    · simp at h

theorem put_then_get (store : SessionStore) (s : Session) :
    (store.put s).get s.token = some s := by
  simp [SessionStore.put, SessionStore.get, AssocMap.get?_insert_same]

theorem delete_then_get (store : SessionStore) (tok : SessionToken) :
    (store.delete tok).get tok = none := by
  simp [SessionStore.delete, SessionStore.get, AssocMap.get?_erase]

private theorem findSome_mem (l : List (SessionToken × Session)) (tok : SessionToken) (s : Session)
    (h : l.findSome? (fun p => if p.1 == tok then some p.2 else none) = some s) :
    ∃ p ∈ l, p.2 = s := by
  induction l with
  | nil => simp [List.findSome?] at h
  | cons hd tl ih =>
    simp only [List.findSome?] at h
    by_cases hcidk : (hd.1 == tok)
    · simp only [hcidk, ite_true] at h
      exact ⟨hd, List.mem_cons_self, Option.some_inj.mp h⟩
    · simp only [hcidk, Bool.not_true, ↓reduceIte, ite_false] at h
      obtain ⟨p, hp, heq⟩ := ih h
      exact ⟨p, List.mem_cons_of_mem _ hp, heq⟩

theorem prune_removes_expired (store : SessionStore) (tok : SessionToken) (now : Nat)
    (s : Session) (h : (store.prune now).get tok = some s) : s.isFresh now = true := by
  simp only [SessionStore.prune, SessionStore.get, AssocMap.get?] at h
  have ⟨p, hp, heq⟩ := findSome_mem _ tok s h
  simp only [List.mem_filter] at hp
  rw [← heq]; exact hp.2

theorem extend_refreshes (s : Session) (ttlMs now : Nat) (h : ttlMs > 0) :
    (s.extend ttlMs now).isFresh (now + ttlMs - 1) = true := by
  simp [Session.extend, Session.isFresh]; omega

-- Additional theorems

theorem set_then_get (store : SessionStore) (s : Session) :
    (store.put s).getFresh s.token (s.createdAt) =
    if s.isFresh s.createdAt then some s else none := by
  simp [SessionStore.getFresh, SessionStore.put, SessionStore.get, AssocMap.get?_insert_same]

theorem expired_not_found (store : SessionStore) (tok : SessionToken) (now : Nat)
    (h : store.getFresh tok now = none) : ∀ s, store.get tok = some s → ¬s.isFresh now := by
  intro s hget hfresh
  have hget2 : AssocMap.get? store tok = some s := hget
  simp only [SessionStore.getFresh, SessionStore.get] at h
  simp only [hget2, hfresh] at h
  simp at h

theorem ttl_decreases (s : Session) (now now' : Nat) (h : now ≤ now') :
    s.ttlRemaining now' ≤ s.ttlRemaining now := by
  simp only [Session.ttlRemaining]
  split <;> split <;> omega

theorem extend_increases_ttl (s : Session) (ttl now : Nat) :
    (s.extend ttl now).expiresAt = now + ttl := by
  simp [Session.extend]

theorem empty_get_none (tok : SessionToken) :
    SessionStore.empty.get tok = none := by
  simp [SessionStore.empty, SessionStore.get, AssocMap.get?_empty]

theorem put_preserves_other (store : SessionStore) (s : Session) (tok : SessionToken)
    (hne : tok ≠ s.token) :
    (store.put s).get tok = store.get tok := by
  simp only [SessionStore.put, SessionStore.get]
  exact AssocMap.get?_insert_diff store s.token tok s (Ne.symm hne)

theorem delete_preserves_other (store : SessionStore) (tok tok' : SessionToken) (hne : tok ≠ tok') :
    (store.delete tok).get tok' = store.get tok' := by
  simp only [SessionStore.delete, SessionStore.get, AssocMap.erase, AssocMap.get?]
  induction store.entries with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.filter_cons, List.findSome?]
    rcases Bool.eq_false_or_eq_true (hd.1 == tok) with hc | hc
    · -- hc : hd.1 == tok = true: filtered out; hd.1 ≠ tok'
      have hhdtok' : (hd.1 == tok') = false := by
        rw [Bool.eq_false_iff]; intro h
        exact hne (LawfulBEq.eq_of_beq hc ▸ LawfulBEq.eq_of_beq h)
      simp only [hc, Bool.not_true, ↓reduceIte, List.findSome?, hhdtok', ite_false]
      exact ih
    · -- hc : hd.1 == tok = false: kept
      simp only [hc, Bool.not_false, ↓reduceIte, List.findSome?]
      split
      · rfl
      · exact ih




-- Additional theorems (simplified for correctness)


theorem get_fresh_implies_fresh (store : SessionStore) (tok : SessionToken) (now : Nat)
    (s : Session) (h : store.getFresh tok now = some s) :
    s.isFresh now = true := no_stale_reads store tok now s h

theorem put_updates_get (store : SessionStore) (s : Session) :
    (store.put s).get s.token = some s := put_then_get store s

theorem getFresh_none_of_expired (store : SessionStore) (tok : SessionToken) (now : Nat)
    (s : Session) (hget : store.get tok = some s) (hexp : s.expiresAt ≤ now) :
    store.getFresh tok now = none := by
  simp [SessionStore.getFresh, hget, Session.isFresh, Nat.not_lt.mpr hexp]

theorem put_then_delete_empty (store : SessionStore) (s : Session) :
    ((store.put s).delete s.token).get s.token = none := by
  simp [SessionStore.delete, SessionStore.get, SessionStore.put, AssocMap.get?_erase]

theorem extend_always_fresh (s : Session) (now ttl : Nat) (h : ttl > 0) :
    (s.extend ttl now).isFresh now = true := by
  simp [Session.extend, Session.isFresh, h]

theorem get_empty (tok : SessionToken) : SessionStore.empty.get tok = none :=
  empty_get_none tok


end TSLean.DO.SessionStore
