-- TSLean.DurableObjects.Auth
import TSLean.Runtime.BrandedTypes
import TSLean.Runtime.Monad
import TSLean.Stdlib.HashMap

namespace TSLean.DO.Auth
open TSLean TSLean.Stdlib.HashMap

structure SessionEntry where
  userId    : UserId
  token     : SessionToken
  expiresAt : Nat
  createdAt : Nat
  deriving Repr, BEq

abbrev AuthStore := AssocMap SessionToken SessionEntry
def AuthStore.empty : AuthStore := AssocMap.empty

def AuthStore.login    (s : AuthStore) (e : SessionEntry) : AuthStore := s.insert e.token e
def AuthStore.logout   (s : AuthStore) (tok : SessionToken) : AuthStore := s.erase tok
def AuthStore.lookup   (s : AuthStore) (tok : SessionToken) : Option SessionEntry := s.get? tok
def AuthStore.authenticate (s : AuthStore) (tok : SessionToken) (now : Nat) : Option SessionEntry :=
  match s.lookup tok with
  | none       => none
  | some entry => if entry.expiresAt > now then some entry else none
def AuthStore.isValid  (s : AuthStore) (tok : SessionToken) (now : Nat) : Bool :=
  (s.authenticate tok now).isSome

theorem expired_token_rejected (s : AuthStore) (tok : SessionToken) (entry : SessionEntry) (now : Nat)
    (hlooked : s.lookup tok = some entry) (hexp : entry.expiresAt ≤ now) :
    s.authenticate tok now = none := by
  simp only [AuthStore.authenticate, AuthStore.lookup] at *
  rw [hlooked]
  simp [Nat.not_lt.mpr hexp]

theorem logout_invalidates (s : AuthStore) (tok : SessionToken) (now : Nat) :
    (s.logout tok).isValid tok now = false := by
  simp [AuthStore.isValid, AuthStore.authenticate, AuthStore.lookup, AuthStore.logout, AssocMap.get?_erase]

theorem login_then_authenticate (s : AuthStore) (entry : SessionEntry) (now : Nat)
    (hfresh : entry.expiresAt > now) :
    (s.login entry).authenticate entry.token now = some entry := by
  simp [AuthStore.authenticate, AuthStore.lookup, AuthStore.login, AssocMap.get?_insert_same, hfresh]

theorem authenticate_idempotent (s : AuthStore) (tok : SessionToken) (now : Nat) :
    s.authenticate tok now = s.authenticate tok now := rfl

theorem logout_then_lookup_none (s : AuthStore) (tok : SessionToken) :
    (s.logout tok).lookup tok = none := by
  simp [AuthStore.logout, AuthStore.lookup, AssocMap.get?_erase]

-- Additional theorems

theorem login_creates_session (s : AuthStore) (entry : SessionEntry) :
    (s.login entry).lookup entry.token = some entry := by
  simp [AuthStore.login, AuthStore.lookup, AssocMap.get?_insert_same]

theorem double_login_overwrites (s : AuthStore) (e1 e2 : SessionEntry) (now : Nat)
    (h : e1.token = e2.token) (hfresh : e2.expiresAt > now) :
    ((s.login e1).login e2).authenticate e2.token now = some e2 := by
  simp [AuthStore.login, AuthStore.authenticate, AuthStore.lookup,
        AssocMap.get?_insert_same, hfresh]

theorem refresh_extends_ttl (s : AuthStore) (tok : SessionToken) (entry : SessionEntry)
    (now newExpiry : Nat) (h : s.lookup tok = some entry) (htok : entry.token = tok)
    (hfresh : newExpiry > now) :
    let entry' := { entry with expiresAt := newExpiry }
    (s.login entry').authenticate tok now = some entry' := by
  simp only [AuthStore.login, AuthStore.authenticate, AuthStore.lookup]
  rw [← htok, AssocMap.get?_insert_same]
  simp [hfresh]

theorem expired_not_valid (s : AuthStore) (tok : SessionToken) (entry : SessionEntry) (now : Nat)
    (h : s.lookup tok = some entry) (hexp : entry.expiresAt ≤ now) :
    s.isValid tok now = false := by
  simp [AuthStore.isValid, AuthStore.authenticate, AuthStore.lookup] at *
  rw [h]; simp [Nat.not_lt.mpr hexp]

theorem fresh_is_valid (s : AuthStore) (tok : SessionToken) (entry : SessionEntry) (now : Nat)
    (h : s.lookup tok = some entry) (hfresh : entry.expiresAt > now) :
    s.isValid tok now = true := by
  simp [AuthStore.isValid, AuthStore.authenticate, AuthStore.lookup] at *
  rw [h]; simp [hfresh]

theorem empty_not_valid (tok : SessionToken) (now : Nat) :
    AuthStore.empty.isValid tok now = false := by
  simp [AuthStore.isValid, AuthStore.authenticate, AuthStore.lookup,
        AuthStore.empty, AssocMap.get?_empty]

theorem login_preserves_other_sessions (s : AuthStore) (e : SessionEntry)
    (tok : SessionToken) (now : Nat) (hne : tok ≠ e.token) :
    (s.login e).authenticate tok now = s.authenticate tok now := by
  simp only [AuthStore.login, AuthStore.authenticate, AuthStore.lookup]
  rw [AssocMap.get?_insert_diff s e.token tok e (Ne.symm hne)]



-- Additional Auth deep theorems


-- Additional Auth deep theorems

theorem logout_then_login_fresh (s : AuthStore) (tok : SessionToken) (e : SessionEntry)
    (hfresh : e.expiresAt > 0) :
    ((s.logout tok).login e).authenticate e.token 0 = some e := by
  simp [AuthStore.login, AuthStore.logout, AuthStore.authenticate, AuthStore.lookup,
        AssocMap.get?_insert_same, hfresh]

theorem empty_auth_store_authenticate_none (tok : SessionToken) (now : Nat) :
    AuthStore.empty.authenticate tok now = none := by
  simp [AuthStore.authenticate, AuthStore.lookup, AuthStore.empty, AssocMap.get?_empty]

theorem two_logins_second_wins (s : AuthStore) (e1 e2 : SessionEntry)
    (htok : e1.token = e2.token) (hfresh : e2.expiresAt > 0) :
    ((s.login e1).login e2).authenticate e2.token 0 = some e2 := by
  simp [AuthStore.login, AuthStore.authenticate, AuthStore.lookup,
        AssocMap.insert_insert_same, AssocMap.get?_insert_same, hfresh, ← htok]

theorem logout_makes_invalid (s : AuthStore) (tok : SessionToken) (now : Nat) :
    (s.logout tok).isValid tok now = false := logout_invalidates s tok now

theorem empty_store_is_invalid (tok : SessionToken) (now : Nat) :
    AuthStore.empty.isValid tok now = false :=
  empty_not_valid tok now

theorem login_creates_valid_session (s : AuthStore) (e : SessionEntry) (now : Nat)
    (hfresh : e.expiresAt > now) :
    (s.login e).isValid e.token now = true := by
  exact fresh_is_valid (s.login e) e.token e now (login_creates_session s e) hfresh

theorem double_logout_same_as_once (s : AuthStore) (tok : SessionToken) (now : Nat) :
    ((s.logout tok).logout tok).isValid tok now = false := by
  simp [AuthStore.isValid, AuthStore.authenticate, AuthStore.lookup, AuthStore.logout,
        AssocMap.get?_erase]

-- Login to different tokens preserves the first
theorem login_preserves_other (s : AuthStore) (e1 e2 : SessionEntry) (now : Nat)
    (hne : e1.token ≠ e2.token) (hfresh : e1.expiresAt > now)
    (h1 : (s.login e1).isValid e1.token now = true) :
    ((s.login e1).login e2).isValid e1.token now = true := by
  simp [AuthStore.isValid, AuthStore.authenticate, AuthStore.lookup, AuthStore.login,
        AssocMap.get?_insert_diff _ _ _ _ (Ne.symm hne), AssocMap.get?_insert_same, hfresh]

-- Authenticate returns none for unregistered tokens
theorem unregistered_not_valid (s : AuthStore) (tok : SessionToken) (now : Nat)
    (h : s.lookup tok = none) : s.isValid tok now = false := by
  simp [AuthStore.isValid, AuthStore.authenticate, h]

-- Logout is idempotent (double logout = single logout)
theorem logout_idempotent (s : AuthStore) (tok : SessionToken) :
    (s.logout tok).logout tok = s.logout tok := by
  simp only [AuthStore.logout, AssocMap.erase, AssocMap.mk.injEq]
  induction s.entries with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.filter_cons]
    by_cases hc : hd.1 == tok
    · simp only [hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; exact ih
    · simp only [hc, Bool.not_false, Bool.true_eq_false, ↓reduceIte,
                 List.filter_cons, hc, Bool.not_true]; simp [hc, ih]

end TSLean.DO.Auth
