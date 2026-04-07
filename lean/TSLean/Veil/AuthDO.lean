-- TSLean.Veil.AuthDO
-- Authentication DO: session lifecycle as a transition system.
-- Sessions go through: (nonexistent) → active → revoked | expired.
-- Safety: revoked/expired sessions cannot authenticate.

import TSLean.Veil.Core

namespace TSLean.Veil.AuthDO
open TSLean.Veil TransitionSystem

/-! ## Session lifecycle -/

inductive SessionStatus where
  | active  | expired | revoked
  deriving Repr, BEq, DecidableEq

/-! ## A simple model: single session per token -/

structure SessionInfo where
  userId    : String
  status    : SessionStatus
  expiresAt : Nat
  deriving Repr

/-! ## State -/

structure State where
  /-- Active sessions: token → info -/
  sessions : List (String × SessionInfo)
  /-- Current time -/
  now      : Nat
  /-- Max TTL -/
  maxTTL   : Nat
  deriving Repr

/-! ## Helpers -/

def State.lookup (s : State) (tok : String) : Option SessionInfo :=
  (s.sessions.find? (fun (t, _) => t == tok)).map Prod.snd

def State.isAuthenticated (s : State) (tok : String) : Bool :=
  match s.lookup tok with
  | some si => si.status == SessionStatus.active && decide (s.now < si.expiresAt)
  | none    => false

/-! ## Initial condition -/

def initState (s : State) : Prop :=
  s.sessions = [] ∧ s.now = 0 ∧ s.maxTTL > 0

/-! ## Assumptions -/

def assumptions (s : State) : Prop := s.maxTTL > 0

/-! ## Actions -/

def login (tok userId : String) (ttl : Nat) (pre post : State) : Prop :=
  ttl > 0 ∧ ttl ≤ pre.maxTTL ∧
  post.sessions = (tok, { userId, status := SessionStatus.active,
                           expiresAt := pre.now + ttl }) :: pre.sessions ∧
  post.now = pre.now ∧ post.maxTTL = pre.maxTTL

def logout (tok : String) (pre post : State) : Prop :=
  post.sessions = (pre.sessions.map fun (t, si) =>
    if t == tok then (t, { si with status := SessionStatus.revoked }) else (t, si)) ∧
  post.now = pre.now ∧ post.maxTTL = pre.maxTTL

def expire (tok : String) (pre post : State) : Prop :=
  (match pre.lookup tok with
   | some si => si.status == SessionStatus.active ∧ si.expiresAt ≤ pre.now
   | none => False) ∧
  post.sessions = (pre.sessions.map fun (t, si) =>
    if t == tok then (t, { si with status := SessionStatus.expired }) else (t, si)) ∧
  post.now = pre.now ∧ post.maxTTL = pre.maxTTL

def tick (delta : Nat) (pre post : State) : Prop :=
  delta > 0 ∧ post.now = pre.now + delta ∧
  post.sessions = pre.sessions ∧ post.maxTTL = pre.maxTTL

def next (pre post : State) : Prop :=
  (∃ tok uid ttl, login tok uid ttl pre post) ∨
  (∃ tok, logout tok pre post) ∨
  (∃ tok, expire tok pre post) ∨
  (∃ d, tick d pre post)

/-! ## Safety: revoked/expired tokens don't authenticate -/

def safe (s : State) : Prop :=
  ∀ tok si, s.lookup tok = some si →
    si.status = SessionStatus.revoked → s.isAuthenticated tok = false

/-! ## Invariant -/

def inv (s : State) : Prop :=
  -- Revoked sessions don't authenticate
  (∀ tok si, s.lookup tok = some si →
    si.status = SessionStatus.revoked → s.isAuthenticated tok = false) ∧
  -- Expired sessions don't authenticate
  (∀ tok si, s.lookup tok = some si →
    si.status = SessionStatus.expired → s.isAuthenticated tok = false) ∧
  -- Active sessions have future expiry
  (∀ tok si, s.lookup tok = some si →
    si.status = SessionStatus.active → s.isAuthenticated tok = true →
    s.now < si.expiresAt) ∧
  s.maxTTL > 0

/-! ## Instance -/

instance : TransitionSystem State where
  init        := initState
  assumptions := assumptions
  next        := next
  safe        := safe
  inv         := inv

/-! ## Verification -/

theorem inv_implies_safe : invSafe (σ := State) :=
  fun s _ hinv => hinv.1

theorem init_establishes_inv : invInit (σ := State) := by
  intro s hassu ⟨hsess, _, _⟩
  refine ⟨?_, ?_, ?_, hassu⟩
  all_goals {
    intro tok si hlook
    simp [State.lookup, hsess] at hlook
  }

-- All three invariant properties follow directly from isAuthenticated definition.
-- isAuthenticated = (status == active) && decide (now < expiresAt)
-- So: revoked/expired → !authenticated; active → authenticated → now < expiresAt

-- Key: isAuthenticated checks si.status == active && decide (now < expiresAt)
-- If status ≠ active, the && short-circuits to false
private theorem auth_false_of_not_active (s : State) (tok : String) (si : SessionInfo)
    (hlook : s.lookup tok = some si) (hne : si.status ≠ SessionStatus.active) :
    s.isAuthenticated tok = false := by
  simp only [State.isAuthenticated, hlook]
  cases hst : si.status
  · exact absurd hst hne
  · rfl  -- (expired == active) = false reduces to false && _ = false
  · rfl

private theorem auth_lt_of_true (s : State) (tok : String) (si : SessionInfo)
    (hlook : s.lookup tok = some si) (hauth : s.isAuthenticated tok = true) :
    s.now < si.expiresAt := by
  simp only [State.isAuthenticated, hlook] at hauth
  obtain ⟨_, hdec⟩ := Bool.and_eq_true_iff.mp hauth
  exact of_decide_eq_true hdec

-- All invariant cases follow from auth_false_of_not_active and auth_lt_of_true
private def inv_of_maxTTL (s : State) (hmax : s.maxTTL > 0) : inv s :=
  ⟨fun tok si hlook hrev =>
    auth_false_of_not_active s tok si hlook (by rw [hrev]; decide),
   fun tok si hlook hexp =>
    auth_false_of_not_active s tok si hlook (by rw [hexp]; decide),
   fun tok si hlook _ hauth => auth_lt_of_true s tok si hlook hauth,
   hmax⟩

theorem logout_preserves_inv (tok : String) (pre post : State)
    (hpre : inv pre) (h : logout tok pre post) : inv post :=
  inv_of_maxTTL post (h.2.2 ▸ hpre.2.2.2)

theorem inv_consecution : invConsecution (σ := State) := by
  intro pre post _ hinv hnext
  have hmax := hinv.2.2.2
  rcases hnext with ⟨tok, uid, ttl, hlog⟩ | ⟨tok, hlo⟩ | ⟨tok, hexp⟩ | ⟨delta, htick⟩
  · exact inv_of_maxTTL post (hlog.2.2.2.2 ▸ hmax)
  · exact logout_preserves_inv tok pre post hinv hlo
  · exact inv_of_maxTTL post (hexp.2.2.2 ▸ hmax)
  · exact inv_of_maxTTL post (htick.2.2.2 ▸ hmax)

theorem assumptions_invariant : isInvariant (σ := State) TransitionSystem.assumptions := by
  intro s hr
  induction hr with
  | init s hi =>
    simp only [TransitionSystem.assumptions, assumptions]; exact hi.2.2
  | step s s' _ hn ih =>
    simp only [TransitionSystem.assumptions, assumptions] at ih ⊢
    rcases hn with ⟨_, _, _, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩
    · rw [h.2.2.2.2]; exact ih
    · rw [h.2.2]; exact ih
    · rw [h.2.2.2]; exact ih
    · rw [h.2.2.2]; exact ih

theorem safety_holds : isInvariant (σ := State) TransitionSystem.safe :=
  safe_of_invInductive assumptions_invariant ⟨init_establishes_inv, inv_consecution⟩ inv_implies_safe

/-! ## Additional theorems -/

theorem lookup_empty (tok : String) :
    (⟨[], n, m⟩ : State).lookup tok = none := by
  simp [State.lookup]

theorem isAuthenticated_empty (tok : String) :
    (⟨[], n, m⟩ : State).isAuthenticated tok = false := by
  simp [State.isAuthenticated, State.lookup]

theorem login_creates_session (tok uid : String) (ttl : Nat) (pre post : State)
    (h : login tok uid ttl pre post) :
    post.sessions.length = pre.sessions.length + 1 := by
  obtain ⟨_, _, hsess, _, _⟩ := h; simp [hsess]

theorem tick_preserves_sessions (delta : Nat) (pre post : State)
    (h : tick delta pre post) :
    post.sessions = pre.sessions := h.2.2.1

theorem tick_advances_time (delta : Nat) (pre post : State)
    (h : tick delta pre post) :
    post.now = pre.now + delta := h.2.1

theorem maxTTL_preserved_by_login (tok uid : String) (ttl : Nat) (pre post : State)
    (h : login tok uid ttl pre post) :
    post.maxTTL = pre.maxTTL := h.2.2.2.2

theorem ttl_bounded_by_maxTTL (tok uid : String) (ttl : Nat) (pre post : State)
    (h : login tok uid ttl pre post) :
    ttl ≤ pre.maxTTL := h.2.1

theorem active_session_requires_positive_ttl (tok uid : String) (ttl : Nat) (pre post : State)
    (h : login tok uid ttl pre post) :
    ttl > 0 := h.1

theorem no_sessions_initially : initState s → s.sessions = [] :=
  fun h => h.1

theorem revoked_not_authenticated (s : State)
    (hinv : inv s) (tok : String) (si : SessionInfo)
    (hlook : s.lookup tok = some si) (hrev : si.status = SessionStatus.revoked) :
    s.isAuthenticated tok = false := hinv.1 tok si hlook hrev

theorem expired_not_authenticated (s : State)
    (hinv : inv s) (tok : String) (si : SessionInfo)
    (hlook : s.lookup tok = some si) (hexp : si.status = SessionStatus.expired) :
    s.isAuthenticated tok = false := hinv.2.1 tok si hlook hexp

-- maxTTL is positive for all reachable states
theorem maxTTL_positive (s : State) (hr : reachable s) : s.maxTTL > 0 :=
  assumptions_invariant s hr

-- Sessions list grows monotonically on login
theorem login_sessions_grow (tok uid : String) (ttl : Nat) (pre post : State)
    (h : login tok uid ttl pre post) :
    pre.sessions.length < post.sessions.length := by
  obtain ⟨_, _, hsess, _, _⟩ := h; simp [hsess]

-- Tick doesn't change session count
theorem tick_sessions_unchanged (delta : Nat) (pre post : State)
    (h : tick delta pre post) :
    post.sessions.length = pre.sessions.length := by
  rw [h.2.2.1]

-- Logout maps sessions (length unchanged)
theorem logout_same_session_count (tok : String) (pre post : State)
    (h : logout tok pre post) :
    post.sessions.length = pre.sessions.length := by
  obtain ⟨hsess, _, _⟩ := h; simp [hsess]

-- Expire maps sessions (length unchanged)
theorem expire_same_session_count (tok : String) (pre post : State)
    (h : expire tok pre post) :
    post.sessions.length = pre.sessions.length := by
  obtain ⟨_, hsess, _, _⟩ := h; simp [hsess]

-- Authenticated sessions have future expiry (via the invariant)
theorem authenticated_has_future_expiry (s : State) (hr : reachable s)
    (tok : String) (si : SessionInfo)
    (hlook : s.lookup tok = some si) (hauth : s.isAuthenticated tok = true) :
    s.now < si.expiresAt :=
  auth_lt_of_true s tok si hlook hauth

-- The now field increases monotonically
theorem now_nondecreasing (pre post : State) (h : next pre post) :
    post.now ≥ pre.now := by
  rcases h with ⟨_, _, _, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩
  · exact h.2.2.2.1 ▸ Nat.le_refl _  -- login: post.now = pre.now
  · exact h.2.1 ▸ Nat.le_refl _       -- logout: post.now = pre.now
  · exact h.2.2.1 ▸ Nat.le_refl _     -- expire: post.now = pre.now
  · exact h.2.1 ▸ Nat.le_add_right _ _  -- tick: post.now = pre.now + delta

-- Sessions are initially empty
theorem init_no_sessions (s : State) (hi : initState s) : s.sessions = [] := hi.1

-- A logged-in session has active status
theorem login_creates_active_session (tok uid : String) (ttl : Nat) (pre post : State)
    (h : login tok uid ttl pre post) :
    ∃ si, post.lookup tok = some si ∧ si.status = SessionStatus.active := by
  obtain ⟨_, _, hsess, hnow, _⟩ := h
  refine ⟨⟨uid, SessionStatus.active, pre.now + ttl⟩, ?_, rfl⟩
  simp [State.lookup, hsess, List.find?, beq_self_eq_true]

-- After logout, the invariant holds (revoked sessions can't authenticate)
-- This follows from inv_of_maxTTL + the fact maxTTL doesn't change
theorem logout_preserves_safety (tok : String) (pre post : State)
    (hpre : inv pre) (h : logout tok pre post) :
    safe post := by
  have hmax := hpre.2.2.2
  exact (inv_of_maxTTL post (h.2.2 ▸ hmax)).1

end TSLean.Veil.AuthDO
