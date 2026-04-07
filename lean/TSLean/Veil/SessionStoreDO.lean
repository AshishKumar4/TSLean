-- TSLean.Veil.SessionStoreDO
-- Session Store Durable Object as a Veil-style transition system.
-- Safety: only fresh sessions can authenticate; expired ones are rejected.

import TSLean.Veil.Core
import TSLean.DurableObjects.SessionStore
import TSLean.Runtime.BrandedTypes

namespace TSLean.Veil.SessionStoreDO
open TSLean TSLean.Veil TransitionSystem TSLean.DO.SessionStore TSLean.Stdlib.HashMap

/-! ## State -/

structure State where
  store   : SessionStore
  clock   : Nat  -- current logical time
  maxSessions : Nat  -- capacity limit
  deriving Repr

/-! ## Initial condition -/

def initState (s : State) : Prop :=
  s.store = SessionStore.empty ∧ s.clock = 0 ∧ s.maxSessions > 0

/-! ## Assumptions -/

def assumptions (s : State) : Prop := s.maxSessions > 0

/-! ## Actions -/

def createSession (sess : Session) (pre post : State) : Prop :=
  sess.expiresAt > pre.clock ∧
  post.store = pre.store.put sess ∧
  post.clock = pre.clock ∧
  post.maxSessions = pre.maxSessions

def revokeSession (tok : SessionToken) (pre post : State) : Prop :=
  post.store = pre.store.delete tok ∧
  post.clock = pre.clock ∧
  post.maxSessions = pre.maxSessions

def advanceClock (delta : Nat) (pre post : State) : Prop :=
  delta > 0 ∧
  post.clock = pre.clock + delta ∧
  post.store = pre.store ∧
  post.maxSessions = pre.maxSessions

/-! ## Transition -/

def next (pre post : State) : Prop :=
  (∃ sess, createSession sess pre post) ∨
  (∃ tok, revokeSession tok pre post) ∨
  (∃ delta, advanceClock delta pre post)

/-! ## Safety: revoked/deleted sessions don't authenticate -/

def safe (s : State) : Prop :=
  ∀ tok, s.store.getFresh tok s.clock = none ∨
    ∃ sess, s.store.getFresh tok s.clock = some sess ∧ sess.isFresh s.clock = true

/-! ## Invariant -/

def inv (s : State) : Prop :=
  -- All sessions returned by getFresh are actually fresh
  (∀ tok sess, s.store.getFresh tok s.clock = some sess → sess.isFresh s.clock = true) ∧
  s.maxSessions > 0

/-! ## Instance -/

instance : TransitionSystem State where
  init        := initState
  assumptions := assumptions
  next        := next
  safe        := safe
  inv         := inv

/-! ## Verification -/

theorem inv_implies_safe : invSafe (σ := State) := by
  intro s _ ⟨hfresh, _⟩
  intro tok
  rcases h : s.store.getFresh tok s.clock with _ | sess
  · exact Or.inl rfl
  · exact Or.inr ⟨sess, rfl, hfresh tok sess h⟩

-- Helper: empty store returns none for getFresh
private theorem empty_getFresh_none (tok : SessionToken) (now : Nat) :
    SessionStore.empty.getFresh tok now = none := by
  simp [SessionStore.getFresh, SessionStore.get, SessionStore.empty, AssocMap.get?_empty]

theorem init_establishes_inv : invInit (σ := State) := by
  intro s hassu hinit
  refine ⟨?_, hassu⟩
  intro tok sess hfresh
  rw [hinit.1] at hfresh
  simp [empty_getFresh_none] at hfresh

theorem createSession_preserves_inv (sess : Session) (pre post : State)
    (hpre : inv pre) (h : createSession sess pre post) : inv post := by
  obtain ⟨hfreshsess, hstore, hclock, hmaxpost⟩ := h
  refine ⟨?_, by rw [hmaxpost]; exact hpre.2⟩
  rw [hclock, hstore]
  intro tok s hfresh
  simp only [SessionStore.getFresh, SessionStore.get, SessionStore.put] at hfresh
  by_cases heq : tok = sess.token
  · -- inserted session
    have hget : (AssocMap.insert pre.store sess.token sess).get? tok = some sess := by
      rw [heq]; exact AssocMap.get?_insert_same pre.store sess.token sess
    rw [hget] at hfresh
    have hif : sess.isFresh pre.clock = true := by simp [Session.isFresh, hfreshsess]
    simp only [hif, ↓reduceIte, Option.some.injEq] at hfresh
    exact hfresh ▸ hif
  · -- different session: insert of sess.token doesn't affect tok
    have hdiff : (AssocMap.insert pre.store sess.token sess).get? tok = pre.store.get? tok :=
      AssocMap.get?_insert_diff pre.store sess.token tok sess (Ne.symm heq)
    rw [hdiff] at hfresh
    exact hpre.1 tok s (by simp [SessionStore.getFresh, SessionStore.get, hfresh])

theorem revokeSession_preserves_inv (tok : SessionToken) (pre post : State)
    (hpre : inv pre) (h : revokeSession tok pre post) : inv post := by
  obtain ⟨hstore, hclock, hmaxpost⟩ := h
  refine ⟨?_, by rw [hmaxpost]; exact hpre.2⟩
  rw [hclock, hstore]
  intro tok' s hfresh
  by_cases heq : tok' = tok
  · subst heq
    -- erase tok' removes the entry, getFresh returns none — contradiction
    simp only [SessionStore.getFresh, SessionStore.get, SessionStore.delete,
               AssocMap.get?_erase] at hfresh
    exact absurd hfresh (by simp)
  · -- tok' ≠ tok: delete of tok doesn't affect tok'
    have hne : tok ≠ tok' := fun h => heq h.symm
    have hpreq : pre.store.getFresh tok' pre.clock = some s := by
      simp only [SessionStore.getFresh, SessionStore.get, SessionStore.delete] at hfresh ⊢
      have hkeep := delete_preserves_other pre.store tok tok' hne
      simp [SessionStore.get] at hkeep
      rwa [← hkeep]
    exact hpre.1 tok' s hpreq

theorem advanceClock_preserves_inv (delta : Nat) (pre post : State)
    (hpre : inv pre) (h : advanceClock delta pre post) : inv post := by
  obtain ⟨hpos, hclock, hstore, hmaxpost⟩ := h
  refine ⟨?_, by rw [hmaxpost]; exact hpre.2⟩
  rw [hclock, hstore]
  intro tok sess hfresh
  exact no_stale_reads pre.store tok (pre.clock + delta) sess hfresh

theorem inv_consecution : invConsecution (σ := State) := by
  intro pre post _ hinv hnext
  rcases hnext with ⟨sess, h⟩ | ⟨tok, h⟩ | ⟨delta, h⟩
  · exact createSession_preserves_inv sess pre post hinv h
  · exact revokeSession_preserves_inv tok pre post hinv h
  · exact advanceClock_preserves_inv delta pre post hinv h

theorem assumptions_invariant : isInvariant (σ := State) TransitionSystem.assumptions := by
  intro s hr
  induction hr with
  | init s hi => simp [TransitionSystem.assumptions, assumptions, hi.2.2]
  | step s s' _ hn ih =>
    simp only [TransitionSystem.assumptions, assumptions] at ih ⊢
    rcases hn with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> (try rw [h.2.2.2]) <;> (try rw [h.2.2]) <;> exact ih

theorem safety_holds : isInvariant (σ := State) TransitionSystem.safe :=
  safe_of_invInductive assumptions_invariant ⟨init_establishes_inv, inv_consecution⟩ inv_implies_safe

/-! ## Additional theorems -/

theorem getFresh_after_create (pre post : State) (sess : Session)
    (h : createSession sess pre post) :
    post.store.getFresh sess.token post.clock = some sess := by
  obtain ⟨hfresh, hstore, hclock, _⟩ := h
  rw [hstore, hclock]
  simp only [SessionStore.getFresh, SessionStore.get, SessionStore.put,
             TSLean.Stdlib.HashMap.AssocMap.get?_insert_same]
  exact if_pos (by exact decide_eq_true_eq.mpr hfresh)

theorem getFresh_none_after_revoke (pre post : State) (tok : SessionToken)
    (h : revokeSession tok pre post) :
    post.store.getFresh tok post.clock = none := by
  obtain ⟨hstore, hclock, _⟩ := h
  rw [hstore, hclock]
  simp [SessionStore.getFresh, delete_then_get]

theorem create_fresh_session_valid (state : State) (hr : reachable state)
    (tok : SessionToken) (sess : Session)
    (h : state.store.getFresh tok state.clock = some sess) :
    sess.isFresh state.clock = true := by
  have := safety_holds state hr
  rcases this tok with hn | ⟨s, hs, hf⟩
  · rw [hn] at h; simp at h
  · rw [h] at hs; exact Option.some_inj.mp hs ▸ hf

theorem clock_advance_delta (pre post : State) (h : advanceClock delta pre post) :
    post.clock = pre.clock + delta := h.2.1

theorem clock_strictly_increases (pre post : State) (delta : Nat)
    (h : advanceClock delta pre post) :
    post.clock > pre.clock := by
  have hpos := h.1
  have heq := h.2.1
  omega

-- The session store is empty initially
theorem initial_store_empty (s : State) (hi : initState s) :
    s.store = SessionStore.empty := hi.1

-- The clock starts at zero
theorem initial_clock_zero (s : State) (hi : initState s) :
    s.clock = 0 := hi.2.1

-- maxSessions is positive for all reachable states
theorem maxSessions_positive (s : State) (hr : reachable s) : s.maxSessions > 0 :=
  assumptions_invariant s hr

-- createSession preserves clock
theorem createSession_same_clock (sess : Session) (pre post : State)
    (h : createSession sess pre post) : post.clock = pre.clock := h.2.2.1

-- revokeSession preserves clock
theorem revokeSession_same_clock (tok : SessionToken) (pre post : State)
    (h : revokeSession tok pre post) : post.clock = pre.clock := h.2.1

-- revokeSession preserves maxSessions
theorem revokeSession_same_maxSessions (tok : SessionToken) (pre post : State)
    (h : revokeSession tok pre post) : post.maxSessions = pre.maxSessions := h.2.2

-- createSession guard: session must be fresh at creation time
theorem createSession_fresh_guard (sess : Session) (pre post : State)
    (h : createSession sess pre post) : sess.expiresAt > pre.clock := h.1

-- advanceClock preserves the store
theorem advanceClock_same_store (delta : Nat) (pre post : State)
    (h : advanceClock delta pre post) : post.store = pre.store := h.2.2.1

-- advanceClock preserves maxSessions
theorem advanceClock_same_maxSessions (delta : Nat) (pre post : State)
    (h : advanceClock delta pre post) : post.maxSessions = pre.maxSessions := h.2.2.2

-- Fresh session at any reachable state is always valid
theorem reachable_fresh_implies_valid (state : State) (hr : reachable state)
    (tok : SessionToken) (sess : Session)
    (h : state.store.getFresh tok state.clock = some sess) :
    sess.expiresAt > state.clock := by
  have hfresh := create_fresh_session_valid state hr tok sess h
  simp [Session.isFresh] at hfresh; exact hfresh

-- Revoking then looking up gives none
theorem revoke_makes_inaccessible (pre post : State) (tok : SessionToken)
    (h : revokeSession tok pre post) :
    post.store.getFresh tok post.clock = none :=
  getFresh_none_after_revoke pre post tok h

-- The clock is monotonically non-decreasing across transitions
theorem clock_nondecreasing (pre post : State) (h : next pre post) :
    post.clock ≥ pre.clock := by
  rcases h with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩
  · exact h.2.2.1 ▸ Nat.le_refl _  -- createSession: post.clock = pre.clock
  · exact h.2.1 ▸ Nat.le_refl _     -- revokeSession: post.clock = pre.clock
  · exact h.2.1 ▸ Nat.le_add_right _ _  -- advanceClock: post.clock = pre.clock + delta

-- All valid sessions retrieved from reachable state are not yet expired
theorem no_expired_sessions_returned (state : State) (hr : reachable state)
    (tok : SessionToken) (sess : Session)
    (h : state.store.getFresh tok state.clock = some sess) :
    ¬(state.clock ≥ sess.expiresAt) := by
  have hpos := reachable_fresh_implies_valid state hr tok sess h
  omega

-- Clock starts at zero and advances monotonically
theorem clock_starts_at_zero (s : State) (hi : initState s) : s.clock = 0 :=
  initial_clock_zero s hi

-- Store starts empty
theorem store_starts_empty (s : State) (hi : initState s) :
    s.store = SessionStore.empty :=
  initial_store_empty s hi

-- getFresh returns none for empty store
theorem empty_store_no_sessions (tok : SessionToken) (now : Nat) :
    SessionStore.empty.getFresh tok now = none := by
  simp [SessionStore.getFresh, SessionStore.get, SessionStore.empty,
        TSLean.Stdlib.HashMap.AssocMap.get?_empty]

-- Revoke then get fresh returns none
theorem revoke_prevents_fresh (pre post : State) (tok : SessionToken)
    (h : revokeSession tok pre post) :
    post.store.getFresh tok post.clock = none :=
  getFresh_none_after_revoke pre post tok h

end TSLean.Veil.SessionStoreDO
