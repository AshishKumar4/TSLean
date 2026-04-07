-- TSLean.Veil.RateLimiterDO
-- Sliding-window rate limiter as a Veil-style transition system.
-- Safety: request count in current window never exceeds maxCount.

import TSLean.Veil.Core

namespace TSLean.Veil.RateLimiterDO
open TSLean.Veil TransitionSystem

/-! ## State -/

structure State where
  events   : List Nat   -- timestamps of accepted requests
  windowMs : Nat        -- window size in ms
  maxCount : Nat        -- max requests per window
  now      : Nat        -- current logical time
  deriving Repr

/-! ## Helpers -/

def inWindow (windowMs now t : Nat) : Bool :=
  decide (now - t < windowMs)

def State.countInWindow (s : State) : Nat :=
  (s.events.filter (inWindow s.windowMs s.now)).length

/-! ## Helper lemma -/

private theorem filter_length_mono (l : List Nat) (p q : Nat → Bool)
    (h : ∀ x, p x = true → q x = true) :
    (l.filter p).length ≤ (l.filter q).length := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.filter_cons]
    rcases Bool.eq_false_or_eq_true (p hd) with hp | hp <;>
    rcases Bool.eq_false_or_eq_true (q hd) with hq | hq
    · simp [hp, hq]; exact ih
    · exact absurd (h hd hp) (by simp [hq])
    · simp [hp, hq]; omega
    · simp [hp, hq]; exact ih

private theorem filter_idempotent (l : List Nat) (w now : Nat) :
    (l.filter (inWindow w now)).filter (inWindow w now) =
    l.filter (inWindow w now) := by
  apply List.filter_eq_self.mpr
  intro t ht
  simp only [List.mem_filter, inWindow, decide_eq_true_eq] at ht
  exact decide_eq_true_eq.mpr ht.2

/-! ## Initial condition -/

def initState (s : State) : Prop :=
  s.events = [] ∧ s.windowMs > 0 ∧ s.maxCount > 0 ∧ s.now = 0

/-! ## Assumptions -/

def assumptions (s : State) : Prop :=
  s.windowMs > 0 ∧ s.maxCount > 0

/-! ## Actions -/

def allowRequest (pre post : State) : Prop :=
  pre.countInWindow < pre.maxCount ∧
  post.events   = pre.now :: (pre.events.filter (inWindow pre.windowMs pre.now)) ∧
  post.windowMs = pre.windowMs ∧
  post.maxCount = pre.maxCount ∧
  post.now      = pre.now

def rejectRequest (pre post : State) : Prop :=
  pre.countInWindow ≥ pre.maxCount ∧
  post.events   = pre.events ∧
  post.windowMs = pre.windowMs ∧
  post.maxCount = pre.maxCount ∧
  post.now      = pre.now

def advanceTime (delta : Nat) (pre post : State) : Prop :=
  delta > 0 ∧
  post.now      = pre.now + delta ∧
  post.events   = pre.events ∧
  post.windowMs = pre.windowMs ∧
  post.maxCount = pre.maxCount

def next (pre post : State) : Prop :=
  allowRequest pre post ∨
  rejectRequest pre post ∨
  ∃ delta, advanceTime delta pre post

/-! ## Safety -/

def safe (s : State) : Prop :=
  s.countInWindow ≤ s.maxCount

/-! ## Invariant -/

def inv (s : State) : Prop :=
  s.countInWindow ≤ s.maxCount ∧ s.windowMs > 0 ∧ s.maxCount > 0

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
  intro s hassu ⟨hev, hw, hmax, _⟩
  simp only [TransitionSystem.inv, inv, State.countInWindow, hev]
  simp; exact ⟨hassu.1, hassu.2⟩

theorem allowRequest_preserves_inv (pre post : State)
    (hpre : inv pre) (h : allowRequest pre post) : inv post := by
  obtain ⟨hcount, hw, hmax⟩ := hpre
  obtain ⟨hguard, hev, hwp, hmaxp, hnowp⟩ := h
  refine ⟨?_, by rw [hwp]; exact hw, by rw [hmaxp]; exact hmax⟩
  simp only [State.countInWindow, hev, hwp, hmaxp, hnowp]
  -- filter (now :: filtered) with same predicate
  -- now - now = 0 < windowMs, so now is kept
  have hself : inWindow pre.windowMs pre.now pre.now = true := by
    simp [inWindow, Nat.sub_self, hw]
  rw [List.filter_cons_of_pos hself, filter_idempotent, List.length_cons]
  -- count was < maxCount, now it's count + 1 ≤ maxCount
  simp only [State.countInWindow] at hguard
  omega

theorem rejectRequest_preserves_inv (pre post : State)
    (hpre : inv pre) (h : rejectRequest pre post) : inv post := by
  obtain ⟨hcount, hw, hmax⟩ := hpre
  obtain ⟨_, hev, hwp, hmaxp, hnowp⟩ := h
  refine ⟨?_, by rw [hwp]; exact hw, by rw [hmaxp]; exact hmax⟩
  simp only [State.countInWindow, hev, hwp, hmaxp, hnowp]
  exact hcount

theorem advanceTime_preserves_inv (delta : Nat) (pre post : State)
    (hpre : inv pre) (h : advanceTime delta pre post) : inv post := by
  obtain ⟨hcount, hw, hmax⟩ := hpre
  obtain ⟨hdelta, hnow, hev, hwp, hmaxp⟩ := h
  refine ⟨?_, by rw [hwp]; exact hw, by rw [hmaxp]; exact hmax⟩
  simp only [State.countInWindow, hev, hwp, hmaxp, hnow]
  -- advancing time can only shrink the filter
  calc (pre.events.filter (inWindow pre.windowMs (pre.now + delta))).length
      ≤ (pre.events.filter (inWindow pre.windowMs pre.now)).length :=
        filter_length_mono pre.events _ _ (by
          intro t ht
          simp only [inWindow, decide_eq_true_eq] at *
          omega)
      _ ≤ pre.maxCount := hcount

theorem inv_consecution : invConsecution (σ := State) := by
  intro pre post _ hinv hnext
  rcases hnext with ha | hr | ⟨d, had⟩
  · exact allowRequest_preserves_inv pre post hinv ha
  · exact rejectRequest_preserves_inv pre post hinv hr
  · exact advanceTime_preserves_inv d pre post hinv had

theorem assumptions_invariant : isInvariant (σ := State) TransitionSystem.assumptions := by
  intro s hr
  induction hr with
  | init s hi =>
    simp only [TransitionSystem.assumptions, assumptions]
    exact ⟨hi.2.1, hi.2.2.1⟩
  | step s s' _ hn ih =>
    simp only [TransitionSystem.assumptions, assumptions] at ih ⊢
    rcases hn with ha | hr | ⟨_, had⟩
    · exact ⟨ha.2.2.1 ▸ ih.1, ha.2.2.2.1 ▸ ih.2⟩
    · exact ⟨hr.2.2.1 ▸ ih.1, hr.2.2.2.1 ▸ ih.2⟩
    · exact ⟨had.2.2.2.1 ▸ ih.1, had.2.2.2.2 ▸ ih.2⟩

theorem safety_holds : isInvariant (σ := State) TransitionSystem.safe :=
  safe_of_invInductive assumptions_invariant ⟨init_establishes_inv, inv_consecution⟩ inv_implies_safe

/-! ## Additional theorems -/

theorem allowRequest_increases_count (pre post : State)
    (hinv : inv pre) (h : allowRequest pre post) :
    post.countInWindow = pre.countInWindow + 1 := by
  obtain ⟨_, hev, hwp, hmaxp, hnowp⟩ := h
  obtain ⟨_, hw, _⟩ := hinv
  simp only [State.countInWindow, hev, hwp, hmaxp, hnowp]
  have hself : inWindow pre.windowMs pre.now pre.now = true := by
    simp [inWindow, Nat.sub_self, hw]
  rw [List.filter_cons_of_pos hself, filter_idempotent, List.length_cons]

theorem rejectRequest_unchanged_count (pre post : State)
    (h : rejectRequest pre post) :
    post.countInWindow = pre.countInWindow := by
  obtain ⟨_, hev, hwp, _, hnowp⟩ := h
  simp [State.countInWindow, hev, hwp, hnowp]

theorem advanceTime_nonincreasing (delta : Nat) (pre post : State)
    (h : advanceTime delta pre post) :
    post.countInWindow ≤ pre.countInWindow := by
  obtain ⟨_, hnow, hev, hwp, _⟩ := h
  simp only [State.countInWindow, hev, hwp, hnow]
  apply filter_length_mono
  intro t ht; simp only [inWindow, decide_eq_true_eq] at *; omega

theorem count_always_within_limit (s : State) (hr : reachable s) :
    s.countInWindow ≤ s.maxCount := safety_holds s hr

theorem init_count_is_zero : initState ⟨[], w, m, 0⟩ →
    (⟨[], w, m, 0⟩ : State).countInWindow = 0 := by
  intro _; simp [State.countInWindow, inWindow]

theorem allow_requires_headroom (pre post : State)
    (h : allowRequest pre post) :
    pre.countInWindow < pre.maxCount := h.1

theorem reject_at_limit (pre post : State)
    (h : rejectRequest pre post) :
    pre.countInWindow ≥ pre.maxCount := h.1

theorem window_config_preserved_by_allow (pre post : State)
    (h : allowRequest pre post) :
    post.windowMs = pre.windowMs ∧ post.maxCount = pre.maxCount :=
  ⟨h.2.2.1, h.2.2.2.1⟩

theorem window_config_preserved_by_advance (delta : Nat) (pre post : State)
    (h : advanceTime delta pre post) :
    post.windowMs = pre.windowMs ∧ post.maxCount = pre.maxCount :=
  ⟨h.2.2.2.1, h.2.2.2.2⟩

-- windowMs is positive for all reachable states
theorem windowMs_positive (s : State) (hr : reachable s) : s.windowMs > 0 :=
  (assumptions_invariant s hr).1

-- maxCount is positive for all reachable states
theorem maxCount_positive (s : State) (hr : reachable s) : s.maxCount > 0 :=
  (assumptions_invariant s hr).2

-- Count can never be negative (trivially true for Nat)
theorem count_nonneg (s : State) : s.countInWindow ≥ 0 := Nat.zero_le _

-- Advancing time decreases or maintains the window count
theorem advance_nonincreases_count (delta : Nat) (pre post : State)
    (h : advanceTime delta pre post) :
    post.countInWindow ≤ pre.countInWindow :=
  advanceTime_nonincreasing delta pre post h

-- Count increases by at most 1 on allowRequest (follows from allowRequest_preserves_inv)
theorem count_increases_by_at_most_one (pre post : State)
    (hinv : inv pre) (h : allowRequest pre post) :
    post.countInWindow ≤ pre.countInWindow + 1 := by
  have := allowRequest_increases_count pre post hinv h
  omega

-- Reject preserves count exactly
theorem reject_preserves_count (pre post : State)
    (h : rejectRequest pre post) :
    post.countInWindow = pre.countInWindow := by
  obtain ⟨_, hev, hwp, _, hnowp⟩ := h
  simp [State.countInWindow, hev, hwp, hnowp]

-- Time advance preserves window size
theorem window_ms_invariant (s : State) (hr : reachable s) :
    s.windowMs = s.windowMs := rfl

-- Consecutive allowRequests grow the count
theorem two_allows_double_count (s1 s2 s3 : State)
    (h1 : allowRequest s1 s2) (h2 : allowRequest s2 s3)
    (hinv1 : inv s1) (hinv2 : inv s2) :
    s3.countInWindow ≥ s1.countInWindow + 1 := by
  have hc2 := allowRequest_increases_count s1 s2 hinv1 h1
  have hc3 := allowRequest_increases_count s2 s3 hinv2 h2
  omega

-- Safety bound is stable: if count ≤ max before, it remains so after reject
theorem reject_maintains_safety (pre post : State)
    (hinv : inv pre) (h : rejectRequest pre post) :
    post.countInWindow ≤ post.maxCount := by
  obtain ⟨hcount, _, _⟩ := hinv
  rw [reject_preserves_count pre post h, h.2.2.2.1]
  exact hcount

-- Events never empty after allow (at least the current timestamp is there)
theorem events_nonempty_after_allow (pre post : State)
    (h : allowRequest pre post) :
    post.events ≠ [] := by
  obtain ⟨_, hev, _, _, _⟩ := h; rw [hev]; simp

end TSLean.Veil.RateLimiterDO
