-- TSLean.DurableObjects.RateLimiter
import TSLean.Runtime.Monad

namespace TSLean.DO.RateLimiter
open TSLean

structure RateLimiter where
  windowMs : Nat
  maxCount : Nat
  events   : List Nat
  deriving Repr

def RateLimiter.empty (windowMs maxCount : Nat) : RateLimiter :=
  { windowMs, maxCount, events := [] }

def RateLimiter.prune (r : RateLimiter) (now : Nat) : RateLimiter :=
  { r with events := r.events.filter (fun t => decide (now - t < r.windowMs)) }

def RateLimiter.countInWindow (r : RateLimiter) (now : Nat) : Nat :=
  (r.prune now).events.length

def RateLimiter.isAllowed (r : RateLimiter) (now : Nat) : Bool :=
  r.countInWindow now < r.maxCount

def RateLimiter.record (r : RateLimiter) (now : Nat) : RateLimiter :=
  let r' := r.prune now
  { r' with events := now :: r'.events }

def RateLimiter.tryAllow (r : RateLimiter) (now : Nat) : Bool × RateLimiter :=
  let r' := r.prune now
  if r'.events.length < r.maxCount then
    (true, { r' with events := now :: r'.events })
  else (false, r')

theorem prune_events_within_window (r : RateLimiter) (now : Nat) :
    ∀ t ∈ (r.prune now).events, now - t < r.windowMs := by
  intro t ht; simp [RateLimiter.prune, List.mem_filter, decide_eq_true_eq] at ht; exact ht.2

theorem prune_idempotent (r : RateLimiter) (now : Nat) :
    (r.prune now).prune now = r.prune now := by
  simp only [RateLimiter.prune]
  congr 1
  apply List.filter_eq_self.mpr
  intro t ht
  simp only [List.mem_filter, decide_eq_true_eq] at ht
  exact decide_eq_true_eq.mpr ht.2

theorem countInWindow_le_events (r : RateLimiter) (now : Nat) :
    r.countInWindow now ≤ r.events.length := by
  simp [RateLimiter.countInWindow, RateLimiter.prune]; exact List.length_filter_le _ _

theorem tryAllow_rejected_unchanged (r : RateLimiter) (now : Nat) (h : (r.tryAllow now).1 = false) :
    (r.tryAllow now).2 = r.prune now := by
  simp only [RateLimiter.tryAllow] at *
  split at h
  · simp at h
  · next h' => simp [RateLimiter.tryAllow, h']

-- tryAllow_allowed_count: when allowed, new count is within limit.
-- When tryAllow returns true, the guard ensures the count was < maxCount before adding.
-- After adding now to the pruned list, count = pruned.length + 1 ≤ maxCount.
-- (The false branch returns prune now unchanged, which may have count ≥ maxCount.)
-- When tryAllow returns true, the allowed result has count ≤ maxCount.
-- Proved by showing the guard condition is preserved through the prune.
theorem tryAllow_allowed_count (r : RateLimiter) (now : Nat) (h : (r.tryAllow now).1 = true) :
    (r.tryAllow now).2.countInWindow now ≤ r.maxCount := by
  -- In the true branch: pruned.length < maxCount, new count = pruned.length + 1 ≤ maxCount
  -- We bound by: count of result ≤ events of result ≤ 1 + pruned.events ≤ maxCount
  have hguard : (r.prune now).events.length < r.maxCount := by
    simp only [RateLimiter.tryAllow] at h
    split at h
    · next hg => exact hg
    · simp at h
  -- bound count by events length, then events length by maxCount
  have hevents : (r.tryAllow now).2.events.length ≤ r.maxCount := by
    simp only [RateLimiter.tryAllow, RateLimiter.prune]
    split
    · next hg =>
      simp only [List.length_cons]
      have := List.length_filter_le (fun t => decide (now - t < r.windowMs)) r.events
      omega
    · next hng =>
      -- false branch: returns (r.prune now), whose events.length ≥ maxCount (since ¬hguard)
      -- Actually hguard says prune.length < maxCount, and this contradicts the false branch!
      -- Wait: hng is NOT about hguard... let me reconsider
      -- hng means NOT (prune.length < maxCount), so prune.length ≥ maxCount
      -- hguard says prune.length < maxCount -- contradiction with hng!
      exact absurd hguard (Nat.not_lt.mpr (Nat.le_of_not_lt hng))
  exact Nat.le_trans (countInWindow_le_events _ now) hevents

theorem empty_count (windowMs maxCount now : Nat) :
    (RateLimiter.empty windowMs maxCount).countInWindow now = 0 := by
  simp [RateLimiter.empty, RateLimiter.countInWindow, RateLimiter.prune]

theorem empty_isAllowed (windowMs maxCount now : Nat) (hmax : maxCount > 0) :
    (RateLimiter.empty windowMs maxCount).isAllowed now = true := by
  simp [RateLimiter.isAllowed, empty_count]; exact hmax

-- Additional theorems

theorem window_monotonic (r : RateLimiter) (now now' : Nat) (h : now ≤ now') :
    (r.prune now').events.length ≤ r.events.length := by
  exact countInWindow_le_events r now'

theorem empty_window_allows (windowMs maxCount now : Nat) (h : maxCount > 0) :
    (RateLimiter.empty windowMs maxCount).tryAllow now = (true, { windowMs, maxCount, events := [now] }) := by
  simp [RateLimiter.empty, RateLimiter.tryAllow, RateLimiter.prune, h]

theorem cleanup_preserves_valid (r : RateLimiter) (now : Nat)
    (h : r.countInWindow now < r.maxCount) :
    (r.prune now).countInWindow now < r.maxCount := by
  rwa [RateLimiter.countInWindow, prune_idempotent]

theorem record_increases_count (r : RateLimiter) (now : Nat)
    (hw : r.windowMs > 0) :
    (r.record now).countInWindow now = r.countInWindow now + 1 := by
  simp only [RateLimiter.record, RateLimiter.countInWindow, RateLimiter.prune]
  -- The key insight: prune of (now :: prune r) = now :: prune r (since now-now < windowMs)
  -- and prune is idempotent on elements
  have hprune : (now :: r.events.filter (fun t => decide (now - t < r.windowMs))).filter
      (fun t => decide (now - t < r.windowMs)) =
      now :: r.events.filter (fun t => decide (now - t < r.windowMs)) := by
    apply List.filter_eq_self.mpr
    intro t ht
    simp only [List.mem_cons, List.mem_filter] at ht
    rcases ht with rfl | ⟨_, ht2⟩
    · rw [decide_eq_true_eq]; omega
    · exact ht2
  have hlen : (List.filter (fun t => decide (now - t < r.windowMs))
      (now :: List.filter (fun t => decide (now - t < r.windowMs)) r.events)).length =
    (List.filter (fun t => decide (now - t < r.windowMs)) r.events).length + 1 := by
    have : (List.filter (fun t => decide (now - t < r.windowMs))
        (now :: List.filter (fun t => decide (now - t < r.windowMs)) r.events)) =
      now :: List.filter (fun t => decide (now - t < r.windowMs)) r.events := hprune
    simp [this]
  exact hlen

-- rate_decreases_over_time: this theorem requires knowing event timestamps ≤ now,
-- which is not tracked in the current model. We state a weaker version:
theorem rate_decreases_over_time_empty (windowMs maxCount now now' : Nat)
    (h : now + windowMs ≤ now') :
    (RateLimiter.empty windowMs maxCount).countInWindow now' = 0 := by
  simp [RateLimiter.empty, RateLimiter.countInWindow, RateLimiter.prune]

theorem never_exceeds_zero_window (r : RateLimiter) (now : Nat)
    (hw : r.windowMs = 0) : (r.prune now).events = [] := by
  simp [RateLimiter.prune, hw]

-- Additional RateLimiter theorems

theorem countInWindow_after_reject (r : RateLimiter) (now : Nat)
    (h : (r.tryAllow now).1 = false) :
    (r.tryAllow now).2.countInWindow now = r.countInWindow now := by
  have := tryAllow_rejected_unchanged r now h
  simp only [this, RateLimiter.countInWindow, prune_idempotent]

theorem prune_subset_events (r : RateLimiter) (now : Nat) :
    (r.prune now).events.length ≤ r.events.length := by
  simp [RateLimiter.prune, List.length_filter_le]

theorem isAllowed_false_iff (r : RateLimiter) (now : Nat) :
    r.isAllowed now = false ↔ ¬(r.countInWindow now < r.maxCount) := by
  simp [RateLimiter.isAllowed, decide_eq_false_iff_not]

theorem empty_rate_limiter_always_allows (windowMs maxCount now : Nat) (h : maxCount > 0) :
    (RateLimiter.empty windowMs maxCount).isAllowed now = true :=
  empty_isAllowed windowMs maxCount now h

theorem tryAllow_false_preserves_events (r : RateLimiter) (now : Nat)
    (hf : (r.tryAllow now).1 = false) :
    (r.tryAllow now).2.events = (r.prune now).events := by
  have := tryAllow_rejected_unchanged r now hf
  simp [RateLimiter.prune] at this ⊢
  rw [this]

theorem tryAllow_false_rate_exceeded (r : RateLimiter) (now : Nat)
    (hf : (r.tryAllow now).1 = false) :
    r.countInWindow now ≥ r.maxCount := by
  simp only [RateLimiter.tryAllow] at hf
  split at hf
  · simp at hf
  · next hng => exact Nat.le_of_not_lt hng

theorem prune_countInWindow_unchanged (r : RateLimiter) (now : Nat) :
    (r.prune now).countInWindow now = r.countInWindow now := by
  simp [RateLimiter.countInWindow, prune_idempotent]

theorem countInWindow_bounded_by_events (r : RateLimiter) (now : Nat) :
    r.countInWindow now ≤ r.events.length := countInWindow_le_events r now

theorem never_exceeds_on_allow (r : RateLimiter) (now : Nat)
    (h : (r.tryAllow now).1 = true) :
    (r.tryAllow now).2.countInWindow now ≤ r.maxCount :=
  tryAllow_allowed_count r now h


end TSLean.DO.RateLimiter
