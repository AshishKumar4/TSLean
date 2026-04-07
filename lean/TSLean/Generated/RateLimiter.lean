-- TSLean.Generated.RateLimiter
-- TypeScript → Lean 4 transpiled code for a sliding-window rate limiter
-- Original TypeScript pattern: class RateLimiterDO extends DurableObject { ... }

import TSLean.DurableObjects.Model
import TSLean.DurableObjects.RateLimiter
import TSLean.Runtime.Monad

namespace TSLean.Generated.RateLimiter
open TSLean TSLean.DO TSLean.DO.RateLimiter

-- TypeScript: const DEFAULT_WINDOW = 60_000
def defaultWindowMs : Nat := 60000
def defaultMax : Nat := 100

-- TypeScript: function createLimiter(windowMs: number, maxCount: number): State
def createLimiter (windowMs maxCount : Nat) : RateLimiter :=
  RateLimiter.empty windowMs maxCount

-- TypeScript: function checkLimit(state: State, now: number): [boolean, State]
def checkLimit (state : RateLimiter) (now : Nat) : Bool × RateLimiter :=
  state.tryAllow now

-- TypeScript: function getCount(state: State, now: number): number
def getCount (state : RateLimiter) (now : Nat) : Nat :=
  state.countInWindow now

-- TypeScript: function isWithinLimit(state: State, now: number): boolean
def isWithinLimit (state : RateLimiter) (now : Nat) : Bool :=
  state.isAllowed now

-- Theorems about correctness

theorem createLimiter_initial_count (windowMs maxCount now : Nat) :
    getCount (createLimiter windowMs maxCount) now = 0 :=
  empty_count windowMs maxCount now

theorem createLimiter_allows_when_positive (windowMs maxCount now : Nat) (h : maxCount > 0) :
    isWithinLimit (createLimiter windowMs maxCount) now = true :=
  empty_isAllowed windowMs maxCount now h

theorem checkLimit_preserves_windowMs (state : RateLimiter) (now : Nat) :
    (checkLimit state now).2.windowMs = state.windowMs := by
  simp only [checkLimit, RateLimiter.tryAllow]; split <;> rfl

theorem checkLimit_preserves_maxCount (state : RateLimiter) (now : Nat) :
    (checkLimit state now).2.maxCount = state.maxCount := by
  simp only [checkLimit, RateLimiter.tryAllow]; split <;> rfl

theorem getCount_after_allow (state : RateLimiter) (now : Nat)
    (h : (checkLimit state now).1 = true) :
    getCount (checkLimit state now).2 now ≤ state.maxCount :=
  tryAllow_allowed_count state now h

theorem getCount_nonneg (state : RateLimiter) (now : Nat) :
    0 ≤ getCount state now := Nat.zero_le _

theorem defaultMax_positive : defaultMax > 0 := by decide
theorem defaultWindowMs_positive : defaultWindowMs > 0 := by decide

theorem create_default_allows :
    isWithinLimit (createLimiter defaultWindowMs defaultMax) 0 = true :=
  createLimiter_allows_when_positive defaultWindowMs defaultMax 0 defaultMax_positive

theorem checkLimit_state_count_le (state : RateLimiter) (now : Nat)
    (h : (checkLimit state now).1 = true) :
    getCount (checkLimit state now).2 now ≤ state.maxCount :=
  tryAllow_allowed_count state now h

theorem isWithinLimit_false_iff (state : RateLimiter) (now : Nat) :
    isWithinLimit state now = false ↔ ¬(state.countInWindow now < state.maxCount) :=
  isAllowed_false_iff state now

theorem checkLimit_reject_when_full (state : RateLimiter) (now : Nat)
    (h : isWithinLimit state now = false) :
    (checkLimit state now).1 = false := by
  simp only [checkLimit, isWithinLimit, RateLimiter.tryAllow, RateLimiter.isAllowed,
             RateLimiter.countInWindow] at *
  split
  · next hg =>
    -- hg : prune.events.length < maxCount, h : maxCount ≤ prune.events.length
    -- Contradiction: hg says length < maxCount but h says maxCount ≤ length
    exact absurd hg (Nat.not_lt.mpr (Nat.le_of_not_lt (decide_eq_false_iff_not.mp h)))
  · rfl

end TSLean.Generated.RateLimiter
