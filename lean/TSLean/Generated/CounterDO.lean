-- TSLean.Generated.CounterDO
-- TypeScript → Lean 4 transpiled Durable Object: persistent counter
-- Original TypeScript: class CounterDO extends DurableObject { ... }

import TSLean.DurableObjects.Model
import TSLean.Runtime.Monad

namespace TSLean.Generated.CounterDO
open TSLean TSLean.DO

-- TypeScript: type CounterState = { count: number }
structure CounterState where count : Nat deriving Repr

-- TypeScript: const initial = new CounterState()
def CounterState.initial : CounterState := { count := 0 }

-- TypeScript: async increment(): Promise<number>
def increment : DOMonad CounterState Nat := do
  let st ← get
  let st' := { st with count := st.count + 1 }
  set st'
  return st'.count

-- TypeScript: async decrement(): Promise<number>
def decrement : DOMonad CounterState Nat := do
  let st ← get
  let st' := { st with count := if st.count > 0 then st.count - 1 else 0 }
  set st'
  return st'.count

-- TypeScript: async getCount(): Promise<number>
def getCount : DOMonad CounterState Nat := do
  let st ← get
  return st.count

-- TypeScript: async reset(): Promise<void>
def reset : DOMonad CounterState Unit := do
  set CounterState.initial

-- TypeScript: async addN(n: number): Promise<number>
def addN (n : Nat) : DOMonad CounterState Nat := do
  let st ← get
  let st' := { st with count := st.count + n }
  set st'
  return st'.count

-- Structural properties of CounterState

theorem initial_count_zero : CounterState.initial.count = 0 := rfl

theorem counterState_eq (s t : CounterState) : s = t ↔ s.count = t.count := by
  constructor
  · intro h; cases h; rfl
  · intro h; cases s; cases t; simp_all

theorem counter_increment_eq (s : CounterState) :
    { s with count := s.count + 1 }.count = s.count + 1 := rfl

theorem counter_decrement_pos (s : CounterState) (h : s.count > 0) :
    { s with count := s.count - 1 }.count = s.count - 1 := rfl

theorem counter_decrement_zero (s : CounterState) (h : s.count = 0) :
    { s with count := if s.count > 0 then s.count - 1 else 0 }.count = 0 := by
  simp [h]

theorem counter_addN_eq (s : CounterState) (n : Nat) :
    { s with count := s.count + n }.count = s.count + n := rfl

theorem counter_addN_zero (s : CounterState) :
    { s with count := s.count + 0 }.count = s.count := by simp

theorem counter_addN_comm (s : CounterState) (m n : Nat) :
    (s.count + m) + n = (s.count + n) + m := by omega

theorem counter_reset_gives_initial : CounterState.initial = { count := 0 } := rfl

-- Sequence of operations: count after multiple increments
theorem count_after_n_increments (s : CounterState) (n : Nat) :
    { s with count := s.count + n }.count = s.count + n := rfl

-- Monotonicity: addN increases count
theorem addN_monotone (s : CounterState) (n : Nat) :
    s.count ≤ { s with count := s.count + n }.count := Nat.le_add_right _ _

-- Decrement doesn't exceed original
theorem decrement_le (s : CounterState) :
    (if s.count > 0 then s.count - 1 else 0) ≤ s.count := by
  split <;> omega

-- After reset then increment, count is 1
theorem reset_then_increment :
    { CounterState.initial with count := CounterState.initial.count + 1 }.count = 1 := rfl

-- After k increments from 0, count is k
theorem k_increments_from_zero (k : Nat) :
    { CounterState.initial with count := CounterState.initial.count + k }.count = k := by
  simp [CounterState.initial]

end TSLean.Generated.CounterDO
