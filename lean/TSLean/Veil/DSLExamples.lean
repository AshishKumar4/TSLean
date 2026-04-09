-- TSLean.Veil.DSLExamples
-- Demonstrates the mini Veil DSL on three transition systems.
-- Each example: define state, actions, safety; build TransitionSystem; prove safety.

import TSLean.Veil.DSL

open TSLean.Veil TransitionSystem TSLean.Veil.DSL

/-! ## Example 1: Nat Counter (simplest case) -/

namespace NatCounter

-- State: a natural number counter with a maximum
structure State where
  count : Nat
  max   : Nat
  deriving Repr, BEq, Inhabited

-- Actions using the DSL macros
veil_action increment (s : State) where
  { s with count := s.count + 1 }

veil_action reset (s : State) where
  { s with count := 0 }

-- A relational action with a guard
veil_relation guarded_inc (pre post : State) where
  pre.count < pre.max ∧ post = { pre with count := pre.count + 1 }

-- Safety property
veil_safety bounded (s : State) where
  s.count ≤ s.max

-- Invariant (stronger: includes max > 0)
def inv (s : State) : Prop := s.count ≤ s.max ∧ s.max > 0

def initState (s : State) : Prop := s.count = 0 ∧ s.max > 0

-- TransitionSystem instance using DSL's next2 combinator
instance : TransitionSystem State where
  init        := initState
  assumptions := fun _ => True
  next        := next2 guarded_inc reset
  safe        := bounded
  inv         := inv

-- Proof: init establishes invariant
theorem init_inv : invInit (σ := State) := by
  intro s _ ⟨hc, hm⟩
  exact ⟨by omega, hm⟩

-- Proof: guarded_inc preserves invariant
theorem guarded_inc_preserves (pre post : State)
    (_ : True) (hi : inv pre) (h : guarded_inc pre post) : inv post := by
  obtain ⟨hbound, hpos⟩ := hi
  obtain ⟨hguard, heq⟩ := h
  subst heq; simp only [inv]; omega

-- Proof: reset preserves invariant
theorem reset_preserves (pre post : State)
    (_ : True) (hi : inv pre) (h : reset pre post) : inv post := by
  obtain ⟨_, hpos⟩ := hi
  simp only [reset] at h; subst h
  simp only [inv]; omega

-- Proof: consecution via next2_preserves
theorem consecution : invConsecution (σ := State) := by
  intro s s' ha hi hn
  exact next2_preserves guarded_inc_preserves reset_preserves ha hi hn

-- Proof: inv implies safety
theorem inv_safe : invSafe (σ := State) := by
  intro s _ ⟨hb, _⟩; exact hb

-- Proof: assumptions hold trivially
theorem assu_inv : isInvariant (σ := State) TransitionSystem.assumptions :=
  fun _ _ => trivial

-- The main safety theorem
theorem safety_holds : isInvariant (σ := State) TransitionSystem.safe :=
  safe_of_invInductive assu_inv ⟨init_inv, consecution⟩ inv_safe

-- Alternative: use the safety_of_inv_inductive combinator from DSL
theorem safety_holds' : ∀ s, reachable s → bounded s :=
  safety_of_inv_inductive State (fun _ _ => trivial)
    (fun s _ ⟨hc, hm⟩ => ⟨by omega, hm⟩)
    (fun s s' _ hi hn => next2_preserves guarded_inc_preserves reset_preserves (by trivial) hi hn)
    (fun s _ hi => hi.1)

end NatCounter

/-! ## Example 2: Token Ring (two nodes) -/

namespace TokenRing

structure State where
  hasToken : Bool  -- node 0 has the token
  inCS     : Bool  -- node 0 is in critical section
  deriving Repr, BEq, Inhabited

-- Actions
veil_action acquire (s : State) where
  { s with inCS := true }

veil_action release (s : State) where
  { s with inCS := false, hasToken := false }

-- Relational: acquire requires the token
veil_relation safe_acquire (pre post : State) where
  pre.hasToken = true ∧ pre.inCS = false ∧ post = { pre with inCS := true }

veil_relation safe_release (pre post : State) where
  pre.inCS = true ∧ post = { pre with inCS := false, hasToken := false }

veil_relation receive_token (pre post : State) where
  pre.hasToken = false ∧ post = { pre with hasToken := true }

-- Safety: if in CS then has token
veil_safety mutex (s : State) where
  s.inCS = true → s.hasToken = true

def inv (s : State) : Prop := s.inCS = true → s.hasToken = true
def initState (s : State) : Prop := s.hasToken = true ∧ s.inCS = false

instance : TransitionSystem State where
  init := initState
  assumptions := fun _ => True
  next := next3 safe_acquire safe_release receive_token
  safe := mutex
  inv  := inv

theorem init_inv : invInit (σ := State) := by
  intro s _ ⟨_, hincs⟩; intro h; simp [hincs] at h

theorem acquire_ok (pre post : State) (_ : True) (hi : inv pre)
    (h : safe_acquire pre post) : inv post := by
  obtain ⟨htok, _, heq⟩ := h; subst heq; intro; exact htok

theorem release_ok (pre post : State) (_ : True) (_ : inv pre)
    (h : safe_release pre post) : inv post := by
  obtain ⟨_, heq⟩ := h; subst heq; intro habs; simp at habs

theorem receive_ok (pre post : State) (_ : True) (hi : inv pre)
    (h : receive_token pre post) : inv post := by
  obtain ⟨_, heq⟩ := h; subst heq; intro; exact rfl

theorem consecution : invConsecution (σ := State) := by
  intro s s' ha hi hn
  exact next3_preserves acquire_ok release_ok receive_ok ha hi hn

theorem safety_holds : isInvariant (σ := State) TransitionSystem.safe :=
  safe_of_invInductive (fun _ _ => trivial) ⟨init_inv, consecution⟩ (fun s _ hi => hi)

end TokenRing

/-! ## Example 3: Bounded Queue (capacity invariant) -/

namespace BoundedQueue

structure State where
  size     : Nat
  capacity : Nat
  deriving Repr, BEq, Inhabited

veil_relation enqueue (pre post : State) where
  pre.size < pre.capacity ∧
  post.size = pre.size + 1 ∧
  post.capacity = pre.capacity

veil_relation dequeue (pre post : State) where
  pre.size > 0 ∧
  post.size = pre.size - 1 ∧
  post.capacity = pre.capacity

veil_safety not_over_capacity (s : State) where
  s.size ≤ s.capacity

def inv (s : State) : Prop := s.size ≤ s.capacity ∧ s.capacity > 0
def initState (s : State) : Prop := s.size = 0 ∧ s.capacity > 0

instance : TransitionSystem State where
  init := initState
  assumptions := fun s => s.capacity > 0
  next := next2 enqueue dequeue
  safe := not_over_capacity
  inv  := inv

theorem init_inv : invInit (σ := State) := by
  intro s hassu ⟨hsz, hcap⟩; exact ⟨by omega, hcap⟩

theorem enqueue_ok (pre post : State) (hassu : pre.capacity > 0)
    (hi : inv pre) (h : enqueue pre post) : inv post := by
  obtain ⟨hbound, hcap⟩ := hi
  obtain ⟨hguard, hsz, hcapeq⟩ := h
  exact ⟨by omega, by omega⟩

theorem dequeue_ok (pre post : State) (_ : pre.capacity > 0)
    (hi : inv pre) (h : dequeue pre post) : inv post := by
  obtain ⟨hbound, hcap⟩ := hi
  obtain ⟨_, hsz, hcapeq⟩ := h
  exact ⟨by omega, by omega⟩

theorem assu_inv : isInvariant (σ := State) TransitionSystem.assumptions := by
  intro s hr; induction hr with
  | init s hi => exact hi.2
  | step s s' _ hn ih =>
    simp only [TransitionSystem.assumptions]
    rcases hn with ⟨_, _, hcap⟩ | ⟨_, _, hcap⟩ <;> rw [hcap] <;> exact ih

theorem safety_holds : isInvariant (σ := State) TransitionSystem.safe :=
  safe_of_invInductive assu_inv
    ⟨init_inv, fun s s' ha hi hn =>
      next2_preserves enqueue_ok dequeue_ok ha hi hn⟩
    (fun s _ hi => hi.1)

-- Bonus: use the DSL combinator directly
theorem safety_direct : ∀ s, reachable s → not_over_capacity s :=
  safety_of_inv_inductive State
    (fun s hr => assu_inv s hr)
    (fun s hassu ⟨hsz, hcap⟩ => ⟨by omega, hcap⟩)
    (fun s s' ha hi hn => next2_preserves enqueue_ok dequeue_ok ha hi hn)
    (fun s _ hi => hi.1)

end BoundedQueue
