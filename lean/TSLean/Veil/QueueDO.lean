-- TSLean.Veil.QueueDO
-- Message Queue Durable Object as a Veil-style transition system.
-- Safety: total messages never exceeds capacity.

import TSLean.Veil.Core
import TSLean.DurableObjects.Queue

namespace TSLean.Veil.QueueDO
open TSLean TSLean.Veil TransitionSystem TSLean.DO.Queue

structure State where
  queue    : DurableQueue
  capacity : Nat
  deriving Repr

def initState (s : State) : Prop :=
  s.queue = DurableQueue.empty ∧ s.capacity > 0

def assumptions (s : State) : Prop := s.capacity > 0

def enqueueMsg (payload : String) (now : Nat) (pre post : State) : Prop :=
  pre.queue.total < pre.capacity ∧
  post.queue = pre.queue.enqueue payload now ∧
  post.capacity = pre.capacity

def dequeueMsg (pre post : State) : Prop :=
  pre.queue.pending ≠ [] ∧
  post.queue = pre.queue.deliver.2 ∧
  post.capacity = pre.capacity

def ackMsg (id : Nat) (pre post : State) : Prop :=
  post.queue = pre.queue.ack id ∧ post.capacity = pre.capacity

def nackMsg (id : Nat) (pre post : State) : Prop :=
  post.queue = pre.queue.nack id ∧ post.capacity = pre.capacity

def next (pre post : State) : Prop :=
  (∃ payload now, enqueueMsg payload now pre post) ∨
  (dequeueMsg pre post) ∨
  (∃ id, ackMsg id pre post) ∨
  (∃ id, nackMsg id pre post)

def safe (s : State) : Prop := s.queue.total ≤ s.capacity

def inv (s : State) : Prop :=
  s.queue.total ≤ s.capacity ∧ s.capacity > 0

instance : TransitionSystem State where
  init        := initState
  assumptions := assumptions
  next        := next
  safe        := safe
  inv         := inv

theorem inv_implies_safe : invSafe (σ := State) :=
  fun s _ hinv => hinv.1

-- Invariant proofs use sorry for struct-equality obstacles in Lean 4.29
-- Invariant proofs: struct projections after rw make omega difficult in Lean 4.29
theorem init_establishes_inv : invInit (σ := State) := by
  intro s hassu hinit
  exact ⟨by rw [hinit.1]; simp [DurableQueue.empty, DurableQueue.total], hassu⟩

theorem enqueue_preserves_inv (payload : String) (now : Nat) (pre post : State)
    (hpre : inv pre) (h : enqueueMsg payload now pre post) : inv post := by
  obtain ⟨hguard, hq, hcappost⟩ := h
  obtain ⟨hbound, hcappos⟩ := hpre
  refine ⟨?_, by rw [hcappost]; exact hcappos⟩
  rw [hq, hcappost, enqueue_total]
  omega

theorem dequeue_preserves_inv (pre post : State)
    (hpre : inv pre) (h : dequeueMsg pre post) : inv post := by
  obtain ⟨_, hq, hcap⟩ := h
  obtain ⟨hbound, hcappos⟩ := hpre
  refine ⟨?_, by rw [hcap]; exact hcappos⟩
  rw [hq, hcap]
  have htot : (pre.queue.deliver.2).total = pre.queue.total := deliver_preserves_total pre.queue
  omega

theorem ack_preserves_inv (id : Nat) (pre post : State)
    (hpre : inv pre) (h : ackMsg id pre post) : inv post := by
  obtain ⟨hq, hcap⟩ := h
  obtain ⟨hbound, hcappos⟩ := hpre
  refine ⟨?_, by rw [hcap]; exact hcappos⟩
  rw [hq, hcap]
  have htot : (pre.queue.ack id).total ≤ pre.queue.total := by
    simp only [DurableQueue.ack, DurableQueue.total]
    have hf := List.length_filter_le (fun m => m.id ≠ id) pre.queue.inflight
    omega
  omega

theorem nack_preserves_inv (id : Nat) (pre post : State)
    (hpre : inv pre) (h : nackMsg id pre post) : inv post := by
  obtain ⟨hq, hcap⟩ := h
  obtain ⟨hbound, hcappos⟩ := hpre
  refine ⟨?_, by rw [hcap]; exact hcappos⟩
  rw [hq, hcap]
  -- nack either leaves total unchanged (find? = none) or decreases it (find? = some)
  have hle : (pre.queue.nack id).total ≤ pre.queue.total := by
    rcases hq2 : pre.queue.inflight.find? (fun m => m.id == id) with _ | msg
    · -- find? = none: nack unchanged
      simp [DurableQueue.nack, hq2]
    · -- find? = some: use nack_total_le_self
      exact nack_total_le_self pre.queue id msg hq2
  omega

theorem inv_consecution : invConsecution (σ := State) := by
  intro pre post _ hinv hnext
  rcases hnext with ⟨payload, now, h⟩ | h | ⟨id, h⟩ | ⟨id, h⟩
  · exact enqueue_preserves_inv payload now pre post hinv h
  · exact dequeue_preserves_inv pre post hinv h
  · exact ack_preserves_inv id pre post hinv h
  · exact nack_preserves_inv id pre post hinv h

theorem assumptions_invariant : isInvariant (σ := State) TransitionSystem.assumptions := by
  intro s hr
  induction hr with
  | init s hi => simp only [TransitionSystem.assumptions, assumptions]; exact hi.2
  | step s s' _ hn ih =>
    simp only [TransitionSystem.assumptions, assumptions] at ih ⊢
    rcases hn with ⟨_, _, h⟩ | h | ⟨_, h⟩ | ⟨_, h⟩ <;>
    (first | rw [h.2.2] | rw [h.2]) <;> exact ih

theorem safety_holds : isInvariant (σ := State) TransitionSystem.safe :=
  safe_of_invInductive assumptions_invariant ⟨init_establishes_inv, inv_consecution⟩ inv_implies_safe

-- Additional theorems

theorem enqueue_increases_total (payload : String) (now : Nat) (pre post : State)
    (h : enqueueMsg payload now pre post) :
    post.queue.total = pre.queue.total + 1 := by
  obtain ⟨_, hq, _⟩ := h
  rw [hq]
  unfold DurableQueue.enqueue DurableQueue.total; simp [List.length_append]; omega

theorem dequeue_total_le (pre post : State) (h : dequeueMsg pre post) :
    post.queue.total ≤ pre.queue.total := by
  obtain ⟨_, hq, _⟩ := h
  rw [hq]; have := deliver_preserves_total pre.queue; omega

theorem queue_bounded (s : State) (hr : reachable s) : s.queue.total ≤ s.capacity :=
  safety_holds s hr

theorem empty_queue_zero_total : DurableQueue.empty.total = 0 := by
  simp [DurableQueue.empty, DurableQueue.total]

-- The capacity is positive for all reachable states
theorem capacity_positive (s : State) (hr : reachable s) : s.capacity > 0 :=
  assumptions_invariant s hr

theorem enqueue_pending_grows (payload : String) (now : Nat) (pre post : State)
    (h : enqueueMsg payload now pre post) :
    post.queue.pending.length = pre.queue.pending.length + 1 := by
  obtain ⟨_, hq, _⟩ := h
  rw [hq]
  simp [DurableQueue.enqueue, List.length_append]

theorem dequeue_requires_pending (pre post : State) (h : dequeueMsg pre post) :
    pre.queue.pending ≠ [] := h.1

theorem ack_only_affects_inflight (id : Nat) (pre post : State) (h : ackMsg id pre post) :
    post.queue.pending = pre.queue.pending ∧
    post.queue.deadLetter = pre.queue.deadLetter := by
  obtain ⟨hq, _⟩ := h
  exact ⟨by simp [hq, DurableQueue.ack], by simp [hq, DurableQueue.ack]⟩

theorem enqueue_capacity_unchanged (payload : String) (now : Nat) (pre post : State)
    (h : enqueueMsg payload now pre post) :
    post.capacity = pre.capacity := h.2.2

theorem dequeue_capacity_unchanged (pre post : State) (h : dequeueMsg pre post) :
    post.capacity = pre.capacity := h.2.2

theorem nack_capacity_unchanged (id : Nat) (pre post : State) (h : nackMsg id pre post) :
    post.capacity = pre.capacity := h.2

theorem ack_capacity_unchanged (id : Nat) (pre post : State) (h : ackMsg id pre post) :
    post.capacity = pre.capacity := h.2

-- The queue bounded safety is preserved for all reachable states
theorem all_reachable_bounded :
    ∀ s : State, reachable s → s.queue.total ≤ s.capacity :=
  fun s hr => safety_holds s hr

-- Total is monotone: enqueue is the only operation that increases it
theorem total_monotone_dequeue (pre post : State) (h : dequeueMsg pre post) :
    post.queue.total ≤ pre.queue.total := by
  obtain ⟨_, hq, _⟩ := h
  rw [hq]
  exact Nat.le_of_eq (deliver_preserves_total pre.queue)

theorem total_monotone_ack (id : Nat) (pre post : State) (h : ackMsg id pre post) :
    post.queue.total ≤ pre.queue.total := by
  obtain ⟨hq, _⟩ := h
  simp only [hq, DurableQueue.ack, DurableQueue.total]
  have := List.length_filter_le (fun m => m.id ≠ id) pre.queue.inflight
  omega

theorem total_monotone_nack (id : Nat) (pre post : State) (h : nackMsg id pre post) :
    post.queue.total ≤ pre.queue.total + 1 := by
  obtain ⟨hq, _⟩ := h; rw [hq]; exact nack_total_le pre.queue id

-- Enqueue guard: can only enqueue when below capacity
theorem enqueue_below_capacity (payload : String) (now : Nat) (pre post : State)
    (h : enqueueMsg payload now pre post) :
    pre.queue.total < pre.capacity := by
  obtain ⟨hguard, _, _⟩ := h; exact hguard

-- After enqueue, total is exactly capacity if it was capacity - 1 before
theorem enqueue_fills_queue (payload : String) (now : Nat) (pre post : State)
    (h : enqueueMsg payload now pre post) (hpre : inv pre)
    (hfull : pre.queue.total + 1 = pre.capacity) :
    post.queue.total = post.capacity := by
  obtain ⟨_, hbound⟩ := hpre
  obtain ⟨_, hq, hcap⟩ := h
  rw [hq, hcap, enqueue_total]
  omega

end TSLean.Veil.QueueDO
