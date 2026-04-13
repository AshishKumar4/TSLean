-- TSLean.Generated.QueueProcessor
-- TypeScript → Lean 4 transpiled Durable Object for message queue processing
-- Original TypeScript pattern: class QueueProcessorDO extends DurableObject { ... }

import TSLean.DurableObjects.Model
import TSLean.DurableObjects.Queue
import TSLean.Runtime.Monad

namespace TSLean.Generated.QueueProcessor
open TSLean TSLean.DO TSLean.DO.Queue

-- TypeScript: type ProcessorState = { pending: Message[], inflight: Message[], dead: Message[] }
abbrev ProcessorState := DurableQueue

-- TypeScript: const MAX_ATTEMPTS = 3
def maxAttempts : Nat := 3

-- TypeScript: function createProcessor(): ProcessorState
def createProcessor : ProcessorState := DurableQueue.empty

-- TypeScript: function enqueue(state: ProcessorState, payload: string, now: number): ProcessorState
def enqueue (state : ProcessorState) (payload : String) (now : Nat) : ProcessorState :=
  state.enqueue payload now maxAttempts

-- TypeScript: function dequeue(state: ProcessorState): [Message | null, ProcessorState]
def dequeue (state : ProcessorState) : Option QueueMessage × ProcessorState :=
  state.deliver

-- TypeScript: function ack(state: ProcessorState, id: number): ProcessorState
def ack (state : ProcessorState) (id : Nat) : ProcessorState := state.ack id

-- TypeScript: function nack(state: ProcessorState, id: number): ProcessorState
def nack (state : ProcessorState) (id : Nat) : ProcessorState := state.nack id

-- TypeScript: function pendingCount(state: ProcessorState): number
def pendingCount (state : ProcessorState) : Nat := state.pending.length

-- TypeScript: function inflightCount(state: ProcessorState): number
def inflightCount (state : ProcessorState) : Nat := state.inflight.length

-- Theorems about the generated queue processor

theorem createProcessor_empty :
    pendingCount createProcessor = 0 ∧ inflightCount createProcessor = 0 := by
  simp [pendingCount, inflightCount, createProcessor, DurableQueue.empty]

theorem enqueue_increases_pending (state : ProcessorState) (payload : String) (now : Nat) :
    pendingCount (enqueue state payload now) = pendingCount state + 1 := by
  simp [pendingCount, enqueue, DurableQueue.enqueue, List.length_append]

theorem enqueue_preserves_inflight (state : ProcessorState) (payload : String) (now : Nat) :
    inflightCount (enqueue state payload now) = inflightCount state := by
  simp [inflightCount, enqueue, DurableQueue.enqueue]

theorem dequeue_decreases_pending (state : ProcessorState) (h : state.pending ≠ []) :
    (dequeue state).2.pending.length < state.pending.length := by
  simp [dequeue]
  cases hpend : state.pending with
  | nil => exact absurd hpend h
  | cons msg rest => simp [DurableQueue.deliver, hpend]

theorem ack_clears_id (state : ProcessorState) (id : Nat) :
    (ack state id).inflight = state.inflight.filter (fun m => m.id ≠ id) :=
  ack_removes_from_inflight state id

theorem nack_total_bounded (state : ProcessorState) (id : Nat) :
    (nack state id).total ≤ state.total + 1 := nack_total_le state id

theorem enqueue_total_eq (state : ProcessorState) (payload : String) (now : Nat) :
    (enqueue state payload now).total = state.total + 1 :=
  enqueue_total state payload now

theorem dequeue_some_iff_nonempty (state : ProcessorState) :
    (dequeue state).1.isSome = true ↔ state.pending ≠ [] := by
  constructor
  · intro h
    simp [dequeue, DurableQueue.deliver] at h
    cases hpend : state.pending with
    | nil => simp [hpend] at h
    | cons _ _ => simp [hpend]
  · intro h
    cases hpend : state.pending with
    | nil => exact absurd hpend h
    | cons msg rest =>
      simp [dequeue, DurableQueue.deliver, hpend]

theorem enqueue_preserves_deadLetter_eq (state : ProcessorState) (payload : String) (now : Nat) :
    (enqueue state payload now).deadLetter = state.deadLetter := by
  simp [enqueue, DurableQueue.enqueue]

end TSLean.Generated.QueueProcessor
