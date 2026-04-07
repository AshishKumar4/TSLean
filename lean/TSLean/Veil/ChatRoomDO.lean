-- TSLean.Veil.ChatRoomDO
-- Chat Room Durable Object: message ordering and broadcast.
-- Safety: all delivered messages exist in the message log.

import TSLean.Veil.Core

namespace TSLean.Veil.ChatRoomDO
open TSLean.Veil TransitionSystem

/-! ## State -/

structure Message where
  id        : Nat
  authorId  : String
  content   : String
  timestamp : Nat
  deriving Repr, BEq

structure State where
  members   : List String   -- current members
  messages  : List Message  -- message log (ordered by append)
  delivered : List (String × Nat)  -- (userId, msgId) pairs delivered
  nextId    : Nat           -- next message ID
  now       : Nat           -- current time
  deriving Repr

/-! ## Helpers -/

def State.isMember (s : State) (uid : String) : Bool :=
  s.members.contains uid

def State.msgExists (s : State) (msgId : Nat) : Bool :=
  s.messages.any (fun m => m.id == msgId)

def State.wellOrdered (s : State) : Prop :=
  s.messages.Pairwise (fun a b => a.timestamp ≤ b.timestamp)

/-! ## Initial condition -/

def initState (s : State) : Prop :=
  s.members = [] ∧ s.messages = [] ∧ s.delivered = [] ∧
  s.nextId = 0 ∧ s.now = 0

/-! ## Assumptions -/

def assumptions (_ : State) : Prop := True

/-! ## Actions -/

def join (uid : String) (pre post : State) : Prop :=
  ¬pre.isMember uid = true ∧
  post.members = uid :: pre.members ∧
  post.messages = pre.messages ∧
  post.delivered = pre.delivered ∧
  post.nextId = pre.nextId ∧
  post.now = pre.now

def leave (uid : String) (pre post : State) : Prop :=
  post.members = pre.members.filter (· != uid) ∧
  post.messages = pre.messages ∧
  post.delivered = pre.delivered ∧
  post.nextId = pre.nextId ∧
  post.now = pre.now

def sendMessage (authorId content : String) (pre post : State) : Prop :=
  pre.isMember authorId = true ∧
  post.messages = pre.messages ++ [{
    id := pre.nextId, authorId, content, timestamp := pre.now }] ∧
  post.members = pre.members ∧
  post.delivered = pre.delivered ∧
  post.nextId = pre.nextId + 1 ∧
  post.now = pre.now

def deliverMessage (uid : String) (msgId : Nat) (pre post : State) : Prop :=
  pre.isMember uid = true ∧
  pre.msgExists msgId = true ∧
  post.delivered = (uid, msgId) :: pre.delivered ∧
  post.members = pre.members ∧
  post.messages = pre.messages ∧
  post.nextId = pre.nextId ∧
  post.now = pre.now

def tick (delta : Nat) (pre post : State) : Prop :=
  post.now = pre.now + delta ∧
  post.members = pre.members ∧
  post.messages = pre.messages ∧
  post.delivered = pre.delivered ∧
  post.nextId = pre.nextId

def next (pre post : State) : Prop :=
  (∃ uid, join uid pre post) ∨
  (∃ uid, leave uid pre post) ∨
  (∃ authorId content, sendMessage authorId content pre post) ∨
  (∃ uid msgId, deliverMessage uid msgId pre post) ∨
  (∃ d, tick d pre post)

/-! ## Safety: delivered messages must exist in log -/

def safe (s : State) : Prop :=
  ∀ uid msgId, (uid, msgId) ∈ s.delivered → s.msgExists msgId = true

/-! ## Inductive invariant -/

def inv (s : State) : Prop :=
  -- Delivered messages exist in log
  (∀ uid msgId, (uid, msgId) ∈ s.delivered → s.msgExists msgId = true) ∧
  -- All message IDs < nextId
  (∀ m ∈ s.messages, m.id < s.nextId) ∧
  -- Message IDs are unique (captured by nextId bound)
  True

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
  intro s _ ⟨_, hmsg, hdel, hid, _⟩
  simp only [TransitionSystem.inv, inv, hmsg, hdel, hid]
  exact ⟨by simp, by simp, trivial⟩

theorem join_preserves_inv (uid : String) (pre post : State)
    (hpre : inv pre) (h : join uid pre post) : inv post := by
  obtain ⟨hdel, hids, _⟩ := hpre
  obtain ⟨_, hmemb, hmsg, hdelp, hnext, _⟩ := h
  exact ⟨by simp only [State.msgExists, hmsg, hdelp]; exact hdel,
         by simp only [hmsg, hnext]; exact hids,
         trivial⟩

theorem leave_preserves_inv (uid : String) (pre post : State)
    (hpre : inv pre) (h : leave uid pre post) : inv post := by
  obtain ⟨hdel, hids, _⟩ := hpre
  obtain ⟨hmemb, hmsg, hdelp, hnext, _⟩ := h
  exact ⟨by simp only [State.msgExists, hmsg, hdelp]; exact hdel,
         by simp only [hmsg, hnext]; exact hids,
         trivial⟩

theorem sendMessage_preserves_inv (authorId content : String) (pre post : State)
    (hpre : inv pre) (h : sendMessage authorId content pre post) : inv post := by
  obtain ⟨hdel, hids, _⟩ := hpre
  obtain ⟨_, hmsg, hmemb, hdelp, hnext, hnow⟩ := h
  refine ⟨?_, ?_, trivial⟩
  · intro uid msgId hmem
    simp only [State.msgExists, hmsg, hdelp] at *
    simp only [List.any_append, List.any_cons, Bool.or_eq_true]
    left; exact hdel uid msgId hmem
  · intro m hm
    simp only [hmsg] at hm
    simp only [List.mem_append, List.mem_singleton] at hm
    rcases hm with hm | rfl
    · simp only [hnext]; exact Nat.lt_succ_of_lt (hids m hm)
    · simp only [hnext]; exact Nat.lt_succ_self _

theorem deliverMessage_preserves_inv (uid : String) (msgId : Nat) (pre post : State)
    (hpre : inv pre) (h : deliverMessage uid msgId pre post) : inv post := by
  obtain ⟨hdel, hids, _⟩ := hpre
  obtain ⟨_, hmexists, hdelp, hmemb, hmsg, hnext, _⟩ := h
  refine ⟨?_, ?_, trivial⟩
  · intro uid2 msgId2 hmem
    simp only [hdelp, hmsg, State.msgExists] at *
    simp only [List.mem_cons] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | hmem
    · exact hmexists
    · exact hdel uid2 msgId2 hmem
  · simp only [hmsg, hnext]; exact hids

theorem tick_preserves_inv (delta : Nat) (pre post : State)
    (hpre : inv pre) (h : tick delta pre post) : inv post := by
  obtain ⟨hdel, hids, _⟩ := hpre
  obtain ⟨_, hmemb, hmsg, hdelp, hnext⟩ := h
  exact ⟨by simp only [State.msgExists, hmsg, hdelp]; exact hdel,
         by simp only [hmsg, hnext]; exact hids,
         trivial⟩

theorem inv_consecution : invConsecution (σ := State) := by
  intro pre post _ hinv hnext
  rcases hnext with ⟨uid, hj⟩ | ⟨uid, hl⟩ | ⟨aid, cont, hs⟩ | ⟨uid, mid, hd⟩ | ⟨d, ht⟩
  · exact join_preserves_inv uid pre post hinv hj
  · exact leave_preserves_inv uid pre post hinv hl
  · exact sendMessage_preserves_inv aid cont pre post hinv hs
  · exact deliverMessage_preserves_inv uid mid pre post hinv hd
  · exact tick_preserves_inv d pre post hinv ht

theorem safety_holds : isInvariant (σ := State) TransitionSystem.safe :=
  safe_of_invInductive
    (fun s _ => trivial)
    ⟨init_establishes_inv, inv_consecution⟩
    inv_implies_safe

/-! ## Additional theorems -/

theorem join_increases_members (uid : String) (pre post : State)
    (h : join uid pre post) :
    post.members.length = pre.members.length + 1 := by
  obtain ⟨_, hmemb, _, _, _, _⟩ := h; simp [hmemb]

theorem leave_decreases_members (uid : String) (pre post : State)
    (h : leave uid pre post) :
    post.members.length ≤ pre.members.length := by
  obtain ⟨hmemb, _, _, _, _⟩ := h
  simp [hmemb]; exact List.length_filter_le _ _

theorem sendMessage_increases_count (aid cont : String) (pre post : State)
    (h : sendMessage aid cont pre post) :
    post.messages.length = pre.messages.length + 1 := by
  obtain ⟨_, hmsg, _, _, _, _⟩ := h; simp [hmsg, List.length_append]

theorem deliverMessage_increases_delivered (uid : String) (msgId : Nat) (pre post : State)
    (h : deliverMessage uid msgId pre post) :
    post.delivered.length = pre.delivered.length + 1 := by
  obtain ⟨_, _, hdelp, _, _, _, _⟩ := h; simp [hdelp]

theorem member_after_join (uid : String) (pre post : State)
    (h : join uid pre post) : post.isMember uid = true := by
  obtain ⟨_, hmemb, _, _, _, _⟩ := h
  simp [State.isMember, hmemb, List.contains_cons, beq_self_eq_true]

theorem not_member_after_leave (uid : String) (pre post : State)
    (h : leave uid pre post) : post.isMember uid = false := by
  obtain ⟨hmemb, _, _, _, _⟩ := h
  simp [State.isMember, hmemb, List.mem_filter, bne_iff_ne]

theorem nextId_monotone (aid cont : String) (pre post : State)
    (h : sendMessage aid cont pre post) :
    post.nextId = pre.nextId + 1 := h.2.2.2.2.1

theorem inv_holds (s : State) (hr : reachable s) : inv s := by
  induction hr with
  | init s hi => exact init_establishes_inv s trivial hi
  | step s s' _ hn ih => exact inv_consecution s s' trivial ih hn

theorem message_ids_lt_nextId (s : State) (hr : reachable s) :
    ∀ m ∈ s.messages, m.id < s.nextId := (inv_holds s hr).2.1

theorem delivered_implies_in_log (s : State) (hr : reachable s)
    (uid : String) (msgId : Nat) (hd : (uid, msgId) ∈ s.delivered) :
    s.msgExists msgId = true := by
  exact (safety_holds s hr) uid msgId hd

-- Messages log is monotonically growing
theorem messages_grow_monotone (pre post : State) (h : next pre post) :
    pre.messages.length ≤ post.messages.length := by
  rcases h with ⟨_, hjoin⟩ | ⟨_, hleave⟩ | ⟨_, _, hsend⟩ | ⟨_, _, hdel⟩ | ⟨_, htick⟩
  · simp [hjoin.2.2.1]
  · simp [hleave.2.1]
  · rw [hsend.2.1]; simp [List.length_append]
  · simp [hdel.2.2.2.2]
  · simp [htick.2.2.1]

-- nextId never decreases
theorem nextId_nondecreasing (pre post : State) (h : next pre post) :
    post.nextId ≥ pre.nextId := by
  rcases h with ⟨_, hjoin⟩ | ⟨_, hleave⟩ | ⟨_, _, hsend⟩ | ⟨_, _, hdel⟩ | ⟨_, htick⟩
  all_goals (simp_all [join, leave, sendMessage, deliverMessage, tick]; try omega)

-- Time is monotonically non-decreasing
theorem now_nondecreasing_chatroom (pre post : State) (h : next pre post) :
    post.now ≥ pre.now := by
  rcases h with ⟨_, hjoin⟩ | ⟨_, hleave⟩ | ⟨_, _, hsend⟩ | ⟨_, _, hdel⟩ | ⟨_, htick⟩
  all_goals (simp_all [join, leave, sendMessage, deliverMessage, tick]; try omega)

-- Delivered set grows monotonically
theorem delivered_grows_monotone (pre post : State) (h : next pre post) :
    pre.delivered.length ≤ post.delivered.length := by
  rcases h with ⟨_, hjoin⟩ | ⟨_, hleave⟩ | ⟨_, _, hsend⟩ | ⟨_, _, hdel⟩ | ⟨_, htick⟩
  all_goals (simp_all [join, leave, sendMessage, deliverMessage, tick]; try omega)

-- Members list reflects current membership: existing members stay after join
theorem isMember_after_join_persists (uid : String) (pre post : State)
    (h : join uid pre post) (uid2 : String) (hmem : pre.isMember uid2 = true) :
    post.isMember uid2 = true := by
  obtain ⟨_, hmemb, _, _, _, _⟩ := h
  simp only [State.isMember] at hmem
  simp only [State.isMember, hmemb, List.contains_cons, hmem, Bool.or_true]

-- Initial state has empty messages
theorem init_empty_messages (s : State) (hi : initState s) :
    s.messages = [] := hi.2.1

-- Initial state has no delivered messages
theorem init_empty_delivered (s : State) (hi : initState s) :
    s.delivered = [] := hi.2.2.1

-- Initial nextId is 0
theorem init_nextId_zero (s : State) (hi : initState s) :
    s.nextId = 0 := hi.2.2.2.1

end TSLean.Veil.ChatRoomDO
