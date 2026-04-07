-- TSLean.DurableObjects.ChatRoom
import TSLean.Runtime.BrandedTypes
import TSLean.Runtime.Monad

namespace TSLean.DO.ChatRoom
open TSLean

structure ChatMessage where
  id        : MessageId
  roomId    : RoomId
  authorId  : UserId
  content   : String
  timestamp : Nat
  deriving Repr, BEq

structure ChatRoom where
  id       : RoomId
  members  : List UserId
  messages : List ChatMessage
  deriving Repr

def ChatRoom.wellOrdered (r : ChatRoom) : Prop :=
  r.messages.Pairwise (fun a b => a.timestamp ≤ b.timestamp)

def ChatRoom.broadcast (r : ChatRoom) (msg : ChatMessage) : ChatRoom :=
  { r with messages := r.messages ++ [msg] }

def ChatRoom.join (r : ChatRoom) (uid : UserId) : ChatRoom :=
  if r.members.contains uid then r else { r with members := uid :: r.members }

def ChatRoom.leave (r : ChatRoom) (uid : UserId) : ChatRoom :=
  { r with members := r.members.filter (· != uid) }

def ChatRoom.getMessages (r : ChatRoom) (since : Nat) : List ChatMessage :=
  r.messages.filter (fun m => m.timestamp > since)

def ChatRoom.messageCount (r : ChatRoom) : Nat := r.messages.length

def ChatRoom.memberCount (r : ChatRoom) : Nat := r.members.length

theorem broadcast_appends (r : ChatRoom) (msg : ChatMessage) :
    (r.broadcast msg).messages = r.messages ++ [msg] := rfl

theorem broadcast_count (r : ChatRoom) (msg : ChatMessage) :
    (r.broadcast msg).messageCount = r.messageCount + 1 := by
  simp [ChatRoom.broadcast, ChatRoom.messageCount, List.length_append]

theorem broadcast_preserves_members (r : ChatRoom) (msg : ChatMessage) :
    (r.broadcast msg).members = r.members := rfl

theorem join_adds_member (r : ChatRoom) (uid : UserId) (h : ¬r.members.contains uid) :
    uid ∈ (r.join uid).members := by
  simp only [ChatRoom.join]
  rw [if_neg h]
  simp

theorem leave_removes_member (r : ChatRoom) (uid : UserId) : uid ∉ (r.leave uid).members := by
  simp [ChatRoom.leave, List.mem_filter, BEq.refl]

theorem getMessages_subset (r : ChatRoom) (since : Nat) :
    (r.getMessages since).length ≤ r.messageCount := by
  simp only [ChatRoom.getMessages, ChatRoom.messageCount]
  exact List.length_filter_le _ _

theorem wellOrdered_broadcast (r : ChatRoom) (msg : ChatMessage) (h : r.wellOrdered)
    (hord : ∀ m ∈ r.messages, m.timestamp ≤ msg.timestamp) :
    (r.broadcast msg).wellOrdered := by
  simp only [ChatRoom.wellOrdered, ChatRoom.broadcast]
  rw [List.pairwise_append]
  exact ⟨h, List.pairwise_singleton _ _, fun m hm b hb => by
    simp only [List.mem_singleton] at hb; rw [hb]; exact hord m hm⟩

-- Additional theorems

theorem join_idempotent (r : ChatRoom) (uid : UserId) :
    (r.join uid).join uid = r.join uid := by
  simp only [ChatRoom.join]
  split
  · next h => simp [h]
  · next h =>
    simp only [List.contains_cons, beq_self_eq_true, Bool.true_or, ↓reduceIte]

theorem leave_idempotent (r : ChatRoom) (uid : UserId) :
    (r.leave uid).leave uid = r.leave uid := by
  simp [ChatRoom.leave, List.filter_filter, Bool.and_self]

theorem join_increases_members (r : ChatRoom) (uid : UserId) (h : ¬r.members.contains uid) :
    (r.join uid).memberCount = r.memberCount + 1 := by
  simp only [ChatRoom.join, ChatRoom.memberCount]
  rw [if_neg h]; simp

theorem leave_decreases_members (r : ChatRoom) (uid : UserId) (h : uid ∈ r.members) :
    (r.leave uid).memberCount ≤ r.memberCount := by
  simp [ChatRoom.leave, ChatRoom.memberCount, List.length_filter_le]

theorem no_duplicate_members (r : ChatRoom) (uid : UserId) :
    let r' := r.join uid
    ¬(r'.join uid).members.length > r'.members.length := by
  simp only [ChatRoom.join]
  split <;> simp [Nat.le_refl]

theorem broadcast_delivers_all (r : ChatRoom) (msg : ChatMessage) :
    msg ∈ (r.broadcast msg).messages := by
  simp [ChatRoom.broadcast]

theorem message_ordering_preserved (r : ChatRoom) (msg : ChatMessage) (h : r.wellOrdered)
    (hmax : ∀ m ∈ r.messages, m.timestamp ≤ msg.timestamp) :
    (r.broadcast msg).messages.getLast? = some msg := by
  simp [ChatRoom.broadcast, List.getLast?_append]

theorem join_then_member (r : ChatRoom) (uid : UserId) :
    (r.join uid).members.contains uid = true := by
  simp [ChatRoom.join]
  split
  · next h => exact h
  · next h => simp [List.contains_cons, beq_self_eq_true]

theorem leave_preserves_others (r : ChatRoom) (uid uid' : UserId) (hne : uid ≠ uid')
    (h : uid' ∈ r.members) : uid' ∈ (r.leave uid).members := by
  simp only [ChatRoom.leave, List.mem_filter]
  exact ⟨h, by simp [bne_iff_ne, Ne.symm hne]⟩






-- Additional theorems (second batch)

theorem messages_append_assoc (r : ChatRoom) (m1 m2 : ChatMessage) :
    ((r.broadcast m1).broadcast m2).messages = r.messages ++ [m1, m2] := by
  simp [ChatRoom.broadcast, List.append_assoc]

theorem broadcast_is_monotone (r : ChatRoom) (msg : ChatMessage) :
    r.messageCount ≤ (r.broadcast msg).messageCount := by
  simp [ChatRoom.messageCount, ChatRoom.broadcast, List.length_append]

theorem getMessages_length_le_total (r : ChatRoom) (since : Nat) :
    (r.getMessages since).length ≤ r.messageCount := getMessages_subset r since

theorem member_of_join (r : ChatRoom) (uid : UserId) (hmem : ¬r.members.contains uid) :
    uid ∈ (r.join uid).members := by
  simp only [ChatRoom.join, hmem, ↓reduceIte]
  simp [List.mem_cons]

end TSLean.DO.ChatRoom
