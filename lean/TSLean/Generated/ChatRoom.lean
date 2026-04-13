-- TSLean.Generated.ChatRoom
-- TypeScript → Lean 4 transpiled Durable Object for a chat room
-- Original TypeScript pattern: class ChatRoomDO extends DurableObject { ... }

import TSLean.DurableObjects.Model
import TSLean.DurableObjects.ChatRoom
import TSLean.Runtime.Monad
import TSLean.Runtime.BrandedTypes

namespace TSLean.Generated.ChatRoom
open TSLean TSLean.DO TSLean.DO.ChatRoom

abbrev Room := ChatRoom

def createRoom (id : RoomId) : Room :=
  { id, members := [], messages := [] }

def joinRoom (room : Room) (uid : UserId) : Room := room.join uid
def leaveRoom (room : Room) (uid : UserId) : Room := room.leave uid
def sendMessage (room : Room) (msg : ChatMessage) : Room := room.broadcast msg
def getMessages (room : Room) (since : Nat := 0) : List ChatMessage := room.getMessages since
def isMember (room : Room) (uid : UserId) : Bool := room.members.contains uid

theorem createRoom_empty (id : RoomId) :
    (createRoom id).members = [] ∧ (createRoom id).messages = [] := ⟨rfl, rfl⟩

theorem joinRoom_adds (room : Room) (uid : UserId) (h : ¬room.members.contains uid) :
    uid ∈ (joinRoom room uid).members := join_adds_member room uid h

theorem leaveRoom_removes (room : Room) (uid : UserId) :
    uid ∉ (leaveRoom room uid).members := ChatRoom.leave_removes_member room uid

theorem sendMessage_count (room : Room) (msg : ChatMessage) :
    (sendMessage room msg).messageCount = room.messageCount + 1 := broadcast_count room msg

theorem sendMessage_delivers (room : Room) (msg : ChatMessage) :
    msg ∈ (sendMessage room msg).messages := broadcast_delivers_all room msg

theorem isMember_after_join (room : Room) (uid : UserId) :
    isMember (joinRoom room uid) uid = true := join_then_member room uid

theorem not_isMember_after_leave (room : Room) (uid : UserId) :
    isMember (leaveRoom room uid) uid = false := by
  simp [isMember, leaveRoom, ChatRoom.leave, List.mem_filter, bne_iff_ne]

theorem getMessages_le_total (room : Room) (since : Nat) :
    (getMessages room since).length ≤ room.messageCount := getMessages_subset room since

theorem sendMessage_preserves_members (room : Room) (msg : ChatMessage) :
    (sendMessage room msg).members = room.members := broadcast_preserves_members room msg

theorem joinRoom_count (room : Room) (uid : UserId) (h : ¬room.members.contains uid) :
    (joinRoom room uid).memberCount = room.memberCount + 1 := join_increases_members room uid h

theorem leaveRoom_count (room : Room) (uid : UserId) (h : uid ∈ room.members) :
    (leaveRoom room uid).memberCount ≤ room.memberCount := leave_decreases_members room uid h

theorem join_idempotent_room (room : Room) (uid : UserId) :
    joinRoom (joinRoom room uid) uid = joinRoom room uid := join_idempotent room uid

theorem leave_idempotent_room (room : Room) (uid : UserId) :
    leaveRoom (leaveRoom room uid) uid = leaveRoom room uid := leave_idempotent room uid

theorem createRoom_zero_count (id : RoomId) : (createRoom id).messageCount = 0 := rfl
theorem createRoom_zero_members (id : RoomId) : (createRoom id).memberCount = 0 := rfl

theorem message_in_room_after_send (room : Room) (msg : ChatMessage) :
    (sendMessage room msg).messageCount > 0 := by
  rw [sendMessage_count]; omega

end TSLean.Generated.ChatRoom
