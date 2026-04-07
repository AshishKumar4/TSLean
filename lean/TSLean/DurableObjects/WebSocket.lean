-- TSLean.DurableObjects.WebSocket
import TSLean.Runtime.Basic
import TSLean.Runtime.Monad

namespace TSLean.DO.WebSocket
open TSLean

inductive Session : Type where
  | end_   : Session
  | send   : String → Session → Session
  | recv   : String → Session → Session
  | choice : Session → Session → Session
  | offer  : Session → Session → Session
  deriving Repr, BEq, DecidableEq

def Session.dual : Session → Session
  | .end_         => .end_
  | .send lbl S   => .recv lbl S.dual
  | .recv lbl S   => .send lbl S.dual
  | .choice S₁ S₂ => .offer  S₁.dual S₂.dual
  | .offer  S₁ S₂ => .choice S₁.dual S₂.dual

inductive WsMessage where
  | text   : String → WsMessage
  | binary : ByteArray → WsMessage
  | ping   : WsMessage
  | pong   : WsMessage
  | close  : Nat → String → WsMessage
  deriving BEq

inductive WsState where
  | connecting | open_ | closing | closed
  deriving Repr, BEq, DecidableEq

instance : LawfulBEq WsState where
  eq_of_beq := by
    intro a b h; cases a <;> cases b <;>
    first | rfl | (exact absurd h (by decide))
  rfl := by intro a; cases a <;> decide

structure Channel (S : Session) where
  id    : String
  state : WsState
  deriving Repr

structure WsDoState where
  connections : List (String × WsState)
  messages    : List (String × WsMessage)

def WsDoState.empty : WsDoState := { connections := [], messages := [] }

def broadcast (state : WsDoState) (msg : WsMessage) : WsDoState :=
  let newMsgs := state.connections |>.filter (fun (_, s) => s == WsState.open_) |>.map (fun (id, _) => (id, msg))
  { state with messages := newMsgs ++ state.messages }

def closeConn (state : WsDoState) (id : String) : WsDoState :=
  { state with connections := state.connections.map fun (cid, s) =>
      if cid == id then (cid, WsState.closed) else (cid, s) }

def openConn (state : WsDoState) (id : String) : WsDoState :=
  { state with connections := (id, WsState.open_) :: state.connections }

theorem Session.dual_involutive (s : Session) : s.dual.dual = s := by
  induction s with
  | end_ => rfl
  | send lbl S ih => simp [Session.dual, ih]
  | recv lbl S ih => simp [Session.dual, ih]
  | choice S₁ S₂ h₁ h₂ => simp [Session.dual, h₁, h₂]
  | offer  S₁ S₂ h₁ h₂ => simp [Session.dual, h₁, h₂]

theorem Session.dual_end : Session.dual .end_ = .end_ := rfl
theorem Session.dual_send (lbl : String) (S : Session) : (Session.send lbl S).dual = .recv lbl S.dual := rfl
theorem Session.dual_recv (lbl : String) (S : Session) : (Session.recv lbl S).dual = .send lbl S.dual := rfl

theorem openConn_count (state : WsDoState) (id : String) :
    (openConn state id).connections.length = state.connections.length + 1 := by simp [openConn]

theorem closeConn_preserves_length (state : WsDoState) (id : String) :
    (closeConn state id).connections.length = state.connections.length := by simp [closeConn, List.length_map]

theorem connecting_ne_closed : WsState.connecting ≠ WsState.closed := by decide
theorem open_ne_closed : WsState.open_ ≠ WsState.closed := by decide

-- Additional theorems

theorem dual_send_recv_match (lbl : String) (S : Session) :
    (Session.send lbl S).dual = Session.recv lbl S.dual := rfl

theorem dual_recv_send_match (lbl : String) (S : Session) :
    (Session.recv lbl S).dual = Session.send lbl S.dual := rfl

theorem dual_choice_offer (S₁ S₂ : Session) :
    (Session.choice S₁ S₂).dual = Session.offer S₁.dual S₂.dual := rfl

theorem dual_offer_choice (S₁ S₂ : Session) :
    (Session.offer S₁ S₂).dual = Session.choice S₁.dual S₂.dual := rfl

theorem broadcast_empty_state (msg : WsMessage) :
    (broadcast WsDoState.empty msg).messages = [] := by
  simp [broadcast, WsDoState.empty]

theorem broadcast_delivers_to_open (state : WsDoState) (id : String) (msg : WsMessage)
    (h : (id, WsState.open_) ∈ state.connections) :
    (id, msg) ∈ (broadcast state msg).messages := by
  simp only [broadcast, List.mem_append]
  left
  apply List.mem_map.mpr
  exact ⟨(id, WsState.open_), List.mem_filter.mpr ⟨h, beq_self_eq_true _⟩, rfl⟩

theorem closeConn_closed (state : WsDoState) (id : String) :
    ∀ p ∈ (closeConn state id).connections, p.1 = id → p.2 = WsState.closed := by
  intro p hp heq
  simp only [closeConn, List.mem_map] at hp
  obtain ⟨⟨cid, s⟩, hmem, hpair⟩ := hp
  simp only at hpair
  split at hpair
  · next hcid =>
    -- cid == id = true: result is (cid, closed)
    cases hpair
    rfl
  · next hcid =>
    -- cid == id = false: result is (cid, s)
    -- p = (cid, s), p.1 = cid, heq : p.1 = id, so cid = id, contradicts hcid
    cases hpair
    simp only [Prod.fst] at heq
    rw [heq] at hcid
    simp [beq_self_eq_true] at hcid

theorem openConn_open (state : WsDoState) (id : String) :
    (id, WsState.open_) ∈ (openConn state id).connections := by
  simp [openConn]

-- WsState has DecidableEq derived
example : DecidableEq WsState := inferInstance

theorem Session.end_dual : Session.end_.dual = Session.end_ := rfl




-- Additional theorems (second batch)

theorem dual_involutive_composed (S₁ S₂ : Session) :
    (Session.choice S₁ S₂).dual = Session.offer S₁.dual S₂.dual := rfl

theorem send_dual_is_recv' (lbl : String) (S : Session) :
    (Session.send lbl S).dual = Session.recv lbl S.dual := rfl

theorem dual_of_offer_is_choice (S₁ S₂ : Session) :
    (Session.offer S₁ S₂).dual = Session.choice S₁.dual S₂.dual := rfl

theorem dual_preserves_via_dual (S : Session) :
    S.dual.dual = S := Session.dual_involutive S

theorem connecting_ne_open : WsState.connecting ≠ WsState.open_ := by decide

end TSLean.DO.WebSocket
