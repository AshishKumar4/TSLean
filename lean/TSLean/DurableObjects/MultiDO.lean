-- TSLean.DurableObjects.MultiDO
import TSLean.DurableObjects.RPC
import TSLean.Runtime.Monad

namespace TSLean.DO.MultiDO
open TSLean TSLean.DO.RPC

abbrev DOId := String

structure RPCEnvelope where
  from_ : DOId
  to_   : DOId
  req   : RPCRequest
  deriving Repr, BEq

structure RPCResponseEnvelope where
  from_ : DOId
  to_   : DOId
  resp  : RPCResponse
  deriving Repr

structure DONetwork where
  inbox     : List RPCEnvelope
  outbox    : List RPCResponseEnvelope
  delivered : List RPCEnvelope
  deriving Repr

def DONetwork.empty : DONetwork := { inbox := [], outbox := [], delivered := [] }

def DONetwork.send (net : DONetwork) (env : RPCEnvelope) : DONetwork :=
  { net with inbox := net.inbox ++ [env] }

def DONetwork.deliver (net : DONetwork) : Option RPCEnvelope × DONetwork :=
  match net.inbox with
  | []         => (none, net)
  | env :: rest => (some env, { net with inbox := rest, delivered := net.delivered ++ [env] })

def DONetwork.respond (net : DONetwork) (resp : RPCResponseEnvelope) : DONetwork :=
  { net with outbox := net.outbox ++ [resp] }

def DONetwork.wasDelivered (net : DONetwork) (env : RPCEnvelope) : Bool :=
  net.delivered.any (fun e => e.req.reqId == env.req.reqId && e.from_ == env.from_)

theorem rpc_roundtrip_empty (env : RPCEnvelope) :
    (DONetwork.empty.send env).deliver.1 = some env := by
  simp [DONetwork.empty, DONetwork.send, DONetwork.deliver]

theorem send_inbox_length (net : DONetwork) (env : RPCEnvelope) :
    (net.send env).inbox.length = net.inbox.length + 1 := by
  simp [DONetwork.send, List.length_append]

theorem deliver_inbox_le (net : DONetwork) :
    (net.deliver.2).inbox.length ≤ net.inbox.length := by
  cases h : net.inbox with
  | nil => simp [DONetwork.deliver, h]
  | cons msg rest => simp only [DONetwork.deliver, h]; simp

theorem deliver_delivered_length (net : DONetwork) (h : net.inbox.length > 0) :
    (net.deliver.2).delivered.length = net.delivered.length + 1 := by
  cases hbox : net.inbox with
  | nil => simp [hbox] at h
  | cons msg rest => simp [DONetwork.deliver, hbox, List.length_append]

theorem respond_outbox_length (net : DONetwork) (resp : RPCResponseEnvelope) :
    (net.respond resp).outbox.length = net.outbox.length + 1 := by
  simp [DONetwork.respond, List.length_append]

theorem wasDelivered_monotone (net : DONetwork) (env new_env : RPCEnvelope)
    (h : net.wasDelivered env = true) : (net.send new_env).wasDelivered env = true := by
  simp [DONetwork.wasDelivered, DONetwork.send] at *; exact h

theorem delivered_after_deliver (net : DONetwork) (env : RPCEnvelope)
    (h : net.deliver.1 = some env) : env ∈ (net.deliver.2).delivered := by
  simp only [DONetwork.deliver] at h ⊢
  split at h
  · simp at h
  · cases h; simp [List.mem_append]

theorem send_then_deliver_nonempty (net : DONetwork) (env : RPCEnvelope) :
    (net.send env).inbox.length > 0 := by
  simp [DONetwork.send, List.length_append]

theorem empty_network_deliver_none :
    DONetwork.empty.deliver.1 = none := by
  simp [DONetwork.empty, DONetwork.deliver]

theorem network_inbox_decreases (net : DONetwork) (h : net.inbox.length > 0) :
    (net.deliver.2).inbox.length < net.inbox.length := by
  cases hbox : net.inbox with
  | nil => simp [hbox] at h
  | cons hd tl => simp [DONetwork.deliver, hbox]

theorem respond_preserves_inbox (net : DONetwork) (resp : RPCResponseEnvelope) :
    (net.respond resp).inbox = net.inbox := rfl

theorem deliver_preserves_outbox (net : DONetwork) :
    (net.deliver.2).outbox = net.outbox := by
  simp [DONetwork.deliver]; cases net.inbox <;> rfl

theorem send_preserves_delivered (net : DONetwork) (env : RPCEnvelope) :
    (net.send env).delivered = net.delivered := rfl

theorem deliver_reqId_matches_head (net : DONetwork) (env : RPCEnvelope)
    (h : net.inbox = env :: net.inbox.tail) :
    net.deliver.1 = some env := by
  simp only [DONetwork.deliver]
  rw [h]

end TSLean.DO.MultiDO
