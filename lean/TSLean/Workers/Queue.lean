-- TSLean.Workers.Queue
-- Cloudflare Queues bindings (axiomatized).

import TSLean.Runtime.Basic

namespace TSLean.Workers.Queue

-- Producer side: send messages to a queue
opaque QueueSender : Type
instance : Inhabited QueueSender := ⟨sorry⟩

axiom send (q : QueueSender) (message : String) : IO Unit
axiom sendBatch (q : QueueSender) (messages : Array String) : IO Unit

-- Consumer side: receive a batch of messages
structure QueueMessage where
  id : String
  body : String
  timestamp : Nat
  deriving Repr, BEq, Inhabited

structure MessageBatch where
  messages : Array QueueMessage
  queue : String
  deriving Repr, BEq, Inhabited

-- Acknowledgment
axiom QueueMessage.ack (msg : QueueMessage) : IO Unit
axiom QueueMessage.retry (msg : QueueMessage) : IO Unit
axiom MessageBatch.ackAll (batch : MessageBatch) : IO Unit
axiom MessageBatch.retryAll (batch : MessageBatch) : IO Unit

end TSLean.Workers.Queue
