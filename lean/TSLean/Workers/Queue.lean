-- TSLean.Workers.Queue
-- Cloudflare Queues bindings.
--
-- Every operation is `opaque`, never `axiom`: this module is in the emitted trusted base, and an
-- `axiom` is a new assumption that every proof reaching it inherits. `opaque` names the same
-- unknown constant without assuming anything, because each result type is already nonempty.

import TSLean.Runtime.Basic

namespace TSLean.Workers.Queue

-- Producer side: send messages to a queue. No `Inhabited`: the handle may be
-- empty, and only the runtime binding produces one.
opaque QueueSender : Type

opaque send (q : QueueSender) (message : String) : IO Unit
opaque sendBatch (q : QueueSender) (messages : Array String) : IO Unit

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
opaque QueueMessage.ack (msg : QueueMessage) : IO Unit
opaque QueueMessage.retry (msg : QueueMessage) : IO Unit
opaque MessageBatch.ackAll (batch : MessageBatch) : IO Unit
opaque MessageBatch.retryAll (batch : MessageBatch) : IO Unit

end TSLean.Workers.Queue
