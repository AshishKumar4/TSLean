-- TSLean.Workers.Scheduler
-- Cloudflare Workers scheduled events and alarm invocation info.
--
-- `noRetry` is `opaque`, never `axiom`: this module is in the emitted trusted base, and an `axiom`
-- is a new assumption that every proof reaching it inherits. `opaque` names the same unknown
-- constant without assuming anything, because `IO Unit` is already nonempty.

import TSLean.Runtime.Basic

namespace TSLean.Workers.Scheduler

structure AlarmInvocationInfo where
  retryCount : Nat
  isRetry : Bool
  deriving Repr, BEq, Inhabited

structure ScheduledEvent where
  scheduledTime : Nat
  cron : String
  deriving Repr, BEq, Inhabited

-- noRetry is a side-effecting call that prevents automatic retry
opaque ScheduledEvent.noRetry (e : ScheduledEvent) : IO Unit

end TSLean.Workers.Scheduler
