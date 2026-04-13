-- TSLean.Workers.Scheduler
-- Cloudflare Workers scheduled events and alarm invocation info.

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
axiom ScheduledEvent.noRetry (e : ScheduledEvent) : IO Unit

end TSLean.Workers.Scheduler
