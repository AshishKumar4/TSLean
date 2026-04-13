// ============================================================================
// Durable Object — Rate Limiter with Alarm-Based Window Expiry
// ============================================================================
//
// A sliding-window rate limiter that uses the Alarm API to clean up expired
// event timestamps. Demonstrates:
//   - storage.get / storage.put for persistent event log
//   - storage.getAlarm / storage.setAlarm for deferred cleanup
//   - alarm() handler for background processing
//
// TSLean maps alarm operations to DurableObjects.Alarm (AlarmState model):
//   - this.ctx.storage.getAlarm()     → AlarmState.next (returns Option Alarm)
//   - this.ctx.storage.setAlarm(time) → AlarmState.schedule (adds alarm to pending)
//   - this.ctx.storage.deleteAlarm()  → AlarmState.empty (clears all alarms)
//   - async alarm() handler           → def alarm : DOMonad σ Unit
//
// The Lean AlarmState model tracks pending/fired/nextId with proved properties:
//   - schedule_increases_pending: scheduling adds to the pending list
//   - tick_fires_due: advancing time moves due alarms to fired
//   - cancel_removes: cancellation removes from pending
//
// Veil verification stub (with --veil flag):
//   The Veil bridge generates a TransitionSystem with actions for fetch and
//   alarm. The safety property to verify: "in-window event count never
//   exceeds maxRequests". See lean/TSLean/Veil/RateLimiterDO.lean for a
//   hand-written proof of this property.

export class RateLimiter extends DurableObject {
  // -- fetch: check rate limit, record event, schedule cleanup alarm.
  async fetch(request: Request): Promise<Response> {
    const now = Date.now();
    const windowMs = 60000;
    const maxRequests = 100;

    // Read the event log from storage
    const events: number[] = (await this.ctx.storage.get("events")) ?? [];
    // Filter to events within the sliding window
    const recent = events.filter((t: number) => now - t < windowMs);

    // Reject if over the limit
    if (recent.length >= maxRequests) {
      return new Response("Rate limited", { status: 429 });
    }

    // Record the new event and persist
    recent.push(now);
    await this.ctx.storage.put("events", recent);

    // Schedule an alarm to clean up expired events if none is pending.
    // getAlarm returns null if no alarm is set.
    const alarm = await this.ctx.storage.getAlarm();
    if (!alarm) {
      await this.ctx.storage.setAlarm(now + windowMs);
    }

    return new Response("OK");
  }

  // -- alarm: fired by the runtime when a scheduled alarm time arrives.
  // -- Cleans up expired events from the window.
  // -- AlarmInvocationInfo (optional param) carries retryCount for retry logic.
  async alarm(): Promise<void> {
    const now = Date.now();
    const events: number[] = (await this.ctx.storage.get("events")) ?? [];
    const recent = events.filter((t: number) => now - t < 60000);
    await this.ctx.storage.put("events", recent);
  }
}
