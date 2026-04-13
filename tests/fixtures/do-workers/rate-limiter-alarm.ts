// Rate limiter with alarm-based window expiry
export class RateLimiter extends DurableObject {
  async fetch(request: Request): Promise<Response> {
    const now = Date.now();
    const windowMs = 60000;
    const maxRequests = 100;

    const events: number[] = (await this.ctx.storage.get("events")) ?? [];
    const recent = events.filter((t: number) => now - t < windowMs);

    if (recent.length >= maxRequests) {
      return new Response("Rate limited", { status: 429 });
    }

    recent.push(now);
    await this.ctx.storage.put("events", recent);

    const alarm = await this.ctx.storage.getAlarm();
    if (!alarm) {
      await this.ctx.storage.setAlarm(now + windowMs);
    }

    return new Response("OK");
  }

  async alarm(): Promise<void> {
    const now = Date.now();
    const events: number[] = (await this.ctx.storage.get("events")) ?? [];
    const recent = events.filter((t: number) => now - t < 60000);
    await this.ctx.storage.put("events", recent);
  }
}
