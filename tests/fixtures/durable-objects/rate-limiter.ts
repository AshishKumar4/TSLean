interface RequestRecord { timestamp: number; count: number }

export class RateLimiterDO {
  private state: DurableObjectState;
  private windowMs = 60_000;
  private maxRequests = 100;
  constructor(state: DurableObjectState, env: Env) { this.state = state; }

  async fetch(request: Request): Promise<Response> {
    const url = new URL(request.url);
    const clientId = url.searchParams.get("clientId") ?? "default";
    if (request.method === "POST" && url.pathname === "/check") {
      const allowed = await this.checkRateLimit(clientId);
      return new Response(JSON.stringify({ allowed, clientId }), {
        headers: { "Content-Type": "application/json" }, status: allowed ? 200 : 429,
      });
    }
    if (request.method === "DELETE" && url.pathname === "/reset") {
      await this.state.storage.delete(clientId);
      return new Response(JSON.stringify({ reset: true }), { headers: { "Content-Type": "application/json" } });
    }
    return new Response("Not Found", { status: 404 });
  }

  private async checkRateLimit(clientId: string): Promise<boolean> {
    const now = Date.now();
    const windowStart = now - this.windowMs;
    const records = await this.state.storage.get<RequestRecord[]>(clientId) ?? [];
    const valid = records.filter(r => r.timestamp >= windowStart);
    const total = valid.reduce((sum, r) => sum + r.count, 0);
    if (total >= this.maxRequests) return false;
    valid.push({ timestamp: now, count: 1 });
    await this.state.storage.put(clientId, valid);
    return true;
  }
}
