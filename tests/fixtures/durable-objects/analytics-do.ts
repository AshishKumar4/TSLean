interface Metric { count: number; sum: number; min: number; max: number; lastSeen: number }

export class AnalyticsDO {
  private state: DurableObjectState;
  constructor(state: DurableObjectState, env: Env) { this.state = state; }
  async fetch(request: Request): Promise<Response> {
    const url = new URL(request.url);
    if (request.method === "POST" && url.pathname === "/track") {
      const event = await request.json() as { name: string; value?: number; timestamp: number };
      await this.trackEvent(event);
      return new Response(JSON.stringify({ success: true }), { headers: { "Content-Type": "application/json" } });
    }
    if (request.method === "GET" && url.pathname === "/count") {
      const name = url.searchParams.get("event") ?? "";
      const metric = await this.state.storage.get<Metric>(`metric:${name}`);
      return new Response(JSON.stringify({ event: name, count: metric?.count ?? 0 }), { headers: { "Content-Type": "application/json" } });
    }
    if (request.method === "DELETE" && url.pathname === "/reset") {
      await this.state.storage.deleteAll();
      return new Response(JSON.stringify({ success: true }), { headers: { "Content-Type": "application/json" } });
    }
    return new Response("Not Found", { status: 404 });
  }
  private async trackEvent(event: { name: string; value?: number; timestamp: number }): Promise<void> {
    const key = `metric:${event.name}`;
    const existing = await this.state.storage.get<Metric>(key);
    const value = event.value ?? 1;
    const updated: Metric = existing
      ? { count: existing.count + 1, sum: existing.sum + value, min: Math.min(existing.min, value), max: Math.max(existing.max, value), lastSeen: event.timestamp }
      : { count: 1, sum: value, min: value, max: value, lastSeen: event.timestamp };
    await this.state.storage.put(key, updated);
    const total = await this.state.storage.get<number>("total:events") ?? 0;
    await this.state.storage.put("total:events", total + 1);
  }
}
