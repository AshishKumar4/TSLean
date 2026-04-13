interface QueueItem { id: string; payload: unknown; enqueuedAt: number; attempts: number; maxAttempts: number; nextRetryAt: number }

export class QueueProcessorDO {
  private state: DurableObjectState;
  constructor(state: DurableObjectState, env: Env) { this.state = state; }
  async fetch(request: Request): Promise<Response> {
    const url = new URL(request.url);
    if (request.method === "POST" && url.pathname === "/enqueue") {
      const body = await request.json() as { payload: unknown; maxAttempts?: number };
      const id = await this.enqueue(body.payload, body.maxAttempts ?? 3);
      return new Response(JSON.stringify({ id }), { headers: { "Content-Type": "application/json" } });
    }
    if (request.method === "POST" && url.pathname === "/process") {
      const processed = await this.processNext();
      return new Response(JSON.stringify({ processed }), { headers: { "Content-Type": "application/json" } });
    }
    if (request.method === "GET" && url.pathname === "/size") {
      const ids = await this.state.storage.get<string[]>("queue:ids") ?? [];
      return new Response(JSON.stringify({ size: ids.length }), { headers: { "Content-Type": "application/json" } });
    }
    return new Response("Not Found", { status: 404 });
  }
  private async enqueue(payload: unknown, maxAttempts: number): Promise<string> {
    const id = crypto.randomUUID();
    const item: QueueItem = { id, payload, enqueuedAt: Date.now(), attempts: 0, maxAttempts, nextRetryAt: Date.now() };
    await this.state.storage.put(`queue:${id}`, item);
    const ids = await this.state.storage.get<string[]>("queue:ids") ?? [];
    ids.push(id);
    await this.state.storage.put("queue:ids", ids);
    return id;
  }
  private async processNext(): Promise<boolean> {
    const ids = await this.state.storage.get<string[]>("queue:ids") ?? [];
    if (ids.length === 0) return false;
    const now = Date.now();
    for (const id of ids) {
      const item = await this.state.storage.get<QueueItem>(`queue:${id}`);
      if (!item || item.nextRetryAt > now) continue;
      item.attempts++;
      if (item.attempts >= item.maxAttempts) {
        await this.state.storage.put(`dlq:${id}`, item);
        await this.state.storage.delete(`queue:${id}`);
        await this.state.storage.put("queue:ids", ids.filter(i => i !== id));
      } else {
        item.nextRetryAt = now + Math.pow(2, item.attempts) * 1000;
        await this.state.storage.put(`queue:${id}`, item);
      }
      return true;
    }
    return false;
  }
}
