export class CounterDO {
  private state: DurableObjectState;
  private count: number = 0;
  constructor(state: DurableObjectState, env: Env) {
    this.state = state;
    this.state.blockConcurrencyWhile(async () => {
      this.count = (await this.state.storage.get<number>("count")) ?? 0;
    });
  }
  async fetch(request: Request): Promise<Response> {
    const url = new URL(request.url);
    if (url.pathname === "/increment" && request.method === "POST") {
      this.count++;
      await this.state.storage.put("count", this.count);
      return new Response(JSON.stringify({ count: this.count }), { headers: { "Content-Type": "application/json" } });
    }
    if (url.pathname === "/decrement" && request.method === "POST") {
      this.count = Math.max(0, this.count - 1);
      await this.state.storage.put("count", this.count);
      return new Response(JSON.stringify({ count: this.count }), { headers: { "Content-Type": "application/json" } });
    }
    if (url.pathname === "/reset" && request.method === "POST") {
      this.count = 0;
      await this.state.storage.put("count", 0);
      return new Response(JSON.stringify({ count: 0 }), { headers: { "Content-Type": "application/json" } });
    }
    if (url.pathname === "/value" && request.method === "GET") {
      return new Response(JSON.stringify({ count: this.count }), { headers: { "Content-Type": "application/json" } });
    }
    return new Response("Not Found", { status: 404 });
  }
}
