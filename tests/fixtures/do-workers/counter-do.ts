// Counter Durable Object — storage get/put, blockConcurrencyWhile
export class Counter extends DurableObject {
  private count: number = 0;

  constructor(ctx: DurableObjectState, env: Env) {
    super(ctx, env);
  }

  async increment(): Promise<number> {
    this.count++;
    await this.ctx.storage.put("count", this.count);
    return this.count;
  }

  async decrement(): Promise<number> {
    this.count--;
    await this.ctx.storage.put("count", this.count);
    return this.count;
  }

  async getCount(): Promise<number> {
    return this.count;
  }

  async fetch(request: Request): Promise<Response> {
    const url = new URL(request.url);
    if (url.pathname === "/increment") {
      const c = await this.increment();
      return new Response(String(c));
    }
    return new Response(String(this.count));
  }
}
