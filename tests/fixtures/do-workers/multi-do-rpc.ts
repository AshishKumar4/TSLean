// Multi-DO with RPC calls between DOs
export class OrderService extends DurableObject {
  async createOrder(userId: string, items: string[]): Promise<string> {
    const orderId = crypto.randomUUID();
    await this.ctx.storage.put(orderId, { userId, items, status: "pending" });
    return orderId;
  }

  async getOrder(orderId: string): Promise<string> {
    const order = await this.ctx.storage.get(orderId);
    return JSON.stringify(order);
  }

  async fetch(request: Request): Promise<Response> {
    const url = new URL(request.url);
    if (url.pathname === "/create") {
      const id = await this.createOrder("user1", ["item1", "item2"]);
      return new Response(id);
    }
    return new Response("Not found", { status: 404 });
  }
}
