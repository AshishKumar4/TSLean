// ============================================================================
// Durable Object — Multi-DO with RPC Between Services
// ============================================================================
//
// Demonstrates multiple Durable Object classes in one module, with cross-DO
// communication via the standard fetch/RPC pattern:
//   - env.MY_DO.idFromName(name) → get a stable DO ID from a name
//   - env.MY_DO.get(id)          → get a stub handle to the DO instance
//   - stub.fetch(request)        → send an HTTP request to the DO
//   - stub.myMethod(args)        → RPC: call a public method directly
//
// TSLean maps the RPC pattern to DurableObjects.RPC (Serializer typeclass +
// RPCHandler). The Serializer typeclass requires a roundtrip proof; for
// auto-generated stubs this uses sorry.
//
// For multi-DO network verification, see DurableObjects.MultiDO which models
// message routing: DONetwork with inbox/outbox/delivered.
//
// Lean output structure:
//   structure OrderServiceState where (...)
//   namespace OrderService
//     def createOrder (self : OrderServiceState) (userId : String) (items : Array String) : IO String := ...
//     def getOrder    (self : OrderServiceState) (orderId : String) : IO String := ...
//     def fetch       (self : OrderServiceState) (request : Request) : IO Response := ...
//   end OrderService

export class OrderService extends DurableObject {
  // -- createOrder: generate a unique ID, persist order data to storage.
  // -- crypto.randomUUID() → "uuid-stub" (axiomatized, no real UUID generation in Lean)
  // -- storage.put(key, value) → Storage.put via modify in DOMonad
  async createOrder(userId: string, items: string[]): Promise<string> {
    const orderId = crypto.randomUUID();
    await this.ctx.storage.put(orderId, { userId, items, status: "pending" });
    return orderId;
  }

  // -- getOrder: read from storage, serialize to JSON.
  // -- storage.get(key) → Storage.get (returns Option StorageValue)
  // -- JSON.stringify(x) → serialize x (axiomatized in TSLean.Stdlib.JSON)
  async getOrder(orderId: string): Promise<string> {
    const order = await this.ctx.storage.get(orderId);
    return JSON.stringify(order);
  }

  // -- fetch: HTTP routing to methods.
  async fetch(request: Request): Promise<Response> {
    const url = new URL(request.url);
    if (url.pathname === "/create") {
      const id = await this.createOrder("user1", ["item1", "item2"]);
      return new Response(id);
    }
    return new Response("Not found", { status: 404 });
  }
}
