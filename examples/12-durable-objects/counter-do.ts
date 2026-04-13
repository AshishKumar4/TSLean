// ============================================================================
// Durable Object — Counter with Storage Persistence
// ============================================================================
//
// The simplest Durable Object: an integer counter that persists across requests
// using the KV storage API.
//
// TSLean maps this to:
//   1. A `CounterState` structure with the class's state fields
//   2. A `namespace Counter` containing each method as a Lean def
//   3. Storage operations mapped to DurableObjects.Model (pure AssocMap)
//
// Lean output structure:
//   structure CounterState where
//     count : Float := 0
//
//   namespace Counter
//     def init : CounterState := { count := 0 }
//     def increment (self : CounterState) : IO Float := ...
//     def decrement (self : CounterState) : IO Float := ...
//     def getCount  (self : CounterState) : Float := self.count
//     def fetch     (self : CounterState) (request : Request) : IO Response := ...
//   end Counter
//
// Key DO patterns demonstrated:
//   - extends DurableObject         → detected by isDOClass(), triggers DO mode
//   - constructor(ctx, env)         → ctx/env filtered from state; init synthesized
//   - this.count++ / this.count--   → modify fun s => { s with count := s.count + 1 }
//   - this.ctx.storage.put(k, v)    → Storage.put via modify in DOMonad
//   - this.ctx.storage.get(k)       → Storage.get (pure read)

export class Counter extends DurableObject {
  private count: number = 0;

  constructor(ctx: DurableObjectState, env: Env) {
    super(ctx, env);
    // In a real app you'd use blockConcurrencyWhile to hydrate from storage:
    //   ctx.blockConcurrencyWhile(async () => {
    //     this.count = (await ctx.storage.get("count")) ?? 0;
    //   });
  }

  // -- Increment: mutates this.count (→ modify in StateT) then persists to storage.
  async increment(): Promise<number> {
    this.count++;
    await this.ctx.storage.put("count", this.count);
    return this.count;
  }

  // -- Decrement: same pattern.
  async decrement(): Promise<number> {
    this.count--;
    await this.ctx.storage.put("count", this.count);
    return this.count;
  }

  // -- Pure read: no side effects → plain Lean def, no IO monad.
  async getCount(): Promise<number> {
    return this.count;
  }

  // -- HTTP handler: routes requests to methods.
  // -- new URL(request.url) → URL.parse
  // -- new Response(body) → mkResponse body
  async fetch(request: Request): Promise<Response> {
    const url = new URL(request.url);
    if (url.pathname === "/increment") {
      const c = await this.increment();
      return new Response(String(c));
    }
    return new Response(String(this.count));
  }
}
