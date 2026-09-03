// ============================================================================
// Cloudflare Workers — Basic Fetch Handler with KV
// ============================================================================
//
// Demonstrates the standard Workers module pattern:
//   export default { async fetch(request, env, ctx) { ... } }
//
// TSLean detects this pattern and wraps the handlers in a `namespace Worker`
// block. Each handler becomes a Lean function with typed parameters.
//
// Lean output structure:
//   namespace Worker
//     def fetch (request : Request) (env : Env) (ctx : ExecutionContext) : IO Response := ...
//   end Worker
//
// Key mappings:
//   new URL(request.url)           → URL.parse request.url
//   new Response("body")           → mkResponse "body"
//   new Response("body", {status}) → mkResponse "body" (with status)
//   url.pathname                   → url.pathname  (field access on URL structure)

// -- Env type declares the Workers bindings available to this Worker.
// -- In Lean, Env is a structure with fields for each binding.
interface WorkerEnv {
  CACHE: KVNamespace;
}

export default {
  // -- The main entry point for every HTTP request.
  // -- Maps to: def fetch (request : Request) (env : Env) (ctx : ExecutionContext) : IO Response
  async fetch(request: Request, env: WorkerEnv, ctx: ExecutionContext): Promise<Response> {
    const url = new URL(request.url);

    // -- Route: /hello → static greeting
    if (url.pathname === "/hello") {
      return new Response("Hello from Cloudflare Workers!");
    }

    // -- Route: /cached?key=X → KV lookup
    // -- KV.get maps to TSLean.Workers.KV.get (axiomatized IO operation)
    if (url.pathname === "/cached") {
      const key = url.searchParams.get("key");
      if (key) {
        const value = await env.CACHE.get(key);
        if (value) {
          return new Response(value);
        }
        return new Response("Key not found", { status: 404 });
      }
      return new Response("Missing key parameter", { status: 400 });
    }

    // -- Default: 404
    return new Response("Not Found", { status: 404 });
  },

  // -- Scheduled event handler (cron triggers).
  // -- Maps to: def scheduled (event : ScheduledEvent) (env : Env) (ctx : ExecutionContext) : IO Unit
  async scheduled(event: ScheduledEvent, env: WorkerEnv, ctx: ExecutionContext): Promise<void> {
    console.log(`Cron fired at ${event.scheduledTime}`);
  }
};
