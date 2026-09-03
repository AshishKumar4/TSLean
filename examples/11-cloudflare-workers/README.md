# 11 — Cloudflare Workers

A standard Cloudflare Workers fetch handler with KV bindings and a scheduled (cron) handler.

## Run

```bash
npx tsx src/cli.ts examples/11-cloudflare-workers/worker-basic.ts -o examples/11-cloudflare-workers/output.lean
```

## What to look for

- `export default { fetch, scheduled }` → `namespace Worker` with `def fetch` and `def scheduled`
- `new URL(request.url)` → `URL.parse request.url`
- `new Response("body", { status: 404 })` → `mkResponse "body"`
- `env.CACHE.get(key)` → KV namespace access (axiomatized via `TSLean.Workers.KV`)
- `url.searchParams.get("key")` → field access on `URL.searchParams`
- `console.log(...)` → `IO.println ...`

## Workers entry point pattern

TSLean detects `export default { fetch }` (or `scheduled`, `queue`) and wraps the handler methods in a `namespace Worker` block. Each handler gets its original parameters as typed Lean function arguments:

```
TypeScript:  async fetch(request: Request, env: Env, ctx: ExecutionContext): Promise<Response>
Lean:        def fetch (request : Request) (env : Env) (ctx : ExecutionContext) : IO Response
```

## Workers bindings

The `Env` interface declares KV, R2, D1, Queue, and DO namespace bindings. TSLean provides Lean stubs for each in `lean/TSLean/Workers/`:

| Binding | Lean Module | Operations |
|---------|------------|------------|
| `KVNamespace` | `TSLean.Workers.KV` | `get`, `put`, `delete`, `list` |
| `R2Bucket` | `TSLean.Workers.R2` | `get`, `put`, `delete`, `list`, `head` |
| `D1Database` | `TSLean.Workers.D1` | `prepare`, `exec`, `batch` |
| `Queue` | `TSLean.Workers.Queue` | `send`, `sendBatch` |
