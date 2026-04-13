# TSLean Durable Objects & Cloudflare Workers Support — v2.0 Plan

## Status Quo

The transpiler has partial, ad-hoc DO awareness scattered across three files:

**What exists (parser/lower):**
- `isDOClass()` detects `extends DurableObject` or `DurableObjectState` ctor params (parser:370-377)
- `hasDOPattern()` injects a virtual `CF_AMBIENT` declaration file with ~25 Workers types (ambient.ts)
- DO constructor params (`ctx: DurableObjectState`, `env: Env`) are filtered from state fields (parser:387-388)
- `this.state.storage.get(key)` is rewritten to `Storage.get(...)` in the parser (parser:1271-1275)
- DO class methods are wrapped in a `Namespace` IR node (parser:333)
- `self.state.X` is flattened to `self.X` in the lowerer (lower.ts:1072-1077)
- `self.storage.X` is dropped to `default` (lower.ts:1079-1082)
- Storage operations in `lowerApp()` emit `sorry` — they are NOT actually lowered (lower.ts:1199-1201)
- Import scanning recognizes DO types and adds `TSLean.DurableObjects.*` imports (lower.ts:231-250)

**What exists (Lean library — 5,018 lines):**
- `DurableObjects/` — 15 modules: Model (Storage = AssocMap), State, Storage (batch ops), Http, WebSocket (session types), RPC (Serializer typeclass), Transaction, Alarm, Auth, ChatRoom, Queue, Hibernation, Analytics, MultiDO, RateLimiter, SessionStore
- `Veil/Core.lean` — `TransitionSystem` typeclass with `init`, `assumptions`, `next`, `safe`, `inv` + `reachable` inductive + 17 proved theorems (induction, safety, liveness)
- `Veil/DSL.lean` — `veil_action`, `veil_relation`, `veil_safety` macros + `next2..next5` combinators + `safety_of_inv_inductive` combinator + `veil_auto`/`state_ext` tactics
- `Veil/*DO.lean` — 6 verified transition systems (Counter, ChatRoom, Auth, Queue, RateLimiter, SessionStore) with full safety proofs
- `Veil/DSLAdoption.lean` — DSL re-formulations of all 6 DOs proving equivalence
- `Veil/DSLExamples.lean` — 3 pedagogical examples (NatCounter, TokenRing, BoundedQueue)
- `Runtime/Monad.lean` — `DOMonad σ α = StateT σ (ExceptT TSError IO) α` with 12 proved monad laws
- `Runtime/WebAPI.lean` — functional models for Headers, URL, SearchParams, Request, Response + 20 proved properties

**The gap:** The transpiler has zero awareness of the Lean library's rich DO models. Storage ops emit `sorry`. No alarm/WS/RPC/transaction handling. No Veil bridge. No `export default` worker entry. The 5,018 lines of hand-written Lean sit unused by the transpiler.

---

## Phase 1: Workers Type Stubs

**Goal:** Every Cloudflare Workers binding type compiles to a Lean type with correct operations.

### 1A. Expand `CF_AMBIENT` (ambient.ts)

The current ambient declares ~25 types but is missing several Workers binding types. Add:

| Type | Fields/Methods to Declare |
|------|--------------------------|
| `KVNamespace` | `get(key, opts?)`, `put(key, value, opts?)`, `delete(key)`, `list(opts?)`, `getWithMetadata(key)` |
| `R2Bucket` | `get(key)`, `put(key, value, opts?)`, `delete(key)`, `list(opts?)`, `head(key)` |
| `R2Object` | `key`, `body`, `httpMetadata`, `customMetadata`, `size`, `etag`, `version` |
| `D1Database` | `prepare(query)`, `exec(query)`, `batch(stmts)`, `dump()` |
| `D1PreparedStatement` | `bind(...values)`, `first(column?)`, `all()`, `raw()`, `run()` |
| `Queue<T>` | `send(message, opts?)`, `sendBatch(messages, opts?)` |
| `MessageBatch<T>` | `messages`, `queue`, `ackAll()`, `retryAll()` |
| `Message<T>` | `id`, `body`, `timestamp`, `ack()`, `retry()` |
| `AlarmInvocationInfo` | `retryCount: number`, `isRetry: boolean` |
| `WebSocketRequestResponsePair` | `request: string`, `response: string` |
| `ScheduledEvent` | `scheduledTime`, `cron`, `noRetry()` |

Also refine existing declarations:
- `DurableObjectState`: add `setWebSocketAutoResponse`, `getWebSocketAutoResponse`, `getWebSocketAutoResponseTimestamp`, `setHibernatableWebSocketEventTimeout`, `getHibernatableWebSocketEventTimeout` (from DO_API_REFERENCE.md)
- `DurableObjectStorage`: add `getCurrentBookmark`, `getBookmarkForTime`, `onNextSessionRestoreBookmark`, overloaded `put(entries: Record)`, overloaded `delete(keys: string[])`, `sql` property (type `SqlStorage`)
- `SqlStorage`: `exec(query, ...bindings)`, `ingest(filename, input)`, `databaseSize`

**Files changed:** `src/do-model/ambient.ts`

### 1B. Lean Stubs for Workers Bindings

Create new Lean modules parallel to the existing stubs pattern (opaque types + axiomatized ops):

| New File | Contents |
|----------|----------|
| `lean/TSLean/Workers/KV.lean` | `opaque KVNamespace : Type`, `axiom KV.get : KVNamespace → String → IO (Option String)`, `axiom KV.put`, `axiom KV.delete`, `axiom KV.list` |
| `lean/TSLean/Workers/R2.lean` | `opaque R2Bucket : Type`, `structure R2Object`, `axiom R2.get`, `axiom R2.put`, `axiom R2.delete`, `axiom R2.list`, `axiom R2.head` |
| `lean/TSLean/Workers/D1.lean` | `opaque D1Database : Type`, `opaque D1PreparedStatement : Type`, `axiom D1.prepare`, `axiom D1.exec`, `axiom D1.batch` |
| `lean/TSLean/Workers/Queue.lean` | `opaque QueueSender : Type`, `structure QueueMessage`, `axiom Queue.send`, `axiom Queue.sendBatch` |
| `lean/TSLean/Workers/Scheduler.lean` | `structure ScheduledEvent`, `structure AlarmInvocationInfo` |

**Pattern:** Follow `lean/TSLean/Stubs/NodeFs.lean` — opaque types for stateful handles, structures for data types, axioms for IO operations. Every opaque type gets an `Inhabited` instance.

### 1C. Type Mapping Updates

In `src/typemap/index.ts`, add recognition for Workers binding types so they resolve to the correct IR types instead of falling through to `TSAny`:

```
KVNamespace     → TyRef("KVNamespace")
R2Bucket        → TyRef("R2Bucket")
D1Database      → TyRef("D1Database")
Queue<T>        → TyRef("QueueSender", [T])
MessageBatch<T> → TyRef("MessageBatch", [T])
```

In `src/codegen/lower.ts` `scanTypeImports()`, add import triggers:
```
KVNamespace         → TSLean.Workers.KV
R2Bucket/R2Object   → TSLean.Workers.R2
D1Database/D1*      → TSLean.Workers.D1
QueueSender/Message → TSLean.Workers.Queue
AlarmInvocationInfo → TSLean.Workers.Scheduler
```

**Files changed:** `src/typemap/index.ts`, `src/codegen/lower.ts`

### 1D. `export default` Worker Entry Point

Recognize the Workers module entry pattern:

```typescript
export default {
  async fetch(request: Request, env: Env, ctx: ExecutionContext): Promise<Response> { ... }
  async scheduled(event: ScheduledEvent, env: Env, ctx: ExecutionContext): Promise<void> { ... }
  async queue(batch: MessageBatch, env: Env, ctx: ExecutionContext): Promise<void> { ... }
}
```

**Parser change:** In `parseExportAssignment()` / `parseExportDecl()`, detect object literal exports with `fetch`/`scheduled`/`queue` methods. Emit an IR `StructDef` named `Worker` with a `Namespace` containing the handler functions. Each handler gets `env: Env` and `ctx: ExecutionContext` as parameters.

**Lowerer change:** Emit a `namespace Worker` block. The `fetch` handler becomes `def Worker.fetch (req : Request) (env : Env) (ctx : ExecutionContext) : IO Response`.

**Files changed:** `src/parser/index.ts`, `src/codegen/lower.ts`

**Estimated effort:** Phase 1 total ~800 lines across 8 files

---

## Phase 2: DO Type Stubs and Storage Lowering

**Goal:** Every DurableObjectStorage / DurableObjectState operation maps to an actual Lean call instead of `sorry`.

### 2A. Storage Operation Lowering

The critical gap. Currently `lowerApp()` at lower.ts:1199-1201 emits `sorry` for all `Storage.*` calls. Replace with actual Lean function calls:

| TypeScript Call | IR After Parser | Lean Output |
|----------------|-----------------|-------------|
| `this.ctx.storage.get("key")` | `App(Var("Storage.get"), [self, litStr("key")])` | `Storage.get self.storage "key"` |
| `this.ctx.storage.put("key", val)` | `App(Var("Storage.put"), [self, litStr("key"), val])` | `Storage.put self.storage "key" val` |
| `this.ctx.storage.delete("key")` | `App(Var("Storage.delete"), [self, litStr("key")])` | `Storage.delete self.storage "key"` |
| `this.ctx.storage.deleteAll()` | `App(Var("Storage.clear"), [self])` | `Storage.clear` |
| `this.ctx.storage.list()` | `App(Var("Storage.list"), [self])` | `Storage.keys self.storage` |
| `this.ctx.storage.getAlarm()` | `App(Var("Storage.getAlarm"), [self])` | `AlarmState.next self.alarms` |
| `this.ctx.storage.setAlarm(t)` | `App(Var("Storage.setAlarm"), [self, t])` | `AlarmState.schedule self.alarms t now` |
| `this.ctx.storage.deleteAlarm()` | `App(Var("Storage.deleteAlarm"), [self])` | `AlarmState.cancel self.alarms ...` |
| `this.ctx.storage.transaction(fn)` | `App(Var("Storage.transaction"), [self, fn])` | `Transaction.commit (fn Transaction.empty) self.storage` |

**Implementation approach:**
1. In `lowerApp()`, replace the `sorry` fallback for `Storage.*` calls with a dispatch table mapping each storage method to its Lean equivalent.
2. Storage operations that mutate state (put, delete, deleteAll) should emit `modify fun s => { s with storage := ... }` since they operate inside `DOMonad`.
3. Storage operations that read (get, list) should emit `do let s ← get; pure (Storage.get s.storage key)`.

**Key design decision:** Storage ops run in `DOMonad σ` where `σ` is the DO's state type. The state type must include a `storage : Storage` field. Two approaches:

- **Option A (transparent storage):** Require the transpiled state struct to include `storage : Storage` as a field. The parser already filters out `DurableObjectState`/`Env` fields, so we'd add `storage : Storage` back as a synthetic field.
- **Option B (wrapped state):** Use `DOState σ` from Model.lean which wraps `{ appState : σ, storage : Storage }`. The transpiled methods operate on `DOState MyAppState`.

**Recommendation: Option B.** It matches the existing Lean library design (`DOState σ`), requires no changes to the user's TS code, and separates app-level state from storage state cleanly.

**Changes needed:**
1. Parser: when `isDOClass()`, synthesize the state struct without the `storage` field (already done), BUT lower the class methods to operate on `DOState <StateName>` instead of bare `<StateName>`.
2. Lowerer: emit `DOState <StateName>` as the monad state type. Map `self.storage` accesses to `(← get).storage`.

**Files changed:** `src/parser/index.ts`, `src/codegen/lower.ts`, `src/stdlib/index.ts` (add storage method table)

### 2B. SQL Storage Stubs

Add `sql` property access on `DurableObjectStorage`:

```typescript
this.ctx.storage.sql.exec("SELECT * FROM users WHERE id = ?", userId)
```

Lean output: axiomatized `SqlStorage.exec` returning `Array (AssocMap String String)`.

New file: `lean/TSLean/Workers/SqlStorage.lean` with `opaque SqlStorage : Type`, `axiom SqlStorage.exec : SqlStorage → String → Array String → IO (Array (AssocMap String String))`.

**Files changed:** `lean/TSLean/Workers/SqlStorage.lean` (new), `src/do-model/ambient.ts`, `src/codegen/lower.ts`

### 2C. `blockConcurrencyWhile` Lowering

```typescript
constructor(ctx: DurableObjectState, env: Env) {
  super(ctx, env);
  ctx.blockConcurrencyWhile(async () => {
    this.count = (await ctx.storage.get("count")) ?? 0;
  });
}
```

This is an initialization pattern. In the Lean model, it maps to the DOMonad's initial state computation — the callback's effect is "run before any concurrent requests."

**Lowering strategy:** Detect `blockConcurrencyWhile` calls in the constructor. Extract the callback body. Emit it as the `init` function of the DO, running in `DOMonad σ`. The callback's storage reads become the initial state hydration.

**Lean output:**
```lean
def MyDO.init : DOMonad MyDOState Unit := do
  let count ← Storage.get (← get).storage "count"
  modify fun s => { s with count := count.getD 0 }
```

**Files changed:** `src/parser/index.ts` (ctor parsing), `src/codegen/lower.ts`

### 2D. DurableObjectNamespace and Stub (RPC) Lowering

```typescript
const id = env.MY_DO.idFromName("my-id");
const stub = env.MY_DO.get(id);
const result = await stub.myMethod(args);  // RPC
```

**Lowering strategy:**
1. `env.MY_DO.idFromName(name)` → `DurableObjectId.fromName name` (pure)
2. `env.MY_DO.get(id)` → `DurableObjectNamespace.get env.MY_DO id` (pure, returns stub handle)
3. `stub.myMethod(args)` → `RPCRequest.mk "myMethod" (serialize args) reqId` piped through `RPCHandler.handle`
4. `stub.fetch(req)` → `DurableObjectStub.fetch stub req` (IO, axiomatized)

The Lean `DurableObjects/RPC.lean` already has `RPCRequest`, `RPCResponse`, `RPCHandler` typeclass, and `Serializer` typeclass. The bridge is: detect `.method()` calls on variables typed as `DurableObjectStub<T>`, look up `T`'s methods, and emit RPC dispatch.

**Files changed:** `src/codegen/lower.ts`, `src/stdlib/index.ts` (add DO method tables)

**Estimated effort:** Phase 2 total ~1200 lines across 6 files

---

## Phase 3: WebSocket Hibernation API

**Goal:** Full WebSocket Hibernation lifecycle: `acceptWebSocket`, `getWebSockets`, tag-based routing, WS event handlers.

### 3A. WS Handler Recognition

The DO API declares three WS handlers:
```typescript
async webSocketMessage(ws: WebSocket, message: string | ArrayBuffer): Promise<void> { ... }
async webSocketClose(ws: WebSocket, code: number, reason: string, wasClean: boolean): Promise<void> { ... }
async webSocketError(ws: WebSocket, error: unknown): Promise<void> { ... }
```

**Parser change:** In `parseClassDecl()`, detect methods named `webSocketMessage`, `webSocketClose`, `webSocketError`. Tag them as WS handlers in the IR (new flag on `FuncDef`: `isWSHandler?: boolean`). Map parameter types: `WebSocket` → the existing `WsState` or a new `WebSocketHandle` type, `string | ArrayBuffer` → `WsMessage` from WebSocket.lean.

### 3B. State/Context Method Lowering

| TypeScript | Lean |
|-----------|------|
| `this.ctx.acceptWebSocket(ws, tags?)` | `WsDoState.openConn wsState ws.id` + tag registration |
| `this.ctx.getWebSockets(tag?)` | filter `wsState.connections` by tag |
| `this.ctx.getTags(ws)` | lookup tags for connection id |
| `this.ctx.setWebSocketAutoResponse(pair)` | store auto-response config in state |
| `ws.send(message)` | `WsDoState.broadcast wsState msg [ws.id]` |
| `ws.close(code, reason)` | `WsDoState.closeConn wsState ws.id` |
| `ws.serializeAttachment(data)` | `Serializer.serialize data` |
| `ws.deserializeAttachment()` | `Serializer.deserialize ...` |

**Lean additions needed:**
- Extend `WsDoState` with tag tracking: `tags : AssocMap String (List String)` (connection id → tag list)
- Add `WsDoState.getByTag`, `WsDoState.setAutoResponse`
- Add `WebSocketHandle` structure wrapping connection id

**Files changed:** `lean/TSLean/DurableObjects/WebSocket.lean` (extend), `src/parser/index.ts`, `src/codegen/lower.ts`, `src/stdlib/index.ts`

### 3C. WebSocketPair in fetch()

```typescript
async fetch(request: Request): Promise<Response> {
  const [client, server] = Object.values(new WebSocketPair());
  this.ctx.acceptWebSocket(server);
  return new Response(null, { status: 101, webSocket: client });
}
```

**Parser change:** Recognize `new WebSocketPair()` → `WsDoState.openConn`. Recognize `Object.values(pair)` destructuring into `[client, server]`. The `Response(null, { status: 101, webSocket: client })` pattern → `HttpResponse.mk 101 ... client`.

**Lowerer change:** Add `WebSocketPair` to the known constructor table. Map the destructuring to a tuple binding.

**Estimated effort:** Phase 3 total ~600 lines across 5 files

---

## Phase 4: Alarm Handlers

**Goal:** `alarm()` handler + `setAlarm`/`deleteAlarm`/`getAlarm` fully lowered.

### 4A. Alarm Handler Recognition

```typescript
async alarm(alarmInfo?: AlarmInvocationInfo): Promise<void> {
  // retry logic using alarmInfo.retryCount
}
```

**Parser change:** Detect method named `alarm` on DO classes. Map `AlarmInvocationInfo` parameter with `retryCount: Nat` and `isRetry: Bool`.

**Lowerer change:** Emit `def MyDO.alarm (info : AlarmInvocationInfo) : DOMonad MyDOState Unit`. The alarm method operates on the same `DOMonad` as other methods.

### 4B. Alarm State Integration

The Lean library has `AlarmState` with `schedule`, `cancel`, `tick`, `next`, `hasDue`. The question is where alarm state lives.

**Design:** Extend `DOState σ` (or synthesize into the state struct) with an `alarms : AlarmState` field when alarm usage is detected. Then:

- `this.ctx.storage.setAlarm(time)` → `modify fun s => { s with alarms := s.alarms.schedule time now }`
- `this.ctx.storage.getAlarm()` → `do let s ← get; pure (s.alarms.next |>.map Alarm.scheduledAt)`
- `this.ctx.storage.deleteAlarm()` → `modify fun s => { s with alarms := ... }`

**Detection:** Scan the DO class for `setAlarm`/`getAlarm`/`deleteAlarm` calls or an `alarm()` method. If found, add `alarms : AlarmState` to the state type.

**Files changed:** `src/parser/index.ts`, `src/codegen/lower.ts`

**Estimated effort:** Phase 4 total ~300 lines across 3 files

---

## Phase 5: Veil Bridge — Auto-Generated Transition Systems

**Goal:** Given transpiled DO code, auto-generate Veil transition system stubs with `sorry`-proofed obligations, so users can fill in the proofs.

This is the most architecturally significant phase. The transpiler has enough information to generate the Veil boilerplate because it knows:
- The state structure (from the class fields)
- The actions (from the public methods)
- The state transitions (from `modify`/`set` calls in method bodies)

### 5A. Transition System Stub Generator

New module: `src/verification/veil-gen.ts`

**Input:** An `IRModule` containing a DO class (detected by `isDOClass()`).

**Output:** A Lean file containing:

```lean
import TSLean.Veil.DSL
import TSLean.Veil.Core
import <TranspiledDOModule>

open TSLean.Veil TransitionSystem TSLean.Veil.DSL

namespace <DOName>.Veil

-- State: reuse the transpiled state type
abbrev State := <DOName>State

-- Init: extracted from blockConcurrencyWhile or constructor
def initState (s : State) : Prop :=
  sorry -- TODO: specify initial state predicate

-- Assumptions: constraints that hold in all reachable states
def assumptions (s : State) : Prop :=
  sorry -- TODO: specify environment assumptions

-- Actions: one per public method, as relational predicates
-- Generated from method signatures and body analysis

veil_relation action_<method1> (pre post : State) where
  sorry -- TODO: specify pre/post conditions for <method1>

veil_relation action_<method2> (pre post : State) where
  sorry -- TODO: specify pre/post conditions for <method2>

-- ...one per public method...

-- Next: disjunction of all actions
-- Uses nextN combinator from DSL.lean
def next := next<N> action_<method1> action_<method2> ...

-- Safety: the property to verify
veil_safety safe (s : State) where
  sorry -- TODO: specify safety property

-- Invariant: strengthened inductive invariant
def inv (s : State) : Prop :=
  sorry -- TODO: specify inductive invariant (must imply safe)

-- TransitionSystem instance
instance : TransitionSystem State where
  init := initState
  assumptions := assumptions
  next := next
  safe := safe
  inv := inv

-- Proof obligations (fill in to complete verification)

theorem inv_implies_safe : invSafe (σ := State) :=
  sorry -- Prove: inv s → assumptions s → safe s

theorem init_establishes_inv : invInit (σ := State) :=
  sorry -- Prove: assumptions s → init s → inv s

-- Per-action preservation theorems
theorem <method1>_preserves_inv (pre post : State)
    (ha : assumptions pre) (hi : inv pre)
    (h : action_<method1> pre post) : inv post :=
  sorry

-- ...one per action...

-- Consecution via nextN_preserves
theorem inv_consecution : invConsecution (σ := State) :=
  sorry -- Use nextN_preserves with per-action theorems

-- Main safety theorem
theorem safety_holds : isInvariant (σ := State) safe :=
  sorry -- Use safety_of_inv_inductive

end <DOName>.Veil
```

### 5B. Smart Stub Population

Where possible, pre-fill the `sorry` placeholders with inferred content:

1. **`initState`:** If `blockConcurrencyWhile` was parsed, extract the field assignments and generate field equality predicates (e.g., `s.count = 0`).

2. **Action relations:** For methods where the body is fully lowered (no sorry), analyze the `modify`/`set` calls to generate relational predicates:
   - `modify fun s => { s with count := s.count + 1 }` → `post.count = pre.count + 1 ∧ post.otherField = pre.otherField`
   - Guards from `if` conditions before state mutation → preconditions

3. **`assumptions`:** Default to `True` (no assumptions). If the state has bounded fields (detected from guards like `count < maxCount`), suggest bounds.

4. **`nextN` selection:** Count the public methods, select the appropriate `next2`..`next5` combinator. If >5 actions, emit a manual disjunction.

### 5C. CLI Integration

Add a `--veil` flag to the CLI:

```bash
tslean counter.ts -o counter.lean --veil
```

This produces two files:
- `counter.lean` — the normal transpilation
- `counter_veil.lean` — the Veil transition system stub

For project mode (`--project --veil`), generate one `_veil.lean` file per DO class detected.

### 5D. Proof Obligation Connection

Extend `src/verification/index.ts` to generate Veil-specific obligations:

| Obligation Kind | Generated From | Lean Theorem |
|----------------|---------------|--------------|
| `InvariantInit` | constructor / blockConcurrencyWhile | `init_establishes_inv` |
| `InvariantConsecution` | each public method | `<method>_preserves_inv` |
| `InvariantSafety` | safety property (user-specified or inferred) | `inv_implies_safe` |
| `StorageConsistency` | storage.put followed by storage.get | key equality theorem |
| `AlarmScheduled` | setAlarm in method, alarm() handler exists | alarm fires eventually |

**Files changed:** `src/verification/veil-gen.ts` (new, ~400 lines), `src/verification/index.ts`, `src/cli.ts`

**Estimated effort:** Phase 5 total ~600 lines across 4 files

---

## Phase 6: Examples

Five complete examples demonstrating the full pipeline, each with:
- TypeScript source
- Expected Lean output
- Veil stub (for DO examples)
- Test coverage

### 6A. Workers Entry Point (no DO)

```typescript
// examples/worker-basic.ts
export interface Env {
  MY_KV: KVNamespace;
}

export default {
  async fetch(request: Request, env: Env, ctx: ExecutionContext): Promise<Response> {
    const url = new URL(request.url);
    if (url.pathname === "/get") {
      const value = await env.MY_KV.get("key");
      return new Response(value ?? "not found");
    }
    return new Response("Hello Workers!", { status: 200 });
  }
};
```

### 6B. Counter DO (storage + alarm)

```typescript
// examples/counter-do.ts
import { DurableObject } from "cloudflare:workers";

export class Counter extends DurableObject<Env> {
  private count: number = 0;

  constructor(ctx: DurableObjectState, env: Env) {
    super(ctx, env);
    ctx.blockConcurrencyWhile(async () => {
      this.count = (await ctx.storage.get<number>("count")) ?? 0;
    });
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
    switch (url.pathname) {
      case "/increment": return Response.json({ count: await this.increment() });
      case "/decrement": return Response.json({ count: await this.decrement() });
      default: return Response.json({ count: this.count });
    }
  }
}
```

### 6C. Chat Room (WebSocket Hibernation)

```typescript
// examples/chat-room-do.ts
import { DurableObject } from "cloudflare:workers";

export class ChatRoom extends DurableObject<Env> {
  async fetch(request: Request): Promise<Response> {
    const [client, server] = Object.values(new WebSocketPair());
    const url = new URL(request.url);
    const room = url.searchParams.get("room") ?? "default";
    this.ctx.acceptWebSocket(server, [room]);
    return new Response(null, { status: 101, webSocket: client });
  }

  async webSocketMessage(ws: WebSocket, message: string | ArrayBuffer): Promise<void> {
    const tags = this.ctx.getTags(ws);
    if (tags.length > 0) {
      const peers = this.ctx.getWebSockets(tags[0]);
      for (const peer of peers) {
        if (peer !== ws) peer.send(typeof message === "string" ? message : "binary");
      }
    }
  }

  async webSocketClose(ws: WebSocket, code: number, reason: string, wasClean: boolean): Promise<void> {
    ws.close(code, reason);
  }
}
```

### 6D. Rate Limiter (alarm-based window expiry)

```typescript
// examples/rate-limiter-do.ts
import { DurableObject } from "cloudflare:workers";

export class RateLimiter extends DurableObject<Env> {
  async fetch(request: Request): Promise<Response> {
    const now = Date.now();
    const windowMs = 60000;
    const maxRequests = 100;

    const events: number[] = (await this.ctx.storage.get<number[]>("events")) ?? [];
    const recent = events.filter(t => now - t < windowMs);

    if (recent.length >= maxRequests) {
      return new Response("Rate limited", { status: 429 });
    }

    recent.push(now);
    await this.ctx.storage.put("events", recent);

    if (!await this.ctx.storage.getAlarm()) {
      await this.ctx.storage.setAlarm(now + windowMs);
    }

    return new Response("OK");
  }

  async alarm(): Promise<void> {
    const now = Date.now();
    const events: number[] = (await this.ctx.storage.get<number[]>("events")) ?? [];
    const recent = events.filter(t => now - t < 60000);
    await this.ctx.storage.put("events", recent);
  }
}
```

### 6E. Multi-DO RPC

```typescript
// examples/multi-do-rpc.ts
import { DurableObject } from "cloudflare:workers";

export class OrderService extends DurableObject<Env> {
  async createOrder(userId: string, items: string[]): Promise<string> {
    const orderId = crypto.randomUUID();
    await this.ctx.storage.put(orderId, { userId, items, status: "pending" });

    // RPC to inventory service
    const inventoryId = this.env.INVENTORY.idFromName("global");
    const inventory = this.env.INVENTORY.get(inventoryId);
    await inventory.reserveItems(items);

    return orderId;
  }
}

export class InventoryService extends DurableObject<Env> {
  async reserveItems(items: string[]): Promise<void> {
    for (const item of items) {
      const stock: number = (await this.ctx.storage.get(item)) ?? 0;
      if (stock <= 0) throw new Error(`Out of stock: ${item}`);
      await this.ctx.storage.put(item, stock - 1);
    }
  }
}
```

**Files:** 5 TypeScript sources in `examples/`, corresponding tests in `tests/e2e/do-examples.test.ts`, fixture-style.

**Estimated effort:** Phase 6 total ~500 lines (examples + tests)

---

## Phase 7: Documentation

### 7A. `docs/durable-objects.md`

Comprehensive guide (~300 lines):

1. **Overview** — what TSLean does with DO code, the DO → Lean mapping model
2. **Supported patterns** — class detection, state extraction, storage ops, WS hibernation, alarms, RPC, blockConcurrencyWhile
3. **Type mapping table** — every DO/Workers type and its Lean equivalent
4. **Storage operations** — side-by-side TS → Lean for every storage method
5. **WebSocket Hibernation** — acceptWebSocket, getWebSockets, tags, WS handlers
6. **Alarm API** — setAlarm/getAlarm/deleteAlarm, alarm() handler
7. **Worker entry point** — export default, Env bindings
8. **Veil bridge** — how to use `--veil`, what gets generated, how to fill in proofs
9. **Examples** — links to the 5 example files with expected output
10. **Limitations** — what's not supported (SQL storage is axiomatized, RPC is structural only, etc.)

### 7B. Update existing docs

- `docs/architecture.md` — add DO pipeline section
- `docs/type-mapping.md` — add Workers/DO types section
- `docs/stdlib-reference.md` — add storage method table
- `docs/limitations.md` — update DO-specific limitations
- `docs/contributing.md` — add "how to add a DO pattern" section

**Estimated effort:** Phase 7 total ~500 lines across 6 files

---

## Execution Order and Dependencies

```
Phase 1A (ambient.ts)
    ↓
Phase 1B (Lean stubs) ──── can run in parallel with 1C, 1D
Phase 1C (typemap + lower imports)
Phase 1D (export default)
    ↓
Phase 2A (storage lowering) ←── depends on 1A, 1B, 1C
Phase 2B (SQL stubs)
Phase 2C (blockConcurrencyWhile) ←── depends on 2A
Phase 2D (namespace + RPC) ←── depends on 1C
    ↓
Phase 3 (WebSocket) ←── depends on 2A
Phase 4 (Alarms) ←── depends on 2A
    ↓
Phase 5 (Veil bridge) ←── depends on 2A, 3, 4
    ↓
Phase 6 (Examples) ←── depends on all above
Phase 7 (Docs) ←── depends on all above
```

## Estimated Totals

| Phase | New Lines | Files Changed | Files Created |
|-------|-----------|---------------|---------------|
| 1. Workers stubs | ~800 | 4 | 5 Lean files |
| 2. Storage lowering | ~1200 | 6 | 1 Lean file |
| 3. WebSocket | ~600 | 5 | 0 |
| 4. Alarms | ~300 | 3 | 0 |
| 5. Veil bridge | ~600 | 4 | 1 TS file |
| 6. Examples | ~500 | 2 | 5 TS + 1 test |
| 7. Docs | ~500 | 6 | 1 new doc |
| **Total** | **~4500** | **~20** | **~14** |

## Key Design Decisions

### D1: DOState wrapper vs. flat state struct

**Decision: Use `DOState σ` wrapper from Model.lean.**

Rationale: The existing Lean library is built around `DOState σ = { appState : σ, storage : Storage }`. Using it directly means all 5,018 lines of existing DO theorems apply without adaptation. The transpiler synthesizes `σ` (the user's state fields) and wraps it.

### D2: Storage as pure model vs. IO axioms

**Decision: Pure model (AssocMap) with `DOMonad` for state threading.**

Rationale: This is what the Lean library already does. Storage is `AssocMap StorageKey StorageValue`. Mutations go through `modify` in `DOMonad`. This enables verification (you can reason about storage algebraically) at the cost of not modeling actual KV latency/failure. For verification purposes, the pure model is strictly better.

### D3: Veil stubs: `sorry` vs. inferred predicates

**Decision: Generate `sorry` stubs with best-effort inference for simple cases.**

Rationale: Fully inferring invariants from imperative code is undecidable in general. But for common patterns (bounded counter, CRUD storage), the method body analysis can fill in relational predicates. The user always has the option to refine. This is the same approach as the existing `--verify` flag.

### D4: WebSocket session types

**Decision: Do NOT generate session types from transpiled code.**

Rationale: The `Session` inductive in WebSocket.lean (send/recv/choice/offer with duality) is a protocol-level specification that cannot be inferred from imperative WS handler code. The transpiler maps WS operations to `WsDoState` operations (connection tracking, broadcast). Session type verification is left as a manual Veil exercise.

### D5: RPC serialization

**Decision: Use the existing `Serializer` typeclass with `sorry`-proofed roundtrip axioms for user types.**

Rationale: The `Serializer` typeclass in RPC.lean requires a `roundtrip` proof. For auto-generated stubs, emit `instance : Serializer MyType where serialize := sorry; deserialize := sorry; roundtrip := sorry`. Users who want verified serialization can fill these in.

### D6: `export default` detection strategy

**Decision: Pattern-match on `ExportAssignment` with object literal containing `fetch` method.**

Rationale: This is the canonical Workers module format. We don't need to handle all possible export patterns — just the standard one. Class-based workers (`export class MyWorker extends WorkerEntrypoint`) can be handled as a follow-up.
