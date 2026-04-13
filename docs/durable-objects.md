# Durable Objects & Cloudflare Workers Support

TSLean has first-class support for Cloudflare Workers and Durable Objects. The transpiler detects DO patterns, injects ambient type declarations, maps storage/WS/alarm operations to the Lean runtime library, and can auto-generate Veil transition system stubs for formal verification.

## Overview

When TSLean detects a DO class (`extends DurableObject` or `DurableObjectState` constructor param), it:

1. **Injects ambient types** — `CF_AMBIENT` provides ~40 Workers types so the TypeScript checker resolves them without `@cloudflare/workers-types`.
2. **Extracts state** — class fields become a `<ClassName>State` Lean `structure`. Fields typed `DurableObjectState` and `Env` are filtered out.
3. **Namespaces methods** — DO methods are wrapped in a `namespace <ClassName>` block with `self` as the first parameter.
4. **Maps storage ops** — `this.ctx.storage.get/put/delete` calls map to `DurableObjects.Model.Storage.*` pure operations.
5. **Maps WS ops** — `acceptWebSocket`, `getWebSockets`, `getTags` map to `DurableObjects.WebSocket.WsDoState.*`.
6. **Maps alarm ops** — `getAlarm/setAlarm/deleteAlarm` map to `DurableObjects.Alarm.AlarmState.*`.
7. **Adds DO imports** — `TSLean.DurableObjects.*`, `TSLean.Runtime.Monad` imports are automatically added.

## Workers Entry Point

The standard Workers module pattern:

```typescript
export default {
  async fetch(request: Request, env: Env, ctx: ExecutionContext): Promise<Response> {
    return new Response("Hello Workers!");
  }
};
```

Transpiles to:

```lean
namespace Worker

def fetch (request : Request) (env : Env) (ctx : ExecutionContext) : IO Response :=
  pure (mkResponse "Hello Workers!")

end Worker
```

## Storage Operations

| TypeScript | Lean Output |
|-----------|-------------|
| `this.ctx.storage.get("key")` | `Storage.get self.storage "key"` |
| `this.ctx.storage.put("key", val)` | `modify fun s => { s with storage := Storage.put s.storage "key" val }` |
| `this.ctx.storage.delete("key")` | `modify fun s => { s with storage := Storage.delete s.storage "key" }` |
| `this.ctx.storage.deleteAll()` | `modify fun s => { s with storage := Storage.clear }` |
| `this.ctx.storage.list()` | `Storage.keys self.storage` |
| `this.ctx.storage.getAlarm()` | `AlarmState.next self.alarms` |
| `this.ctx.storage.setAlarm(t)` | `modify fun s => { s with alarms := AlarmState.schedule s.alarms t 0 }` |
| `this.ctx.storage.deleteAlarm()` | `modify fun s => { s with alarms := AlarmState.empty }` |
| `this.ctx.storage.transaction(fn)` | `Transaction.commit (fn Transaction.empty) self.storage` |

Storage is modeled as `AssocMap StorageKey StorageValue` from `DurableObjects.Model`. Mutations use `modify` in the `DOMonad` (= `StateT σ (ExceptT TSError IO)`).

## WebSocket Hibernation

| TypeScript | Lean Output |
|-----------|-------------|
| `new WebSocketPair()` | `WebSocketPair.new` |
| `this.ctx.acceptWebSocket(ws, tags)` | `WsDoState.openConn ws tags` |
| `this.ctx.getWebSockets(tag)` | `WsDoState.getByTag tag` |
| `this.ctx.getTags(ws)` | `WsDoState.getTags ws` |
| `ws.send(message)` | `WsDoState.broadcast ...` |
| `ws.close(code, reason)` | `WsDoState.closeConn ...` |

WS handler methods (`webSocketMessage`, `webSocketClose`, `webSocketError`) are recognized and transpiled as DO namespace methods.

## Alarm API

The alarm handler:

```typescript
async alarm(alarmInfo?: AlarmInvocationInfo): Promise<void> {
  // Process alarm
}
```

Transpiles to a method in the DO namespace. `AlarmInvocationInfo` carries `retryCount: Nat` and `isRetry: Bool`.

## blockConcurrencyWhile

```typescript
constructor(ctx: DurableObjectState, env: Env) {
  super(ctx, env);
  ctx.blockConcurrencyWhile(async () => {
    this.count = (await ctx.storage.get("count")) ?? 0;
  });
}
```

The callback is executed as part of initialization — semantically, `blockConcurrencyWhile` ensures the callback runs before any concurrent requests. In the Lean model, the callback is directly invoked.

## Workers Bindings (KV, R2, D1, Queue)

TSLean provides Lean stubs for all major Workers bindings:

| Binding | Lean Module | Model |
|---------|------------|-------|
| `KVNamespace` | `TSLean.Workers.KV` | Opaque + axiomatized `get/put/delete/list` |
| `R2Bucket` | `TSLean.Workers.R2` | Opaque + axiomatized `get/put/delete/list/head` |
| `D1Database` | `TSLean.Workers.D1` | Opaque + axiomatized `prepare/exec/batch/dump` |
| `Queue` | `TSLean.Workers.Queue` | Opaque + axiomatized `send/sendBatch` |
| `ScheduledEvent` | `TSLean.Workers.Scheduler` | Structure with `scheduledTime/cron` |
| `AlarmInvocationInfo` | `TSLean.Workers.Scheduler` | Structure with `retryCount/isRetry` |

These are axiomatized (no implementation) — they exist so transpiled code type-checks in Lean.

## Veil Bridge: Formal Verification

Use `--veil` to auto-generate Veil transition system stubs:

```bash
tslean counter.ts -o counter.lean --veil
```

This produces two files:
- `counter.lean` — the normal transpilation
- `counter_veil.lean` — a Veil transition system stub

The stub contains:

```lean
-- Auto-generated Veil transition system for Counter

import TSLean.Veil.DSL
import TSLean.Veil.Core

namespace Counter.Veil

abbrev State := CounterState

def initState (s : State) : Prop :=
  s.count = 0  -- extracted from constructor

veil_relation action_increment (pre post : State) where
  sorry -- TODO: specify pre/post for increment

veil_relation action_decrement (pre post : State) where
  sorry -- TODO: specify pre/post for decrement

def next_ := next4 action_increment action_decrement action_getCount action_fetch

veil_safety safe (s : State) where
  sorry -- TODO: specify safety property

instance : TransitionSystem State where
  init := initState
  assumptions := assumptions
  next := next_
  safe := safe
  inv := inv

-- Proof obligations
theorem inv_implies_safe : invSafe (σ := State) := sorry
theorem init_establishes_inv : invInit (σ := State) := sorry
theorem increment_preserves_inv ... := sorry
theorem inv_consecution : invConsecution (σ := State) := sorry
theorem safety_holds : isInvariant (σ := State) safe := sorry

end Counter.Veil
```

Fill in the `sorry` placeholders to complete verification. See the hand-written examples in `lean/TSLean/Veil/` for reference patterns.

## Lean Library Architecture

The DO runtime library (5,018 lines) is organized as:

```
lean/TSLean/
├── DurableObjects/          Operational models
│   ├── Model.lean             Storage = AssocMap StorageKey StorageValue
│   ├── State.lean             DurableObjectState wrapper
│   ├── Storage.lean           Batch get/put/delete
│   ├── Http.lean              HttpRequest/HttpResponse
│   ├── WebSocket.lean         Session types, WsDoState
│   ├── RPC.lean               Serializer typeclass, RPCHandler
│   ├── Transaction.lean       Transaction (commit/rollback)
│   ├── Alarm.lean             AlarmState (schedule/cancel/tick)
│   ├── Hibernation.lean       Snapshot take/restore
│   └── ...                    Auth, ChatRoom, Queue, etc.
├── Veil/                    Transition system verification
│   ├── Core.lean              TransitionSystem typeclass + reachability
│   ├── DSL.lean               veil_action/veil_relation/veil_safety macros
│   ├── CounterDO.lean         Verified counter (48 theorems)
│   ├── ChatRoomDO.lean        Verified chat room
│   ├── AuthDO.lean            Verified auth sessions
│   ├── QueueDO.lean           Verified bounded queue
│   ├── RateLimiterDO.lean     Verified rate limiter
│   └── SessionStoreDO.lean    Verified session store
├── Workers/                 Workers binding stubs
│   ├── KV.lean                KVNamespace (axiomatized)
│   ├── R2.lean                R2Bucket/R2Object (axiomatized)
│   ├── D1.lean                D1Database (axiomatized)
│   ├── Queue.lean             QueueSender/MessageBatch (axiomatized)
│   └── Scheduler.lean         ScheduledEvent, AlarmInvocationInfo
└── Runtime/
    ├── Monad.lean             DOMonad = StateT σ (ExceptT TSError IO)
    └── WebAPI.lean            Request/Response/Headers/URL
```

## Limitations

- **SQL Storage** (`this.ctx.storage.sql.exec(...)`) is not yet mapped — emits `sorry`.
- **RPC method dispatch** (`stub.myMethod()`) is recognized structurally but not fully verified — the RPC serialization uses `Serializer` with `sorry`-proofed roundtrip axioms.
- **Hibernation state loss** — the Lean model uses `Snapshot.take/restore` which preserves all state, but real hibernation discards in-memory state. This semantic gap is documented but not modeled.
- **WebSocket session types** — the `Session` inductive (send/recv/choice/offer) in WebSocket.lean cannot be inferred from imperative handler code. Session type verification is manual.
- **Dynamic RPC dispatch** — `stub[methodName]()` where the method name is a runtime value is not supported.
