> Edited & maintained by Claude; presented as-is.

# TypeScript-to-Lean Durable Object Support

The secondary TypeScript-to-Lean compiler detects supported Durable Object patterns,
injects typed ambient declarations, and maps admitted storage, WebSocket, alarm, and
binding operations to the Lean runtime model.

## Overview

When TSLean detects a DO class (`extends DurableObject` or `DurableObjectState` constructor param), it:

1. **Injects ambient types**: `CF_AMBIENT` provides ~40 Workers types so the TypeScript checker resolves them without `@cloudflare/workers-types`.
2. **Extracts state**: class fields become a `<ClassName>State` Lean `structure`. Fields typed `DurableObjectState` and `Env` are filtered out.
3. **Namespaces methods**: DO methods are wrapped in a `namespace <ClassName>` block with `self` as the first parameter.
4. **Maps storage ops**: `this.ctx.storage.get/put/delete` calls map to `DurableObjects.Model.Storage.*` pure operations.
5. **Maps WS ops**: `acceptWebSocket`, `getWebSockets`, `getTags` map to `DurableObjects.WebSocket.WsDoState.*`.
6. **Maps alarm ops**: `getAlarm/setAlarm/deleteAlarm` map to `DurableObjects.Alarm.AlarmState.*`.
7. **Adds DO imports**: `TSLean.DurableObjects.*`, `TSLean.Runtime.Monad` imports are automatically added.

## Workers Entry Point

The standard Workers module pattern:

```typescript
export default {
  async fetch(request: Request, env: Env, ctx: ExecutionContext): Promise<Response> {
    return new Response('Hello Workers!');
  },
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

| TypeScript                         | Lean Output                                                             |
| ---------------------------------- | ----------------------------------------------------------------------- |
| `this.ctx.storage.get("key")`      | `Storage.get self.storage "key"`                                        |
| `this.ctx.storage.put("key", val)` | `modify fun s => { s with storage := Storage.put s.storage "key" val }` |
| `this.ctx.storage.delete("key")`   | `modify fun s => { s with storage := Storage.delete s.storage "key" }`  |
| `this.ctx.storage.deleteAll()`     | `modify fun s => { s with storage := Storage.clear }`                   |
| `this.ctx.storage.list()`          | `Storage.keys self.storage`                                             |
| `this.ctx.storage.getAlarm()`      | `AlarmState.next self.alarms`                                           |
| `this.ctx.storage.setAlarm(t)`     | `modify fun s => { s with alarms := AlarmState.schedule s.alarms t 0 }` |
| `this.ctx.storage.deleteAlarm()`   | `modify fun s => { s with alarms := AlarmState.empty }`                 |
| `this.ctx.storage.transaction(fn)` | `Transaction.commit (fn Transaction.empty) self.storage`                |

Storage is modeled as `AssocMap StorageKey StorageValue` from `DurableObjects.Model`. Mutations use `modify` in the `DOMonad` (= `StateT σ (ExceptT TSError IO)`).

## WebSocket Hibernation

| TypeScript                           | Lean Output                  |
| ------------------------------------ | ---------------------------- |
| `new WebSocketPair()`                | `WebSocketPair.new`          |
| `this.ctx.acceptWebSocket(ws, tags)` | `WsDoState.openConn ws tags` |
| `this.ctx.getWebSockets(tag)`        | `WsDoState.getByTag tag`     |
| `this.ctx.getTags(ws)`               | `WsDoState.getTags ws`       |
| `ws.send(message)`                   | `WsDoState.broadcast ...`    |
| `ws.close(code, reason)`             | `WsDoState.closeConn ...`    |

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

The callback is executed as part of initialization: semantically, `blockConcurrencyWhile` ensures the callback runs before any concurrent requests. In the Lean model, the callback is directly invoked.

## Workers Bindings (KV, R2, D1, Queue)

TSLean provides Lean stubs for all major Workers bindings:

| Binding               | Lean Module                | Model                               |
| --------------------- | -------------------------- | ----------------------------------- |
| `KVNamespace`         | `TSLean.Workers.KV`        | Abstract KV capability contract     |
| `R2Bucket`            | `TSLean.Workers.R2`        | Abstract R2 capability contract     |
| `D1Database`          | `TSLean.Workers.D1`        | Abstract D1 capability contract     |
| `Queue`               | `TSLean.Workers.Queue`     | Abstract queue capability contract  |
| `ScheduledEvent`      | `TSLean.Workers.Scheduler` | Structure with `scheduledTime/cron` |
| `AlarmInvocationInfo` | `TSLean.Workers.Scheduler` | Structure with `retryCount/isRetry` |

These are abstract external capability contracts. They do not prove provider behavior.

## Transition-system proofs

The Lean modules under `lean/TSLean/Veil/` contain hand-authored transition-system models
and proofs. The CLI does not generate proofs or placeholder theorem declarations. A
Durable Object proof must use the modeled behavior and pass the Lean and axiom gates.

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
├── Workers/                 Workers capability models
│   ├── KV.lean                Abstract KV capability model
│   ├── R2.lean                Abstract R2 capability model
│   ├── D1.lean                Abstract D1 capability model
│   ├── Queue.lean             Abstract queue capability model
│   └── Scheduler.lean         ScheduledEvent, AlarmInvocationInfo
└── Runtime/
    ├── Monad.lean             DOMonad = StateT σ (ExceptT TSError IO)
    └── WebAPI.lean            Request/Response/Headers/URL
```

## Limitations

- **SQL storage** (`this.ctx.storage.sql.exec(...)`) is outside the current lowering; `--strict` refuses degraded output.
- **RPC dispatch** has no concrete serialization refinement proof. The current Lean module is an abstract model.
- **Hibernation** is not proved to refine Cloudflare's eviction and restore behavior.
- **WebSocket session types** are hand-authored. The compiler does not infer them from imperative handlers.
- **Dynamic RPC dispatch** through a runtime method name is unsupported.
