> Edited & maintained by Claude; presented as-is.

# 12: Durable Objects

Four Durable Object examples covering the full DO API surface: storage persistence, WebSocket Hibernation, alarm scheduling, and multi-DO RPC.

## Run

```bash
# Compile one Durable Object
bun run src/cli.ts ts-to-lean examples/12-durable-objects/counter-do.ts --output output/counter.lean --strict

# Compile all four
for file in examples/12-durable-objects/*.ts; do
  bun run src/cli.ts ts-to-lean "$file" --output "output/$(basename "$file" .ts).lean" --strict
done
```

## Examples

### `counter-do.ts`: Storage Get/Put

The simplest DO: a counter that persists via `this.ctx.storage.put/get`.

| TypeScript                            | Lean                                              |
| ------------------------------------- | ------------------------------------------------- |
| `class Counter extends DurableObject` | `structure CounterState` + `namespace Counter`    |
| `this.count++`                        | `modify fun s => { s with count := s.count + 1 }` |
| `this.ctx.storage.put("count", v)`    | `Storage.put "count" v` (via modify in DOMonad)   |
| `this.ctx.storage.get("count")`       | `Storage.get "count"`                             |

### `chat-room-ws.ts`: WebSocket Hibernation

Full WebSocket Hibernation lifecycle with tag-based room routing.

| TypeScript                                 | Lean                                                       |
| ------------------------------------------ | ---------------------------------------------------------- |
| `new WebSocketPair()`                      | `WebSocketPair.new`                                        |
| `this.ctx.acceptWebSocket(ws, [room])`     | `openConnWithTags state ws [room]`                         |
| `this.ctx.getWebSockets(tag)`              | `getByTag state tag`                                       |
| `this.ctx.getTags(ws)`                     | `getTags state ws`                                         |
| `webSocketMessage(ws, msg)` handler        | `def webSocketMessage (self) (ws) (msg) : IO Unit`         |
| `webSocketClose(ws, code, reason)` handler | `def webSocketClose (self) (ws) (code) (reason) : IO Unit` |

### `rate-limiter-alarm.ts`: Alarm API

Sliding-window rate limiter using alarms for deferred cleanup.

| TypeScript                        | Lean                         |
| --------------------------------- | ---------------------------- |
| `this.ctx.storage.getAlarm()`     | `AlarmState.next`            |
| `this.ctx.storage.setAlarm(time)` | `AlarmState.schedule`        |
| `async alarm() { ... }` handler   | `def alarm : DOMonad σ Unit` |

### `multi-do-rpc.ts`: Multi-DO Communication

Multiple DO classes with cross-DO RPC calls.

| TypeScript                   | Lean                                                              |
| ---------------------------- | ----------------------------------------------------------------- |
| `crypto.randomUUID()`        | Unsupported runtime operation; `--strict` refuses degraded output |
| `JSON.stringify(x)`          | `serialize x`                                                     |
| `env.MY_DO.idFromName(name)` | `DurableObjectId.fromName name`                                   |
| `stub.myMethod(args)`        | RPC via `Serializer` typeclass                                    |

## Formal transition models

The CLI does not generate proofs or placeholder theorem declarations. Hand-authored Lean
models and proofs are available for the supported examples:

- `lean/TSLean/Veil/CounterDO.lean`
- `lean/TSLean/Veil/ChatRoomDO.lean`
- `lean/TSLean/Veil/RateLimiterDO.lean`

These proofs apply to their stated Lean models. They are not automatic proofs of arbitrary
TypeScript Durable Object source.

## Lean Runtime Library

The hand-written Lean DO models (5,018 lines) in `lean/TSLean/DurableObjects/` and `lean/TSLean/Veil/` provide the formal foundations:

| Module                       | What it models                                                         |
| ---------------------------- | ---------------------------------------------------------------------- |
| `DurableObjects.Model`       | `Storage = AssocMap StorageKey StorageValue` with 15 proved properties |
| `DurableObjects.WebSocket`   | Session types (dual involutive), WsDoState connection tracking         |
| `DurableObjects.Alarm`       | AlarmState (pending/fired), schedule/cancel/tick with 12 theorems      |
| `DurableObjects.Transaction` | Commit/rollback with atomicity proofs                                  |
| `DurableObjects.RPC`         | Serializer typeclass with roundtrip proofs                             |
| `Veil.Core`                  | TransitionSystem typeclass, reachability, induction                    |
| `Veil.DSL`                   | `veil_action`, `veil_relation`, `veil_safety` macros                   |
