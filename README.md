<div align="center">

# TSLean

### TypeScript → Lean 4 Transpiler with Formal Verification

**Transpile real-world TypeScript into verified Lean 4 code — with automated proofs for Cloudflare Durable Objects.**

[![Tests](https://img.shields.io/badge/tests-1051_passing-brightgreen)](#tests)
[![Theorems](https://img.shields.io/badge/theorems-933_proved-blue)](#lean-4-runtime--verification-library)
[![Lean](https://img.shields.io/badge/Lean_4-v4.29.0-orange)](#requirements)
[![Build](https://img.shields.io/badge/lake_build-50%2F50_passing-brightgreen)](#building)
[![License](https://img.shields.io/badge/license-MIT-lightgrey)](#license)

</div>

---

## What is this?

TSLean is a research-grade transpiler that converts properly-typed TypeScript into compilable, verifiable **Lean 4** code. It ships with:

- **A complete transpiler pipeline** — Parser (TS Compiler API) → IR (System Fω + effects) → Type Mapper → Effect Analyzer → Rewrite Pass → Lean 4 Codegen
- **A 6,800+ line Lean 4 verification library** — 933 theorems proving safety properties of Cloudflare Durable Objects (rate limiters, auth sessions, chat rooms, queues, analytics, transactions)
- **Veil-style transition system verification** — 7 DO models formalized as state machines with invariant induction proofs
- **Multi-file project transpilation** — Resolves TypeScript import graphs and generates cross-file Lean module imports
- **1,051 tests** across 27 test files with 0 failures

### Why?

Cloudflare Durable Objects are stateful, single-threaded actors that power real-time systems at scale. But their correctness properties — rate limits are never exceeded, auth tokens can't be used after revocation, message ordering is preserved across broadcasts — are currently validated only by testing.

TSLean makes these properties **mathematically provable**. Write your DO in TypeScript, transpile to Lean 4, and get machine-checked proofs that your system is correct.

---

## Quick Start

```bash
# Install dependencies
npm install

# Transpile a single file
npx tsx src/cli.ts examples/counter.ts -o output.lean

# Transpile a multi-file project
npx tsx src/cli.ts --project my-workers-app/ -o lean/Generated/

# Run tests
npx vitest run

# Build & verify the Lean library (requires Lean 4)
cd lean && lake build
```

---

## Architecture

```
┌─────────────┐     ┌──────────┐     ┌───────────┐     ┌──────────┐     ┌─────────┐     ┌──────────┐
│  TypeScript  │────▶│  Parser  │────▶│  IR (Fω)  │────▶│  Rewrite │────▶│ Codegen │────▶│  Lean 4  │
│   Source     │     │ (TS API) │     │ + Effects │     │   Pass   │     │         │     │  Output  │
└─────────────┘     └──────────┘     └───────────┘     └──────────┘     └─────────┘     └──────────┘
                          │                │                  │                │
                     Type Checker     Effect Inference   Pattern Rewrite  Import Resolution
                     DO Ambient       Monad Stack        Union → Match    TSLean.* mapping
```

### Pipeline Components

| Component | File | Lines | What it does |
|-----------|------|-------|-------------|
| **IR** | `src/ir/types.ts` | 238 | System Fω with algebraic effects — 30+ type variants, 35+ expression variants |
| **Parser** | `src/parser/index.ts` | 1,263 | TypeScript Compiler API (`ts.createProgram` + `TypeChecker`), not Babel |
| **Type Mapper** | `src/typemap/index.ts` | 194 | Interfaces → structures, unions → inductives, branded types → newtypes |
| **Effect System** | `src/effects/index.ts` | 110 | Mutations → `StateT`, async → `TaskM`, throw → `ExceptT`, combined → transformer stacks |
| **Rewrite Pass** | `src/rewrite/index.ts` | 170 | String-discriminant matches → inductive pattern matching |
| **Codegen** | `src/codegen/index.ts` | 686 | Lean 4 emitter: namespaces, do-notation, match, type classes, `s!"..."` interpolation |
| **Verification** | `src/verification/index.ts` | 115 | Proof obligation generation: array bounds, division safety, null checks |
| **Project Mode** | `src/project/index.ts` | 112 | Multi-file transpilation with import graph resolution |
| **CLI** | `src/cli.ts` | 55 | Single file + `--project` directory + `--verify` flag |

### Type Translations

| TypeScript | Lean 4 |
|-----------|--------|
| `interface Point { x: number; y: number }` | `structure Point where x : Float; y : Float` |
| `type Shape = { kind: "circle"; r: number } \| { kind: "rect"; w: number; h: number }` | `inductive Shape where \| circle (r : Float) \| rect (w : Float) (h : Float)` |
| `type UserId = string & { __brand: "UserId" }` | `structure UserId where val : String deriving BEq, DecidableEq` |
| `Promise<T>` | `TaskM T` |
| `T \| undefined` | `Option T` |
| `{ [key: string]: number }` | `AssocMap String Float` |
| `async function f()` | `def f : TaskM Unit := do ...` |
| `x?.prop` | `x.bind (fun v => v.prop)` |
| `a ?? b` | `a.getD b` |
| `{ ...obj, name: v }` | `{ obj with name := v }` |

### Effect Mapping

| TypeScript Pattern | Lean 4 Monad |
|-------------------|-------------|
| Pure functions | Direct functions (no monad) |
| Mutations (`this.state = ...`) | `StateT σ` |
| `async/await` | `TaskM` (IO-based) |
| `throw/try/catch` | `ExceptT TSError` |
| Durable Object methods | `DOMonad σ α = StateT σ (ExceptT TSError IO)` |
| Combined effects | Monad transformer stacks |

---

## Lean 4 Runtime & Verification Library

The `lean/` directory contains a **6,800+ line, 933-theorem** verification library with zero external dependencies (pure Lean 4.29 core).

### Module Structure

```
lean/TSLean/
├── Runtime/              # Core runtime types and monads
│   ├── Basic.lean        # TSValue, TSError, Result, Option utilities
│   ├── Monad.lean        # TaskM, DOMonad = StateT σ (ExceptT TSError IO)
│   ├── Coercions.lean    # Float↔Nat↔Int, String ops, type coercions
│   ├── BrandedTypes.lean # UserId, RoomId, MessageId, SessionToken (verified)
│   └── Validation.lean   # validLength, nonEmpty, containsChar (with proofs)
│
├── Stdlib/               # Verified standard library
│   ├── HashMap.lean      # AssocMap with Nodup + 15 lookup/insert theorems
│   ├── HashSet.lean      # Based on AssocMap, membership proofs
│   ├── Array.lean        # Bounds-checked access, map/filter theorems
│   ├── String.lean       # Length, substring, validated operations
│   ├── Numeric.lean      # Nat/Int/Float arithmetic properties
│   └── OptionResult.lean # Option/Result composition theorems
│
├── Effects/              # Algebraic effect formalization
│   ├── Core.lean         # EffectKind inductive, EffectSet lattice, subsumption
│   └── Transformer.lean  # Monad transformer laws and composition
│
├── DurableObjects/       # 16 DO model files — the core research contribution
│   ├── Model.lean        # StorageValue, DOState, DOAction, state machine model
│   ├── Transaction.lean  # ACID semantics: atomicity, read-own-write, rollback
│   ├── WebSocket.lean    # Session-typed channels, dual_involutive
│   ├── Alarm.lean        # Timed event calculus, monotonicity
│   ├── RPC.lean          # Serializer typeclass with roundtrip proofs
│   ├── Hibernation.lean  # Snapshot/restore correctness
│   ├── RateLimiter.lean  # Sliding window: never_exceeds_limit, monotonic cleanup
│   ├── ChatRoom.lean     # Message ordering, broadcast delivery guarantees
│   ├── SessionStore.lean # TTL expiry, no_stale_reads, set-then-get
│   ├── Queue.lean        # Durable queue: FIFO ordering, at-least-once delivery
│   ├── Auth.lean         # Session auth: expired_rejected, logout_invalidates
│   ├── Analytics.lean    # Event aggregation: no_events_lost, counts_monotonic
│   ├── MultiDO.lean      # Inter-DO RPC: roundtrip, no_message_duplication
│   ├── Http.lean         # HttpRequest/Response, status predicates
│   ├── State.lean        # DurableObjectState wrapping Storage
│   └── Storage.lean      # Storage API: get/put/delete with batch operations
│
├── Veil/                 # Transition system verification (inspired by verse-lab/veil)
│   ├── Core.lean         # TransitionSystem typeclass, reachability, invariant induction
│   ├── CounterDO.lean    # Bounded counter: count ∈ [min, max] always
│   ├── AuthDO.lean       # Session lifecycle: revoked tokens can never authenticate
│   ├── RateLimiterDO.lean# Sliding window transitions: rate never exceeds limit
│   ├── ChatRoomDO.lean   # Message ordering preserved through all transitions
│   ├── QueueDO.lean      # Durable queue: enqueue/dequeue/ack with ordering
│   └── SessionStoreDO.lean # TTL session management with expiry safety
│
├── Verification/         # Proof automation
│   ├── ProofObligation.lean  # Obligation types: bounds, division, null, invariant
│   ├── Invariants.lean       # DO-specific invariant patterns
│   └── Tactics.lean          # Custom tactics for DO proofs
│
└── Generated/            # Transpiler output (verified to compile)
    ├── Hello.lean        # Factorial, greet, distance
    ├── Interfaces.lean   # Point structure, optional fields
    ├── Classes.lean      # Generic Stack<T>, Counter
    ├── CounterDO.lean    # Full DO with state machine
    ├── RateLimiter.lean  # Sliding window DO
    ├── ChatRoom.lean     # WebSocket chat room
    ├── SessionStore.lean # TTL session management
    ├── QueueProcessor.lean # Durable queue processor
    └── FullProject/      # Multi-file transpilation output
        ├── Shared/
        │   ├── Types.lean      # User, Room, UserId, RoomId (branded)
        │   └── Validators.lean # Email, length, format validation
        └── Backend/
            ├── AuthDo.lean     # Session authentication DO
            ├── ChatRoomDo.lean # WebSocket chat room DO
            └── Router.lean     # Request routing
```

### Theorem Highlights

```lean
-- Rate limiter can never exceed its configured limit
theorem never_exceeds_limit (rl : RateLimiter) (now : Nat) :
    (cleanup rl now).window.length ≤ rl.maxRequests

-- Revoked auth tokens can never authenticate
theorem revoked_cannot_authenticate (st : AuthState) (tok : Token) (now : Nat)
    (s : Session) (hfind : st.find tok = some s) (hrev : s.status = .revoked) :
    authenticate st tok now = none

-- ACID transaction reads see own writes
theorem read_own_write (tx : Transaction) (k : String) (v : StorageValue) :
    (write tx k v).read k = some v

-- Serializer roundtrip preserves values
theorem rpc_roundtrip (s : Serializer α) (x : α) :
    s.deserialize (s.serialize x) = some x

-- Durable queue maintains FIFO ordering
theorem fifo_ordering (q : DurableQueue α) (a b : α)
    (h : q.enqueue a |>.enqueue b) :
    h.dequeue.fst = some a

-- Veil: Counter DO invariant is inductive
-- (holds at init, preserved by all transitions → holds for all reachable states)
theorem counter_inv_inductive : invInductive (σ := CounterState)
```

---

## Multi-File Project Transpilation

TSLean resolves TypeScript import graphs and generates proper Lean module imports:

```bash
npx tsx src/cli.ts --project my-workers-app/ -o lean/Generated/MyApp/
```

**Input** (TypeScript):
```typescript
// shared/types.ts
export type UserId = string & { __brand: 'UserId' };
export interface User { id: UserId; email: string; roles: string[] }

// backend/auth-do.ts
import { User, UserId } from '../shared/types';
export class AuthDO {
  async authenticate(token: string): Promise<User | null> { ... }
}
```

**Output** (Lean 4):
```lean
-- Generated/Shared/Types.lean
structure UserId where val : String deriving Repr, BEq, DecidableEq
structure User where id : UserId; email : String; roles : Array String

-- Generated/Backend/AuthDo.lean
import TSLean.Generated.Shared.Types
def authenticate (self : AuthDOState) (token : String) : DOMonad AuthDOState (Option User) := do ...
```

---

## Tests

```bash
npx vitest run
```

**1,051 tests** across 27 test files covering:

| Category | Tests | What's tested |
|----------|-------|--------------|
| Parser | ~180 | All TS syntax: functions, classes, enums, generics, async, destructuring, optional chaining |
| Codegen | ~200 | Lean output: structures, inductives, do-notation, match, namespaces, imports |
| Type Mapping | ~120 | Interfaces, unions, branded types, generics, mapped types, recursive types |
| Effects | ~80 | Effect inference, monad selection, transformer stacks |
| Durable Objects | ~150 | 8 DO patterns: counter, WebSocket, RPC, alarm, rate limiter, chat, session, queue |
| Rewrite Pass | ~60 | Discriminated union → inductive pattern matching |
| E2E / Integration | ~150 | CLI invocation, multi-file projects, pipeline correctness |
| Regression | ~50 | Bug fix lock-in: spread syntax, fall-through, interpolation, getters |
| Verification | ~60 | Proof obligation generation, invariant detection |

---

## Durable Object Patterns

TSLean handles 8 production DO patterns out of the box:

| Pattern | Fixture | What it demonstrates |
|---------|---------|---------------------|
| **Counter** | `counter.ts` | State mutation → `StateT`, increment/decrement/reset |
| **WebSocket Hibernation** | `websocket-hibernation.ts` | Session types, `acceptWebSocket`, hibernation lifecycle |
| **RPC** | `rpc-counter.ts` | Serializer typeclass, remote procedure calls |
| **Alarm Scheduler** | `alarm-scheduler.ts` | Timed events, `setAlarm`, monotonic scheduling |
| **Rate Limiter** | `rate-limiter.ts` | Sliding window, cleanup, configurable limits |
| **Chat Room** | `chat-room.ts` | WebSocket broadcast, message ordering, member management |
| **Session Store** | `session-store.ts` | TTL expiry, token management, authentication |
| **Queue Processor** | `queue-processor.ts` | Durable queue, at-least-once delivery, batch processing |

---

## Veil-Style Verification

Inspired by [Veil](https://github.com/verse-lab/veil) (NUS Verse Lab), TSLean models each DO as a **relational transition system** with:

- **State type** — the DO's persistent state
- **Init predicate** — valid initial states
- **Action relations** — state transitions (increment, authenticate, enqueue, ...)
- **Safety properties** — invariants that must hold for all reachable states
- **Invariant induction** — proof that init ∧ consecution → safety for all reachable states

```lean
-- Example: Counter DO as a transition system
instance : TransitionSystem CounterState where
  init s := s.count = 0 ∧ s.minCount ≤ 0 ∧ 0 ≤ s.maxCount
  next s s' := increment s s' ∨ decrement s s' ∨ reset s s'
  safe s := s.minCount ≤ s.count ∧ s.count ≤ s.maxCount
  inv s := s.minCount ≤ s.count ∧ s.count ≤ s.maxCount

-- This is proved automatically via invariant induction
theorem counter_safety : ∀ s, reachable s → safe s
```

---

## Building

### Requirements

- **Node.js** ≥ 18
- **TypeScript** ≥ 5.0
- **Lean 4** v4.29.0 (for building/verifying the Lean library)

### Install

```bash
git clone https://github.com/AshishKumar4/TSLean.git
cd TSLean
npm install
```

### Verify the Lean Library

```bash
cd lean
lake build    # 50/50 jobs, 933 theorems verified
```

---

## Project Stats

| Metric | Value |
|--------|-------|
| TypeScript source | 3,454 lines across 11 files |
| Lean 4 library | 6,841 lines across 55 files |
| Tests | 1,051 passing across 27 files |
| Proved theorems | 933 (207 Veil + 726 classical) |
| `lake build` | 50/50 jobs, 0 errors |
| Type class instances | 46 |
| Structures | 50 |
| Inductive types | 15 |
| DO model files | 16 |
| Veil transition systems | 7 |
| Git commits | 11 |

---

## Design Decisions

- **TypeScript Compiler API** (not Babel) — full type resolution, generic instantiation, type narrowing
- **System Fω IR** with algebraic effect annotations — every node carries resolved type + effect
- **`DOMonad σ α = StateT σ (ExceptT TSError IO)`** — canonical Durable Object monad stack
- **AssocMap over Std.HashMap** — Batteries has 0 correctness theorems on `Std.HashMap`; we need provable maps
- **No external Lean dependencies** — pure Lean 4.29 core (Std is merged into core since 4.x)
- **Veil-inspired but standalone** — we implement the transition system pattern without depending on Veil's build (avoids Mathlib dependency chain)

---

## License

MIT

---

<div align="center">
<i>Built for the Cloudflare $1M Formal Verification Prize</i>
</div>
