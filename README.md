# TSLean

**TypeScript → Lean 4 transpiler with formal verification for Cloudflare Durable Objects.**

TSLean converts typed TypeScript into compilable, verifiable Lean 4 code. It ships with a runtime library that models Durable Objects as state machines — letting you write your DO in TypeScript and get machine-checked proofs that your system is correct.

## Why?

Cloudflare Durable Objects are stateful actors that power real-time systems at scale. Their correctness properties — rate limits are never exceeded, auth tokens can't be used after revocation, message ordering is preserved — are normally validated only by testing.

TSLean makes these properties mathematically provable. The transpiler produces Lean 4 code that carries the same types, effects, and structure as your TypeScript. The verification library provides proved theorems for common DO patterns.

## Quick Start

```bash
git clone https://github.com/AshishKumar4/TSLean.git
cd TSLean
bun install

# Transpile a single file
npx tsx src/cli.ts examples/counter.ts -o output.lean

# Transpile a multi-file project
npx tsx src/cli.ts --project my-workers-app/ -o lean/Generated/

# Run tests
bun run test

# Build & verify the Lean library (requires Lean 4.29.0)
cd lean && lake build
```

## Architecture

```
┌────────────┐    ┌────────┐    ┌──────────┐    ┌─────────┐    ┌─────────┐    ┌────────┐
│ TypeScript │───▶│ Parser │───▶│ IR (Fω + │───▶│ Rewrite │───▶│ Codegen │───▶│ Lean 4 │
│ Source     │    │(TS API)│    │ effects) │    │  Pass   │    │         │    │ Output │
└────────────┘    └────────┘    └──────────┘    └─────────┘    └─────────┘    └────────┘
```

The parser uses the TypeScript Compiler API (not Babel) for full type resolution and generic instantiation. The IR is System Fω with algebraic effect annotations. The rewrite pass converts discriminated unions into inductive pattern matching. The codegen emits Lean 4 with proper namespaces, do-notation, and `TSLean.*` imports.

## Type Translations

| TypeScript | Lean 4 |
|---|---|
| `interface Point { x: number; y: number }` | `structure Point where x : Float; y : Float` |
| `type Shape = { kind: "circle"; r: number } \| { kind: "rect"; w: number }` | `inductive Shape where \| circle (r : Float) \| rect (w : Float)` |
| `type UserId = string & { __brand: "UserId" }` | `structure UserId where val : String deriving BEq` |
| `Promise<T>` | `TaskM T` |
| `T \| undefined` | `Option T` |
| `{ [key: string]: number }` | `AssocMap String Float` |
| `async function f()` | `def f : TaskM Unit := do ...` |
| `x?.prop` | `x.bind (fun v => v.prop)` |
| `a ?? b` | `a.getD b` |
| `{ ...obj, name: v }` | `{ obj with name := v }` |

## Effect Mapping

| TypeScript Pattern | Lean 4 Monad |
|---|---|
| Pure functions | Direct functions (no monad) |
| Mutations (`this.state = ...`) | `StateT σ` |
| `async/await` | `TaskM` (IO-based) |
| `throw/try/catch` | `ExceptT TSError` |
| Durable Object methods | `DOMonad σ α = StateT σ (ExceptT TSError IO)` |

## Verification Library

The `lean/` directory is a pure Lean 4.29 library (no Mathlib, no external dependencies) that provides:

- **Runtime types and monads** — `TSValue`, `TSError`, `DOMonad`, branded types, coercions
- **Verified standard library** — `AssocMap` (with `Nodup` proof), `HashSet`, bounds-checked arrays, option/result composition
- **Durable Object models** — Transactions (ACID semantics), WebSocket sessions, RPC with roundtrip proofs, rate limiters, chat rooms, queues, auth sessions, analytics
- **Transition system verification** — Each DO modeled as a state machine with init predicates, action relations, safety properties, and invariant induction proofs

### Theorem Examples

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

-- Durable queue maintains FIFO ordering
theorem fifo_ordering (q : DurableQueue α) (a b : α)
    (h : q.enqueue a |>.enqueue b) :
    h.dequeue.fst = some a
```

The library builds with zero `sorry` — IO monad laws use honest `axiom` declarations where Lean's kernel can't reduce `IO` computations.

### Transition Systems (Veil-inspired)

Each DO is modeled as a relational transition system with a safety invariant proved by induction. The library includes a lightweight DSL inspired by [Veil](https://github.com/verse-lab/veil):

```lean
instance : TransitionSystem CounterState where
  init s := s.count = 0 ∧ s.minCount ≤ 0 ∧ 0 ≤ s.maxCount
  next s s' := increment s s' ∨ decrement s s' ∨ reset s s'
  safe s := s.minCount ≤ s.count ∧ s.count ≤ s.maxCount

theorem counter_safety : ∀ s, reachable s → safe s
```

Seven DO models (Counter, Auth, RateLimiter, ChatRoom, Queue, SessionStore, plus DSL examples) are formalized this way, with `Specification.lean` aggregating the verified safety properties.

## Multi-File Transpilation

TSLean resolves TypeScript import graphs and generates Lean module imports:

```bash
npx tsx src/cli.ts --project my-workers-app/ -o lean/Generated/MyApp/
```

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

Produces:

```lean
-- Generated/Shared/Types.lean
structure UserId where val : String deriving Repr, BEq, DecidableEq
structure User where id : UserId; email : String; roles : Array String

-- Generated/Backend/AuthDo.lean
import TSLean.Generated.Shared.Types
def authenticate (self : AuthDOState) (token : String) : DOMonad AuthDOState (Option User) := do ...
```

## Self-Hosting

TSLean can transpile all of its own source modules to Lean 4. The 12 self-hosted files (IR types, parser, codegen, type mapper, effects, rewrite, stdlib, verification, project, DO model, CLI) all compile under `lake build`. This required hand-patching codegen gaps (mutual recursion, TS compiler API stubs, class method dispatch), but the type structures and function signatures are preserved faithfully from the transpiler output.

## Building & Verifying

**Requirements:** Node.js ≥ 18, Lean 4.29.0

```bash
# TypeScript tests (1415 passing)
bun run test

# Lean library (105 build jobs, 0 sorry)
cd lean && lake build

# Type-check the transpiler
bun run lint
```

## Project Structure

- `src/` — Transpiler: parser, IR, type mapper, effect system, rewrite pass, codegen, CLI
- `lean/TSLean/` — Lean 4 runtime, stdlib, DO models, Veil transition systems, verification tactics
- `lean/TSLean/Generated/` — Transpiler output (verified to compile)
- `tests/` — Vitest suites covering parser, codegen, types, effects, DOs, e2e

## License

MIT

---

*Built for the Cloudflare Formal Verification Prize.*
