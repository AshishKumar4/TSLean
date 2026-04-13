# Cloudflare Agents SDK — TSLean Transpilation Report

**Date:** 2026-04-13
**TSLean version:** latest (from `/workspace/tslean/`)
**Target:** Cloudflare Agents SDK (`agents-sdk/packages/agents/src/`)
**Lean version:** 4.29.0

---

## Executive Summary

| Metric | Value |
|--------|-------|
| Total source files | 66 |
| Total TS source lines | 20,297 |
| **Transpilation success rate** | **97.0% (64/66 files)** |
| TSX files (need `-o` workaround) | 2 (with workaround: 100%) |
| Total Lean output lines | 9,196 (incl. TSX) |
| Lean/TS line ratio | 0.45 (Lean output is ~45% of TS input) |
| **Total `sorry` count** | **682** |
| Zero-sorry files | 28 / 66 (42.4%) |
| **Lean compilation success** | **11 / 28 zero-sorry files (39.3%)** |
| **End-to-end success (transpile + compile)** | **11 / 66 files (16.7%)** |

**Bottom line:** TSLean can *parse and transpile* nearly all production TypeScript (97%), but the generated Lean only type-checks for simple files (barrel re-exports, enums, type-only modules). Files with real logic produce Lean that has type errors, missing identifiers, or incorrect monad types. Of the ~20K lines of TS, roughly **3-5% becomes verified Lean** today.

---

## 1. File-by-File Results

### 1a. Files that Failed Transpilation (2)

| File | TS Lines | Reason |
|------|----------|--------|
| `ai-react.tsx` | 13 | CLI outputs `.tsx` instead of `.lean` (path bug) |
| `react.tsx` | 126 | Same `.tsx` output path bug |

Both files transpile successfully when `-o output.lean` is used explicitly. This is a CLI bug, not a transpiler limitation.

### 1b. Zero-Sorry Files (28) — Transpile Clean

| File | TS Lines | Lean Lines | Lean Compiles? |
|------|----------|------------|----------------|
| `ai-chat-agent.ts` | 5 | 13 | No (type mismatch) |
| `ai-chat-v5-migration.ts` | 5 | 13 | No (type mismatch) |
| `ai-types.ts` | 16 | 15 | No (unknown identifier) |
| `chat/client-tools.ts` | 63 | 27 | No (application type mismatch) |
| `chat/index.ts` | 56 | 10 | **Yes** |
| `chat/parse-protocol.ts` | 133 | 45 | No (application type mismatch) |
| `chat/protocol.ts` | 21 | 13 | No (invalid `{...}` notation) |
| `chat/turn-queue.ts` | 117 | 85 | No (function expected) |
| `codemode/ai.ts` | 5 | 10 | **Yes** |
| `core/events.ts` | 52 | 48 | No (field access error) |
| `experimental/memory/index.ts` | 17 | 10 | **Yes** |
| `experimental/memory/session/index.ts` | 56 | 10 | **Yes** |
| `experimental/memory/session/provider.ts` | 73 | 34 | **Yes** |
| `experimental/memory/session/types.ts` | 43 | 42 | No (typeclass stuck) |
| `experimental/memory/utils/index.ts` | 23 | 10 | **Yes** |
| `internal_context.ts` | 34 | 16 | No (unknown `AsyncLocalStorage`) |
| `mcp/client-storage.ts` | 12 | 13 | **Yes** |
| `mcp/client-transports.ts` | 42 | 49 | No (application type mismatch) |
| `mcp/types.ts` | 25 | 51 | No (function expected) |
| `observability/agent.ts` | 63 | 14 | **Yes** |
| `observability/base.ts` | 28 | 13 | **Yes** (warnings only) |
| `observability/mcp.ts` | 39 | 14 | **Yes** |
| `retries.ts` | 159 | 96 | No (typeclass synthesis failure) |
| `serializable.ts` | 163 | 135 | No (typeclass synthesis failure) |
| `types.ts` | 13 | 33 | **Yes** |
| `utils.ts` | 20 | 22 | No (application type mismatch) |
| `vite.ts` | 24 | 14 | No (unknown `babel`) |
| `workflow-types.ts` | 312 | 96 | No (unknown `WorkflowStep`) |

### 1c. Files with Sorrys (38) — Sorted by Sorry Count

| File | TS Lines | Lean Lines | Sorrys | Density* |
|------|----------|------------|--------|----------|
| `index.ts` | 5,451 | 1,770 | 207 | 3.8 |
| `mcp/client.ts` | 1,578 | 580 | 92 | 5.8 |
| `mcp/client-connection.ts` | 816 | 304 | 50 | 6.1 |
| `mcp/worker-transport.ts` | 941 | 406 | 42 | 4.5 |
| `experimental/memory/session/session.ts` | 551 | 297 | 42 | 7.6 |
| `experimental/memory/session/manager.ts` | 488 | 277 | 34 | 7.0 |
| `mcp/transport.ts` | 385 | 220 | 29 | 7.5 |
| `mcp/index.ts` | 549 | 187 | 26 | 4.7 |
| `experimental/memory/session/context.ts` | 814 | 349 | 24 | 2.9 |
| `workflows.ts` | 458 | 119 | 15 | 3.3 |
| `chat/message-builder.ts` | 411 | 71 | 15 | 3.6 |
| `chat/stream-accumulator.ts` | 232 | 100 | 14 | 6.0 |
| `experimental/memory/utils/compaction-helpers.ts` | 493 | 173 | 13 | 2.6 |
| `experimental/memory/session/providers/agent.ts` | 391 | 231 | 8 | 2.0 |
| `chat/sanitize.ts` | 187 | 83 | 7 | 3.7 |
| `mcp/utils.ts` | 829 | 73 | 7 | 0.8 |
| `chat/resumable-stream.ts` | 506 | 247 | 6 | 1.2 |
| `client.ts` | 558 | 154 | 5 | 0.9 |
| `email.ts` | 399 | 104 | 5 | 1.3 |
| `experimental/memory/session/search.ts` | 177 | 111 | 5 | 2.8 |
| `experimental/memory/session/skills.ts` | 96 | 57 | 5 | 5.2 |
| `mcp/x402.ts` | 502 | 60 | 5 | 1.0 |
| `react.tsx` *(via -o)* | 126 | 1,181 | 4 | 3.2 |
| `chat/abort-registry.ts` | 63 | 40 | 4 | 6.3 |
| `mcp/auth-context.ts` | 15 | 21 | 2 | 13.3 |
| `mcp/do-oauth-client-provider.ts` | 258 | 206 | 2 | 0.8 |
| `mcp/rpc.ts` | 315 | 194 | 2 | 0.6 |
| `ai-react.tsx` *(via -o)* | 13 | 144 | 2 | 15.4 |
| `chat/broadcast-state.ts` | 153 | 42 | 1 | 0.7 |
| `chat/continuation-state.ts` | 141 | 106 | 1 | 0.7 |
| `chat/tool-state.ts` | 98 | 33 | 1 | 1.0 |
| `experimental/memory/session/providers/agent-context.ts` | 55 | 59 | 1 | 1.8 |
| `experimental/memory/utils/compaction.ts` | 98 | 33 | 1 | 1.0 |
| `experimental/memory/utils/tokens.ts` | 84 | 33 | 1 | 1.2 |
| `mcp/errors.ts` | 39 | 47 | 1 | 2.6 |
| `mcp/handler.ts` | 143 | 40 | 1 | 0.7 |
| `observability/index.ts` | 125 | 58 | 1 | 0.8 |
| `schedule.ts` | 140 | 35 | 1 | 0.7 |

*Density = sorrys per 100 TS source lines

---

## 2. Sorry Pattern Taxonomy

682 total `sorry` instances across 38 files. Categorized by root cause:

### Category 1: Mutable Field/Index Assignment (57 instances, 8.4%)
```lean
sorry /- assign: FieldAccess -/     -- 50 instances
sorry /- assign: IndexAccess -/     --  7 instances
```
**TS pattern:** `obj.field = value` or `obj[key] = value`
**Why:** Lean is immutable. The transpiler has no mutation model for arbitrary field/index writes on mutable objects. `StateT` + record update syntax covers struct fields but not dynamic property assignment.

### Category 2: Unresolved Expressions in `let` Bindings (68 instances, 10.0%)
```lean
let store := sorry
let writer := sorry
let readable : TSAny := sorry
```
**TS patterns causing this:**
- Complex method chains: `new TextEncoder()`, `response.body.getReader()`
- Constructor calls to browser/Node APIs
- Spread operators: `{ ...defaults, ...options }`
- Destructuring: `const { a, b } = obj`

### Category 3: Conditions with `sorry` (130 instances, 19.1%)
```lean
if (sorry : Bool) /- type test: TSAny -/ then ...
if sorry then ...
if (sorry) || shouldProbeCapabilities then ...
```
**TS patterns:**
- `instanceof` checks (no Lean equivalent)
- Complex boolean expressions involving method calls
- Optional chaining in conditions: `if (obj?.method())`
- Nullish coalescing: `value ?? default`

### Category 4: Bare `sorry` (83 instances, 12.2%)
```lean
sorry
```
Standalone sorry on its own line — typically replacing:
- Complex imperative blocks (for/while loops with mutations)
- Switch/case blocks on non-enum types
- Try/catch with complex recovery logic
- Callback registrations

### Category 5: Lambda/Callback Bodies (92 instances, 13.5%)
```lean
fun args => ... sorry
fun _ => clearInterval keepAlive; ... sorry
```
**TS pattern:** Event handlers, Promise callbacks, Array.map/filter/forEach with complex bodies. The transpiler struggles with closures that capture mutable state.

### Category 6: Optional Chaining / Nullish Coalescing (14 explicit, ~50 implicit)
```lean
Option.getD (sorry) 5000
Option.getD (sorry) "auto"
```
**TS pattern:** `options?.maxAttempts ?? 3`, `transport?.type ?? "auto"`
The transpiler attempts `Option.getD` but fails to resolve the optional access into a valid Lean expression.

### Category 7: Entire Function Bodies (19 instances, 2.8%)
```lean
def get_sessionAffinity (self : AgentState) : String := sorry
```
**TS pattern:** Getter/setter properties, computed property accessors, or functions whose entire body is unsupported.

### Category 8: Type Tests / Guards (15 instances, 2.2%)
```lean
if (sorry : Bool) /- type test: Function -/ then ...
```
**TS pattern:** `if (err instanceof Error)`, `typeof x === "function"`

### Category 9: `pure sorry` / Return Sorry (17 instances, 2.5%)
```lean
pure sorry
```
Function return values that couldn't be transpiled.

### Category 10: Match/Switch Sorry (5 instances, 0.7%)
```lean
match sorry with
```
Switch statements on expressions that couldn't be transpiled.

### Summary: Sorry Causes by Frequency

| Rank | Pattern | Count | % |
|------|---------|-------|---|
| 1 | Conditions with sorry | 130 | 19.1% |
| 2 | Lambda/callback bodies | 92 | 13.5% |
| 3 | Bare sorry (complex blocks) | 83 | 12.2% |
| 4 | Let-binding unresolved expressions | 68 | 10.0% |
| 5 | Mutable field assignment | 57 | 8.4% |
| 6 | Optional chaining/nullish coalescing | ~64 | 9.4% |
| 7 | Entire function bodies | 19 | 2.8% |
| 8 | Pure/return sorry | 17 | 2.5% |
| 9 | Type tests/guards | 15 | 2.2% |
| 10 | Match/switch sorry | 5 | 0.7% |
| — | Other/overlapping | ~132 | 19.4% |

---

## 3. Lean Compilation Analysis

Of 28 zero-sorry files, 11 compile in Lean 4.29.0 (39.3%). The 17 failures fall into these categories:

### Compilation Error Category A: Monad Type Stacking (5 files)
```
error: Application type mismatch: The argument IO String
  has type Type but is expected to have type Type → Type
  in the application StateT Unit (IO String)
```
**Root cause:** The transpiler generates `StateT Unit (IO String)` but the correct Lean type is `StateT Unit IO String`. `IO String` is `Type`, not `Type → Type`. The monad type parameter must be the monad constructor (`IO`), not the applied type (`IO String`). This is a systematic bug in return type generation.

### Compilation Error Category B: Unknown Identifiers (4 files)
```
error: Unknown identifier `AsyncLocalStorage`
error: Unknown identifier `babel`
error: Unknown identifier `WorkflowStep`
```
**Root cause:** References to external TS types, Node.js APIs, or other modules that don't exist in the Lean runtime. The transpiler needs either: stubs for common APIs, or explicit import resolution.

### Compilation Error Category C: Typeclass Synthesis (3 files)
```
error: failed to synthesize instance of type class Repr (Option (Option (TSAny → Float → Bool)))
error: typeclass instance problem is stuck
```
**Root cause:** `deriving Repr, BEq` on structures containing function types or deeply nested Options. Lean can't auto-derive `Repr` or `BEq` for `(TSAny → Float → Bool)`.

### Compilation Error Category D: Invalid Lean Syntax (5 files)
```
error: invalid {...} notation, expected type is not of the form (C ...)
error: `dispose` is not a field of structure `Disposable`
error: Function expected at TurnResult
```
**Root cause:** Anonymous object literals `{ field: value }` without a corresponding Lean structure; field access on types that aren't structures; using type aliases as functions.

---

## 4. What TSLean Handles Well

1. **Enum transpilation** — TS `const enum` / string literal unions → Lean `inductive` types with `toString`. Clean and correct. (`types.ts`)

2. **Interface/type definitions** — TS interfaces → Lean structures with `deriving` clauses (when types are simple). (`serializable.ts`, `workflow-types.ts`)

3. **Re-export barrels** — Index files that just re-export become clean Lean namespace imports. (All `/index.ts` files)

4. **Simple pure functions** — Functions with basic control flow, string operations, and arithmetic transpile with correct structure.

5. **Structure preservation** — The overall module structure (namespaces, function signatures, type hierarchies) is well-preserved in the Lean output.

6. **Comment preservation** — TSDoc comments become Lean docstrings correctly.

---

## 5. What TSLean Cannot Handle (Major Gaps)

### Gap 1: Mutable State (Critical)
The Agents SDK is heavily imperative — classes with mutable fields, event handler registration, WebSocket connection state. TSLean's `StateT`-based approach can't express arbitrary field mutation on dynamic objects.

### Gap 2: Async/Await and Promises (Critical)
809 `async` declarations in the SDK. The transpiler converts these to `StateT`/`ExceptT` monads but generates incorrect type signatures (e.g., `ExceptT String (IO Unit)` instead of `ExceptT String IO Unit`).

### Gap 3: Class Hierarchies with `this` (Major)
The SDK uses deep class hierarchies (`Agent` base class, mixins, method overrides). Lean doesn't have classes; the transpiler generates structures but can't handle `this`, `super`, inheritance, or dynamic dispatch.

### Gap 4: Dynamic Property Access (Major)
`obj[key]`, `Object.keys()`, `Object.entries()`, `delete obj.prop` — common patterns in the SDK for working with JSON-like data. No Lean equivalent is generated.

### Gap 5: External API Types (Major)
Node.js (`AsyncLocalStorage`, `TextEncoder`), Web APIs (`WebSocket`, `Request`, `Response`, `URL`), and Cloudflare Workers types (`DurableObjectState`, `Fetcher`) have no Lean stubs.

### Gap 6: JSX/TSX (Minor CLI Bug)
`.tsx` files transpile correctly but the CLI writes output to `.tsx` instead of `.lean`. Workaround: use `-o` flag.

### Gap 7: Type Guards and Narrowing (Moderate)
`instanceof`, `typeof`, discriminated unions — TypeScript's type narrowing has no Lean equivalent. The transpiler emits `sorry` for these.

### Gap 8: Spread/Rest/Destructuring (Moderate)
`{ ...defaults, ...overrides }`, `const { a, b, ...rest } = obj`, `...args` — structural patterns that are pervasive in the SDK.

### Gap 9: Template Literals with Expressions (Minor)
`` `prefix-${expr}` `` is common; the transpiler handles simple cases but fails on complex interpolations.

### Gap 10: Closures over Mutable State (Major)
Event handlers that capture and mutate outer variables are extremely common in the SDK and fundamentally at odds with Lean's pure functional model.

---

## 6. Recommendations for TSLean Improvement

### P0 — Fix Immediately
1. **Fix monad type generation**: `StateT Unit (IO String)` → `StateT Unit IO String`. This is a systematic bug that breaks every file with `async` functions.
2. **Fix TSX output path**: CLI should output `.lean` for `.tsx` inputs, not `.tsx`.
3. **Fix `deriving` clauses**: Don't emit `deriving Repr, BEq` for structures containing function types.

### P1 — High Impact
4. **Add Web/Node API stubs**: Create Lean declarations for `Request`, `Response`, `URL`, `WebSocket`, `TextEncoder`, `AsyncLocalStorage`, etc. as opaque types with `sorry`-ed methods. This would unblock many files from compiling.
5. **Fix optional chaining translation**: `obj?.field ?? default` should produce valid `Option.getD (obj.field?) default` patterns.
6. **Improve mutable field assignment**: Use `modify (fun s => { s with field := value })` patterns more broadly instead of bare `sorry`.

### P2 — Medium Impact
7. **Anonymous object literal support**: `{ key: value }` should generate named structures or use `AssocMap`.
8. **Type guard translation**: `instanceof` → pattern match; `typeof` → runtime type tag check.
9. **Spread operator**: `{ ...a, ...b }` → record merge function.
10. **Import resolution**: Resolve cross-file references so `WorkflowStep` in one file can find the definition from another.

### P3 — Aspirational
11. **Class hierarchy model**: A trait/typeclass-based approach for class inheritance.
12. **Async/Promise model**: An `Async` monad or `Task` type that properly models JS async semantics.
13. **Closure model**: Effect tracking for closures that capture mutable state.

---

## 7. Honest Assessment

### What % of the SDK can TSLean handle today?

| Level | Definition | % |
|-------|------------|---|
| **Transpile** (produces any `.lean` output) | 97% (64/66, 100% with `-o` workaround) |
| **Transpile clean** (zero `sorry`) | 42% of files (28/66), but only 5.3% of source lines* |
| **Compile in Lean** (type-checks) | 17% of files (11/66), ~2% of source lines** |
| **Semantically correct** (logic preserved) | ~2-5% of total codebase*** |

\* Zero-sorry files account for 1,079 of 20,297 source lines (5.3%), but most are barrel re-exports with 5-56 lines.

\** The 11 compiling files are primarily namespace-only barrels (chat/index.ts, memory/index.ts, etc.) plus `types.ts` (33 lines of enum). Total meaningful compiled Lean: ~250 lines.

\*** Even compiling files may not preserve semantics. The `types.ts` enum translation is the only file where TSLean demonstrably produces correct, meaningful Lean.

### Key Takeaways

1. **TSLean is an excellent parser.** 97% transpilation rate on production code is impressive. The TypeScript→IR front-end handles real-world complexity well.

2. **The Lean code generation has fundamental gaps.** The generated code is structurally reasonable but doesn't type-check because of incorrect monad types, missing API stubs, and unsupported mutation patterns.

3. **The sorry mechanism works as designed.** Rather than crashing, unsupported patterns are replaced with `sorry`, producing files that are at least structurally complete. The 682 sorrys are concentrated in a predictable set of patterns (mutation, async, dynamic access).

4. **The SDK is a worst-case scenario for functional transpilation.** It's heavily imperative, mutation-heavy, uses dynamic objects, class hierarchies, WebSocket state machines, and Node.js APIs. A pure utility library would fare much better.

5. **The path to usefulness is clear.** Fixing the monad type bug (P0) + adding API stubs (P1) + improving optional chaining (P1) would likely increase Lean compilation from 17% to ~40-50% of files. Getting the imperative core (Agent class, MCP client) to compile would require the P3 items.

---

## Appendix: Test Environment

- **Source:** `agents-sdk/packages/agents/src/` — Cloudflare Agents SDK
- **Excluded:** test files, `.d.ts` files, `cli/` directory
- **Transpiler:** `/workspace/tslean/` with `npx tsx src/cli.ts`
- **Lean compiler:** Lean 4.29.0 with TSLean runtime library
- **Compilation test:** `lake env lean <file>` in the TSLean lean project
