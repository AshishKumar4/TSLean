# Lean 4 → Idiomatic TypeScript Transpiler: v2.0 Plan

## The Core Thesis

This is **not** a general Lean→TS compiler. It is a **domain-specific reverse transpiler** that exploits the narrow, well-designed conventions of the TSLean library to produce TypeScript indistinguishable from hand-written code. The Lean code follows ~8 predictable patterns. We recognize those patterns and emit their idiomatic TS equivalents.

---

## Table of Contents

1. [Input Strategy](#1-input-strategy-parse-lean-surface-syntax)
2. [Architecture: The Pipeline](#2-architecture-the-pipeline)
3. [Ideal Output Examples](#3-ideal-output-examples)
4. [Stdlib Mapping Table](#4-stdlib-mapping-table-declarative)
5. [Round-Trip: TS → Lean → Verify → TS](#5-round-trip-ts--lean--verify--ts)
6. [Feasibility: Achievable vs. Aspirational](#6-feasibility-achievable-vs-aspirational)
7. [Existing Work](#7-existing-work)
8. [Reviewer Consensus & Dissent](#8-reviewer-consensus--dissent)
9. [Implementation Order](#9-implementation-order)
10. [Open Decision Questions](#10-open-decision-questions)
11. [Appendix A: Lean 4 Toolchain Research](#appendix-a-lean-4-toolchain-research)
12. [Appendix B: Detailed File Analysis](#appendix-b-detailed-file-analysis)
13. [Appendix C: Full Reviewer Reports](#appendix-c-full-reviewer-reports)

---

## 1. Input Strategy: Parse Lean Surface Syntax

**Decision: Parse the `.lean` text directly. No LCNF, no `.olean`, no generated C.**

Rationale from research:

- Lean 4 has **no structured AST export**. The available outputs are: `.olean` (opaque binary), `.ilean` (JSON but only declaration positions), `-c` (generated C — too low-level), `--json` (diagnostics only).
- Surface syntax preserves names, comments, structure groupings, and the `-- @ts-original:` metadata comments that the forward transpiler embeds.
- The TSLean library uses a **small, predictable dialect** of Lean 4. We are not parsing arbitrary Lean — we are parsing a constrained subset.

**Critical design principle:** The parser should **reject** Lean syntax it does not recognize rather than attempting to handle it. If we encounter something unexpected, emit a diagnostic and skip it.

**Implementation: hand-tuned recursive descent parser**, not a general Lean parser. This will be 1/10th the complexity and 10x more reliable. The subset we need:

| Construct | Example |
|-----------|---------|
| `namespace`/`end` | `namespace TSLean.Generated.CounterDO` |
| `structure` | `structure CounterState where count : Nat` |
| `inductive` | `inductive HttpMethod where \| GET \| POST ...` |
| `def` | `def increment : DOMonad CounterState Nat := do ...` |
| `abbrev` | `abbrev Storage := AssocMap StorageKey StorageValue` |
| `theorem` | (recognize and skip entirely) |
| `instance` | (recognize and skip entirely) |
| `import`/`open`/`set_option` | (metadata, not code) |
| `do`-blocks | `let st ← get; ...; set st'; return x` |
| `match` | `match s with \| .Circle r => ...` |
| `if/then/else` | `if x > 0 then x - 1 else 0` |
| `{ ... with ... }` | `{ st with count := st.count + 1 }` |
| Function application | `f x y` |
| Lambda | `fun x => ...` |
| Comments | `-- TypeScript: ...` (parse as metadata) |

What we explicitly **do not handle**: tactic blocks, `where` clauses with complex recursion, universe polymorphism, `macro`, `syntax`, `elab`, `#check`, `#eval`, dependent types beyond simple generics.

---

## 2. Architecture: The Pipeline

**Revised pipeline (pattern recognition BEFORE IR lowering, no separate IR):**

```
Lean text
  → LeanParser         (surface syntax → LeanAST)
  → Analyzer            (symbol table, declaration classification, metadata extraction)
  → PatternRecognizer   (annotate LeanAST: class extraction, monad analysis, proof erasure)
  → Projector           (build TS outline: which classes, methods, imports)
  → TSEmitter           (annotated LeanAST → TS text directly)
```

### Stage 1: LeanParser

Recursive descent parser producing `LeanAST` nodes. **Reuse the `LeanAST` type definitions from `src/codegen/lean-ast.ts`** in the existing forward transpiler — the same AST types work bidirectionally.

### Stage 2: Analyzer

Two-pass analysis:

1. **First pass**: Build symbol table. Classify every declaration:
   - `structure` → candidate class/interface
   - `def Foo.bar (self: Foo) ...` → candidate instance method
   - `def bar : DOMonad Foo α` → candidate async class method
   - `def Foo.new ...` → candidate constructor
   - `def Foo.bar (args) : Foo` → candidate static factory
   - `theorem`/`axiom`/`private theorem` → **erase**
   - `instance` → **erase** (except extract `Coe` instances as useful metadata)
   - `deriving` → **erase**

2. **Second pass**: Resolve cross-references. Determine which functions call which. Group declarations into class candidates.

### Stage 3: PatternRecognizer

The core of the idiomaticity engine. Operates on annotated `LeanAST`. **Eight primary patterns:**

| # | Pattern | Detection | TS Output |
|---|---------|-----------|-----------|
| 1 | **Class extraction** | structure `S` + functions `S.foo(self: S)` in same namespace | `class S { foo() { ... } }` |
| 2 | **DOMonad → async class** | `DOMonad σ α` functions + structure `σ` | `class extends DurableObject { async foo(): Promise<α> }` |
| 3 | **Monad erasure** | `do { let st ← get; ...; set st'; return x }` | `this.field = ...; return x` |
| 4 | **Proof erasure** | `theorem`, `axiom`, `instance : LawfulBEq`, proof fields | Drop entirely |
| 5 | **Inductive → union** | `inductive` with variant constructors | discriminated union or string literal union |
| 6 | **Functional → mutable** | `{ s with field := val }` on same binding | `this.field = val` |
| 7 | **Stdlib mapping** | `AssocMap.insert`, `List.map`, `Option.some`, etc. | `Map.set()`, `.map()`, nullable |
| 8 | **Branded types** | `structure X where val : String` + `Coe` instance | `type X = string & { __brand: 'X' }` |

### Stage 4: Projector

Build the TS module outline before generating bodies:

- Which files to emit
- Which classes exist, their fields, method signatures
- Import graph (Lean `import` → TS `import`)
- This prevents generating a method body that references a class not yet decided

### Stage 5: TSEmitter

Direct emission from annotated LeanAST to TypeScript text. No intermediate TS AST (unless we find we need one). A pretty-printer that respects:

- 2-space indentation
- `export` on public declarations
- `async`/`Promise<T>` for DOMonad functions
- `readonly` for structure fields that are never updated
- Property getters for nullary reader methods (`get size()`, `get isEmpty()`)

---

## 3. Ideal Output Examples

### Example A: `Generated/CounterDO.lean` → `counter-do.ts`

**Lean input** (100 lines, ~40 def + 60 theorem):

```lean
structure CounterState where count : Nat
def CounterState.initial : CounterState := { count := 0 }
def increment : DOMonad CounterState Nat := do
  let st ← get
  let st' := { st with count := st.count + 1 }
  set st'
  return st'.count
def decrement : DOMonad CounterState Nat := do
  let st ← get
  let st' := { st with count := if st.count > 0 then st.count - 1 else 0 }
  set st'
  return st'.count
def getCount : DOMonad CounterState Nat := do
  let st ← get
  return st.count
def reset : DOMonad CounterState Unit := do
  set CounterState.initial
def addN (n : Nat) : DOMonad CounterState Nat := do
  let st ← get
  let st' := { st with count := st.count + n }
  set st'
  return st'.count
-- ... 60 lines of theorems (erased) ...
```

**Ideal TS output** (25 lines):

```typescript
import { DurableObject } from "cloudflare:workers";

export class CounterDO extends DurableObject {
  private count = 0;

  async increment(): Promise<number> {
    this.count += 1;
    return this.count;
  }

  async decrement(): Promise<number> {
    this.count = Math.max(0, this.count - 1);
    return this.count;
  }

  async getCount(): Promise<number> {
    return this.count;
  }

  async reset(): Promise<void> {
    this.count = 0;
  }

  async addN(n: number): Promise<number> {
    this.count += n;
    return this.count;
  }
}
```

**Pattern recognitions needed**: DOMonad→class (#2), monad erasure (#3), proof erasure (#4), functional→mutable (#6), `if x > 0 then x - 1 else 0` → `Math.max(0, x - 1)`.

### Example B: `Generated/Classes.lean` → `classes.ts`

**Lean input** (110 lines):

```lean
structure Counter where
  value : Nat
  step  : Nat
def Counter.new (step : Nat := 1) : Counter := { value := 0, step }
def Counter.increment (c : Counter) : Counter := { c with value := c.value + c.step }
def Counter.decrement (c : Counter) : Counter :=
  { c with value := if c.value ≥ c.step then c.value - c.step else 0 }
def Counter.reset (c : Counter) : Counter := { c with value := 0 }
def Counter.withStep (c : Counter) (s : Nat) : Counter := { c with step := s }
def Counter.getValue (c : Counter) : Nat := c.value

structure Stack (α : Type) where items : List α
def Stack.empty : Stack α := { items := [] }
def Stack.push (s : Stack α) (x : α) : Stack α := { items := x :: s.items }
def Stack.pop (s : Stack α) : Option α × Stack α :=
  match s.items with
  | [] => (none, s)
  | x :: rest => (some x, { items := rest })
def Stack.peek (s : Stack α) : Option α := s.items.head?
def Stack.size (s : Stack α) : Nat := s.items.length
def Stack.isEmpty (s : Stack α) : Bool := s.items.isEmpty

structure Builder (α : Type) where fields : List (String × String)
def Builder.empty : Builder α := { fields := [] }
def Builder.set (b : Builder α) (k v : String) : Builder α :=
  { fields := (k, v) :: b.fields }
def Builder.get (b : Builder α) (k : String) : Option String :=
  (b.fields.find? (fun (key, _) => key == k)).map Prod.snd
-- ... ~60 lines of theorems (erased) ...
```

**Ideal TS output**:

```typescript
export class Counter {
  private value = 0;

  constructor(private step = 1) {}

  increment(): Counter {
    this.value += this.step;
    return this;
  }

  decrement(): Counter {
    this.value = Math.max(0, this.value - this.step);
    return this;
  }

  reset(): Counter {
    this.value = 0;
    return this;
  }

  withStep(step: number): Counter {
    this.step = step;
    return this;
  }

  get currentValue(): number {
    return this.value;
  }
}

export class Stack<T> {
  private items: T[] = [];

  push(item: T): void {
    this.items.unshift(item);
  }

  pop(): T | undefined {
    return this.items.shift();
  }

  peek(): T | undefined {
    return this.items[0];
  }

  get size(): number {
    return this.items.length;
  }

  get isEmpty(): boolean {
    return this.items.length === 0;
  }
}

export class Builder<T> {
  private fields = new Map<string, string>();

  set(key: string, value: string): Builder<T> {
    this.fields.set(key, value);
    return this;
  }

  get(key: string): string | undefined {
    return this.fields.get(key);
  }
}
```

**Hard part**: `Stack.pop` returns `Option α × Stack α` (tuple of value + new stack). Must recognize this as a "mutate-and-return" pattern — drop the returned stack, convert to mutation.

### Example C: `DurableObjects/Http.lean` → `http.ts`

**Lean input (definitions only, theorems erased)**:

```lean
inductive HttpMethod where
  | GET | POST | PUT | PATCH | DELETE | HEAD | OPTIONS
structure HttpResponse where
  status  : HttpStatus
  headers : HttpHeaders
  body    : String
def HttpResponse.ok          (b : String) := HttpResponse.mk' 200 b
def HttpResponse.badRequest  (b : String) := HttpResponse.mk' 400 b
def HttpResponse.json (body : String) : HttpResponse :=
  { status := 200, headers := ..., body }
def HttpResponse.isSuccess     (r : HttpResponse) : Bool := 200 ≤ r.status && r.status < 300
def HttpResponse.isClientError (r : HttpResponse) : Bool := 400 ≤ r.status && r.status < 500
```

**Ideal TS output:**

```typescript
export type HttpMethod = "GET" | "POST" | "PUT" | "PATCH" | "DELETE" | "HEAD" | "OPTIONS";

export function ok(body: string): Response {
  return new Response(body, { status: 200 });
}

export function created(body: string): Response {
  return new Response(body, { status: 201 });
}

export function badRequest(body: string): Response {
  return new Response(body, { status: 400 });
}

export function notFound(body: string): Response {
  return new Response(body, { status: 404 });
}

export function json(body: string): Response {
  return Response.json(body);
}

export function isSuccess(status: number): boolean {
  return status >= 200 && status < 300;
}

export function isClientError(status: number): boolean {
  return status >= 400 && status < 500;
}

export function isServerError(status: number): boolean {
  return status >= 500 && status < 600;
}
```

**Pattern**: zero-arg inductive → string literal union (#5). Static factories on a structure that maps to a platform type (Web `Response`) → standalone factory functions.

### Example D: `Runtime/BrandedTypes.lean` → `branded-types.ts`

**Lean input (definitions only)**:

```lean
structure UserId where val : String deriving BEq, Hashable
structure RoomId where val : String deriving BEq, Hashable
instance : Coe UserId String where coe u := u.val
def UserId.mk' (s : String) : Option UserId :=
  if s.length > 0 then some { val := s } else none
```

**Ideal TS output:**

```typescript
declare const __brand: unique symbol;

export type UserId = string & { readonly [__brand]: "UserId" };
export type RoomId = string & { readonly [__brand]: "RoomId" };
export type MessageId = string & { readonly [__brand]: "MessageId" };
export type SessionToken = string & { readonly [__brand]: "SessionToken" };

export function makeUserId(s: string): UserId | null {
  return s.length > 0 ? (s as UserId) : null;
}

export function makeRoomId(s: string): RoomId | null {
  return s.length > 0 ? (s as RoomId) : null;
}
```

---

## 4. Stdlib Mapping Table (Declarative)

The single most impactful artifact. A config that the emitter consults:

```typescript
const LEAN_TO_TS: Record<string, MappingRule> = {
  // === Types ===
  "Nat":           { ts: "number" },
  "Int":           { ts: "number" },
  "Float":         { ts: "number" },
  "String":        { ts: "string" },
  "Bool":          { ts: "boolean" },
  "Unit":          { ts: "void" },
  "Option":        { ts: "$1 | undefined", wrapper: "nullable" },
  "List":          { ts: "$1[]" },
  "Array":         { ts: "$1[]" },
  "AssocMap":      { ts: "Map<$1, $2>" },
  "DOMonad":       { ts: "Promise<$2>", context: "async-method" },
  "ByteArray":     { ts: "ArrayBuffer" },
  "Prod":          { ts: "[$1, $2]" },

  // === AssocMap operations ===
  "AssocMap.empty":    { ts: "new Map()", style: "constructor" },
  "AssocMap.insert":   { ts: ".set($1, $2)", style: "receiver" },
  "AssocMap.get?":     { ts: ".get($1)", style: "receiver" },
  "AssocMap.erase":    { ts: ".delete($1)", style: "receiver" },
  "AssocMap.contains": { ts: ".has($1)", style: "receiver" },
  "AssocMap.keys":     { ts: "[...$.keys()]", style: "receiver" },
  "AssocMap.values":   { ts: "[...$.values()]", style: "receiver" },
  "AssocMap.size":     { ts: ".size", style: "property" },

  // === List operations ===
  "List.map":       { ts: ".map($1)", style: "receiver" },
  "List.filter":    { ts: ".filter($1)", style: "receiver" },
  "List.foldl":     { ts: ".reduce($2, $1)", style: "receiver" },
  "List.length":    { ts: ".length", style: "property" },
  "List.head?":     { ts: "[0]", style: "index" },
  "List.isEmpty":   { ts: ".length === 0", style: "property" },
  "List.append":    { ts: ".concat($1)", style: "receiver" },
  "List.reverse":   { ts: ".toReversed()", style: "receiver" },
  "List.find?":     { ts: ".find($1)", style: "receiver" },
  "List.replicate": { ts: "Array.from({ length: $1 }, () => $2)", style: "static" },

  // === String operations ===
  "String.length":     { ts: ".length", style: "property" },
  "String.append":     { ts: "+ $1", style: "operator" },
  "strTrim":           { ts: ".trim()", style: "receiver" },
  "strToUpper":        { ts: ".toUpperCase()", style: "receiver" },
  "strToLower":        { ts: ".toLowerCase()", style: "receiver" },
  "strSlice":          { ts: ".slice($1, $2)", style: "receiver" },
  "strContains":       { ts: ".includes($1)", style: "receiver" },
  "strStartsWith":     { ts: ".startsWith($1)", style: "receiver" },
  "strEndsWith":       { ts: ".endsWith($1)", style: "receiver" },
  "strSplit":          { ts: ".split($1)", style: "receiver" },
  "strJoin":           { ts: ".join($1)", style: "receiver" },
  "strRepeat":         { ts: ".repeat($1)", style: "receiver" },

  // === Option operations ===
  "Option.some":    { ts: "$1", style: "unwrap" },
  "Option.none":    { ts: "undefined", style: "literal" },
  "Option.map":     { ts: "$1 != null ? $2($1) : undefined", style: "inline" },
  "Option.getD":    { ts: "$1 ?? $2", style: "operator" },
  "Option.isSome":  { ts: "$1 != null", style: "predicate" },
  "Option.isNone":  { ts: "$1 == null", style: "predicate" },

  // === Monad operations ===
  "get":      { ts: "this", context: "state-read" },
  "set":      { ts: "this.{field} = {value}", context: "state-write" },
  "return":   { ts: "return $1", context: "return" },
  "pure":     { ts: "$1", context: "unwrap" },
  "throwDO":  { ts: "throw $1", context: "throw" },
  "catchDO":  { ts: "try { $1 } catch { $2 }", context: "try-catch" },
  "liftIO_DO": { ts: "await $1", context: "await" },
  "modifyDO": { ts: "this.{field} = $1(this.{field})", context: "state-modify" },
};
```

---

## 5. Round-Trip: TS → Lean → Verify → TS

### The Full Vision

```
original.ts  →[forward]→  verified.lean  →[lean check]→  ✓  →[reverse]→  output.ts
```

### Metadata Annotations

The forward transpiler should embed structured comment blocks at the top of each generated file:

```lean
-- @ts-source: src/counter-do.ts
-- @ts-class: CounterDO extends DurableObject
-- @ts-field count: number
-- @ts-method increment: async (): Promise<number>
-- @ts-method decrement: async (): Promise<number>
-- @ts-method getCount: async (): Promise<number>
-- @ts-method reset: async (): Promise<void>
```

This is invisible to Lean's type checker and proof engine (verification integrity unaffected) but gives the reverse transpiler ground truth for class names, inheritance, and types that don't survive the Lean encoding.

**Why comment-based metadata is safe for verification**: Metadata in comments is invisible to Lean's type checker and proof engine. Theorems about `CounterState` are equally valid whether or not a comment says the original TS class was called `CounterDO`. The proofs verify behavioral properties of the Lean model, not properties of the TypeScript source text. Comment-based metadata has zero impact on verification integrity.

**Why NOT `attribute`-based metadata**: Custom Lean attributes (`attribute [ts_class "CounterDO"] CounterState`) are part of the Lean elaboration environment. They could interact with tactics, simp lemmas, or other attributes in unexpected ways. They add complexity to the Lean build. Comment-based is cleaner.

### Scope Limitation

The round-trip works for `Generated/` code **only**. The runtime library (`Runtime/`, `DurableObjects/`, `Stdlib/`, `Effects/`, `Verification/`, `Veil/`, `Proofs/`) is never reverse-transpiled — it's a **mapping target**, not a translation source.

Detailed scope breakdown:

| Directory | In scope? | Reason |
|-----------|-----------|--------|
| `TSLean/Generated/` | **YES** | Transpiler output, follows consistent patterns |
| `TSLean/Runtime/` | NO | Runtime library (defines `TSError`, `DOMonad`, etc.) — these are the translation targets |
| `TSLean/DurableObjects/` | NO | Models of Cloudflare DO APIs — corresponds to Cloudflare's runtime, not user TS |
| `TSLean/Stdlib/` | NO | `AssocMap` is the Lean model of `Map` — recognized and mapped, not transpiled |
| `TSLean/Effects/` | NO | Effect tracking infrastructure, no TS analog |
| `TSLean/Verification/` | NO | Proof infrastructure |
| `TSLean/Veil/` | NO | Verification extensions |
| `TSLean/Proofs/` | NO | Semantic preservation proofs |

### Expected Fidelity

| Scenario | Fidelity |
|----------|----------|
| Without metadata annotations | ~72% |
| With metadata annotations | ~85-88% |
| Textually identical to original | Never (formatting, style choices are lost) |
| Functionally equivalent to original | ~95%+ for the supported subset |

### What degrades in the round-trip

- **Formatting and whitespace** (expected, irrelevant)
- **`null` vs `undefined` distinction** (both become `Option`)
- **Ternary `? :` vs `if/else`** (both become Lean `if/then/else`)
- **Method chaining style**
- **`enum` numeric values**
- **Renamed identifiers** (`repeat` → `repeatStr`) unless metadata preserves the original name
- **`extends DurableObject`** — not encoded in Lean structure, requires metadata
- **Variable names** — largely preserved, but some renamed for Lean keyword collision
- **Import structure** — Lean namespaces don't map 1:1 to TS import paths
- **Constructor patterns** — `Counter.new` could have been `new Counter()` or a factory; distinction lost

### Invertibility Assessment Per Transformation

| Transformation | Invertibility | Key Blocker |
|---------------|---------------|-------------|
| class → structure + namespace + methods | ~75% | Inheritance, access modifiers lost |
| discriminated union → inductive | ~60% | Tag field names, literal string values lost |
| async/await → DOMonad do-notation | ~70% | Cannot distinguish async from sync+effectful |
| mutable state → StateT get/set | ~80% | Complex mutation patterns ambiguous |
| try/catch → ExceptT throw/catch | ~90% | Clean mapping via TSError |
| Map<K,V> → AssocMap K V | ~85% | Needs translation table |
| T \| null → Option T | ~95% | null vs undefined conflated |
| number → Nat/Float | ~95% (single trip) | Re-transpilation may choose differently |
| Array → List | ~90% | Both become T[] |

---

## 6. Feasibility: Achievable vs. Aspirational

### Achievable (v1.0 — engineering, not research)

| Capability | Effort |
|------------|--------|
| Lean surface parser for TSLean dialect | 2-3 weeks |
| Proof/instance/theorem erasure | 1 week |
| Simple `structure` → `interface` | 1 week |
| Zero-arg `inductive` → string literal union | 1 week |
| `def Foo.bar(self: Foo)` → class method | 2 weeks |
| Stdlib mapping table (AssocMap→Map, List→Array, Option→nullable) | 2 weeks |
| DOMonad `do`-blocks → async methods (simple get/set/return) | 2-3 weeks |
| `{ s with field := val }` → `this.field = val` (single level) | 1 week |
| Comment metadata extraction (`-- @ts-original:`) | 1 week |
| Golden-file tests against every `Generated/` file | 1 week |

**Total v1.0: ~3-4 months.** Covers ~70% of Generated/ files idiomatically.

### Hard but achievable (v1.5 — requires careful engineering)

| Capability | Challenge |
|------------|-----------|
| Tuple-return state threading (`Option α × Stack α` → `pop(): T \| undefined` + mutation) | Must detect linear usage of returned state |
| Nested with-updates (`{ s with storage := { s.storage with ... } }`) | Multi-level field mutation |
| DOMonad composition (calling one DOMonad function from another) | Method-call recognition across definitions |
| Branded type detection and emission | Pattern match `structure X where val : String` + `Coe` |
| Static factory vs instance method disambiguation | Heuristic: does it take `self` or not? |

### Aspirational (v2.0 — pushing boundaries)

| Capability | Why it's hard |
|------------|---------------|
| `if x > 0 then x - 1 else 0` → `Math.max(0, x - 1)` | Semantic pattern matching on arithmetic expressions |
| Automatic `get size()` for nullary readers | Must distinguish getters from zero-arg methods |
| Platform type mapping (`HttpResponse` → Web API `Response`) | Domain-specific knowledge per API surface |
| Session type emission (`WebSocket.lean`) | No TS equivalent exists |
| Self-hosted transpiler code round-trip | `default` stubs cannot be reconstructed |

### Not achievable (honest assessment)

| Goal | Why |
|------|-----|
| Textually identical round-trip | Formatting, naming, style choices are destroyed by abstraction gap |
| Arbitrary Lean 4 → TS | Dependent types, tactics, metaprogramming have no TS equivalent |
| Transpiling the runtime library (`Runtime/`, `DurableObjects/`) | These ARE the translation target, not source code |
| Handling Lean code not produced by TSLean conventions | The idiomaticity comes from exploiting the narrow conventions |

### Idiomaticity Rating by Module

| Module | Transpilable to idiomatic TS? | Confidence |
|--------|-------------------------------|------------|
| `Generated/Hello.lean` | ~95% | Pure functions, trivial |
| `Generated/Interfaces.lean` | ~90% | Structures → interfaces |
| `Generated/Classes.lean` (Stack, Counter, Builder) | ~75% | Requires immutable→mutable conversion |
| `Generated/CounterDO.lean` | ~85% | Clean DOMonad pattern |
| `Generated/ChatRoom.lean` | ~70% | Nested state, List→Array |
| `Generated/RateLimiter.lean` | ~65% | Tuple returns, sliding window |
| `Generated/SessionStore.lean` | ~70% | AssocMap→Map, branded types |
| `Generated/QueueProcessor.lean` | ~60% | Tuple returns, dead letter queue |
| `DurableObjects/Http.lean` | ~85% | Static factories → helpers |
| `DurableObjects/WebSocket.lean` | ~40% | Session types have no TS equivalent |
| `Effects/Core.lean` | ~30% | Effect system is purely Lean-side |
| `Veil/*.lean` | **0%** | Pure specification, no TS output |
| `Proofs/*.lean` | **0%** | Pure proofs, no TS output |

**Weighted overall: ~55-65% of definition code (excluding proofs/specs) could be transpiled to genuinely idiomatic TypeScript.** If you relax "genuinely idiomatic" to "correct and readable but slightly mechanical-looking," the number jumps to **80-85%**.

---

## 7. Existing Work

**There is no existing Lean 4 → JavaScript or TypeScript transpiler or backend.** Confirmed by research:

- Lean 4 compiles to C (via `EmitC`) and LLVM IR. No JS backend exists or is planned.
- The FRO Year 3 roadmap (Aug 2025 - Jul 2026) focuses on native codegen. No JS/WASM backend.
- The Lean 4 web playground runs Lean server-side via WebSocket, not in the browser.
- Lean 3 had C++ → Emscripten → WASM, which is fundamentally different (whole-program C++ compilation, not source-level transpilation).
- No third-party projects found (checked GitHub, Lean Reservoir package registry, NPM).

**This would be the first Lean 4 → TypeScript transpiler.** The novelty is not in the translation mechanics but in the idiomaticity — making output look hand-written.

### Lean 4 Compilation Pipeline (reference)

```
Lean Source
  → Elaboration (type checking, tactic execution)
  → LCNF (Lean Compiler Normal Form) — multiple optimization passes
  → IR (based on λPure/λRc from "Counting Immutable Beans")
  → C code (EmitC) or LLVM IR (EmitLLVM)
  → Native binary
```

The IR is deeply tied to C/native runtime semantics: reference counting (`inc`, `dec`, `isShared`), boxing/unboxing (`lean_box`/`lean_unbox`), tagged pointers, constructor object layout, C closure ABI. None of these have JavaScript equivalents. This confirms that using the LCNF/IR path would produce non-idiomatic output — the surface syntax approach is correct.

### Available Lean 4 Export Formats

| Format | Via | Useful for reverse transpiler? |
|--------|-----|-------------------------------|
| `.olean` (binary) | `lean -o` | No — opaque binary blob |
| `.ilean` (JSON) | `lean -i` | Marginal — only has declaration positions, not structure |
| C source | `lean -c` | No — too low-level, all idiom information destroyed |
| JSON diagnostics | `lean --json` | No — only error/info messages |
| Dependencies | `lean --deps` | Marginal — could help with import graph |
| **Surface syntax** | Read `.lean` files | **Yes — this is the input** |

---

## 8. Reviewer Consensus & Dissent

Three independent reviewers assessed this plan: a compiler architecture expert, a TypeScript idiomaticity expert, and a round-trip/formal methods expert.

### All three reviewers agree on:

1. **Parse surface syntax** — correct decision
2. **Domain-specific, not general** — the idiomaticity comes from exploiting TSLean's narrow conventions
3. **Proof erasure is the easy part** (~60% of code by volume, trivially identified)
4. **The stdlib mapping table is the highest-ROI artifact** — build it first, make it exhaustive
5. **Golden-file tests from day one** — the `Generated/` files with their `-- TypeScript:` comments are ground truth

### Reviewer 1 (Compiler Architecture) — Key Corrections

**Correction adopted: Pattern recognition must happen BEFORE IR lowering.**

> "If you lower to IR first, you destroy the structural information that pattern recognition needs. Consider what happens with `CounterDO.lean`: at the LeanAST level, you can see that `CounterState` is a structure, `increment` operates on `DOMonad CounterState`, and the `get`/`set`/`{ ... with ... }` pattern is a state mutation. If you lower this to a generic IR first, you lose the semantic relationship between the structure and the DOMonad parameter."

**Correction adopted: Consider dropping the separate IR entirely.**

> "You may not need a separate IR at all for the reverse direction. The forward transpiler needs IR because TypeScript has many constructs that must be normalized before mapping to Lean. But Lean-to-TS is a narrowing translation — there are fewer source patterns to handle."

**Strongest recommendation adopted: Hand-tuned parser for known patterns only.**

> "Do not write a general Lean parser. Write a hand-tuned recursive descent parser that handles exactly the patterns present in this library. It will be 1/10th the code and 10x more reliable."

**Strongest recommendation adopted: Declarative stdlib mapping.**

> "Make the stdlib mapping table declarative and comprehensive. Create a single JSON/TS map file. This is the single most impactful thing you can build."

**Warning: Nested with-updates are harder than they look.**

> "The pattern recognizer must understand calling context, not just the function body. `{ r with messages := r.messages ++ [msg] }` requires knowing whether the caller treats the return as a replacement for `r` (mutation) or a new value (functional)."

**Failure mode table from Reviewer 1:**

| Risk | Likelihood | Impact | Mitigation |
|------|-----------|--------|------------|
| Parser cannot handle Lean indentation rules | Medium | Fatal | Hand-tuned parser for known patterns only |
| Pattern recognition after IR lowering loses information | High | Severe | Move recognition before IR (or eliminate IR) |
| Nested with-updates incorrectly converted to mutations | High | Correctness bug | Conservative default: emit spread, not mutation |
| DOMonad functions not correctly associated with classes | Medium | Wrong output structure | Two-pass analysis: classify then aggregate |
| Proof terms leak into generated TS | Medium | Compile errors | Whitelist computational terms, blacklist everything else |
| Forward IR types do not fit reverse direction | High | Wasted effort | Accept separate reverse-specific representation |
| Stdlib mapping incomplete | Medium | Runtime errors | Declarative map, exhaustive testing |

### Reviewer 2 (TypeScript Idiomaticity) — Key Insights

**The ideal outputs are reimaginings, not translations:**

> "The Lean code and the ideal TS code encode fundamentally different computational models. A general Lean-to-TS transpiler would produce functional code. What you want is a domain-aware rewriter that recognizes specific TSLean idioms and emits corresponding Cloudflare Workers patterns."

**Stylistic markers that distinguish hand-written from transpiled TS:**

| Marker | Hand-written | Naive transpiler output |
|--------|-------------|------------------------|
| **Mutation** | `this.count += 1` | `const st2 = { ...st, count: st.count + 1 }; return [result, st2]` |
| **Platform types** | `new Response(body, { status: 200 })` | `{ status: 200, headers: new Map(), body }` |
| **T \| undefined** | `peek(): T \| undefined` | `peek(): { tag: "some", value: T } \| { tag: "none" }` |
| **Property accessors** | `get size(): number` | `size(): number` |
| **No wrappers** | `Math.max(0, x - 1)` | `x > 0 ? x - 1 : 0` |
| **Void not Unit** | `Promise<void>` | `Promise<[void, State]>` |
| **No tuple returns** | Single return value | `[result, newState]` tuples everywhere |
| **Idiomatic names** | `push`, `pop` | `Stack.push`, `Stack.pop` |
| **No intermediate vars** | `return this.count` | `const st = getState(); return st.count` |

**Irreducible gaps identified:**

1. **Multi-return state threading** (`Stack.pop` returns `Option α × Stack α`) — no mechanical fix without linear type analysis
2. **Session types / advanced type-level constructs** — no TS equivalent
3. **Higher-order monadic composition** — requires case-by-case analysis
4. **List operations with `decide` predicates** → plain predicates (API surface change)

**Monad erasure detection algorithm:**

```
IF function type is DOMonad σ α WHERE σ is a known structure:
  Parse the do-block:
    `let st ← get`                      → read all fields from this
    `let st' := { st with f := e }`     → this.f = e
    `set st'`                           → (implicit, already handled)
    `return st'.f`                      → return this.f
    `return expr`                       → return expr
    `set StructName.initial`            → reset all fields to defaults
```

**Edge cases that break monad erasure:**
- Non-trivial field updates: `if st.count > 0 then st.count - 1 else 0` needs semantic pattern matching
- Multiple `get` bindings interleaving reads and writes
- DOMonad composition: `let _ ← increment; increment` requires knowing `increment` is on the same class
- State accessed through nested structures
- `modifyDO f` where `f` updates multiple fields

**Class formation requires three distinct patterns:**
1. **Explicit self:** `def Foo.bar (f : Foo) ...` → `class Foo { bar() { ... } }`
2. **DOMonad state:** `def bar : DOMonad FooState α` in same namespace as `structure FooState` → `class Foo { async bar(): Promise<α> { ... } }`
3. **Static factories:** `def Foo.mk (args) : Foo` → `class Foo { constructor(args) { ... } }` or `static mk(args): Foo`

### Reviewer 3 (Round-Trip Feasibility) — Key Findings

**Metadata recommendation adopted:**

> "Embed structured comment metadata in forward transpiler output. This addresses the biggest information gap (class name and inheritance) with zero impact on verification integrity."

**Scope boundary adopted:**

> "The round-trip MUST be restricted to code produced by the forward transpiler. Generated/ only. Runtime library is a mapping target, not a translation source."

**Round-trip fidelity by file (detailed):**

| File | Fidelity | Key loss |
|------|----------|----------|
| `Hello.lean` | ~90% | Only `repeatStr` rename is wrong |
| `CounterDO.lean` | ~75% | Class name (`CounterDO` vs `CounterState`), base class require metadata |
| `Classes.lean` | ~80% | `Stack.pop` tuple return, API style choices |
| `Interfaces.lean` | ~85% | Typeclasses → TS interfaces need heuristics |
| `RateLimiter.lean` | ~70% | Library wrapper calls need translation table |
| `SessionStore.lean` | ~70% | Library wrapper calls need translation table |
| `ChatRoom.lean` | ~70% | Library wrapper calls need translation table |
| `QueueProcessor.lean` | ~70% | Library wrapper calls need translation table |
| `SelfHost/effects_index.lean` | ~30% | `default` stubs cannot reconstruct original logic |

**Critical observation on what the forward transpiler adds vs. what can be stripped:**

> "Theorems constitute 40-60% of each generated file. They are purely verification artifacts with zero TS semantics. Stripping is safe and necessary. Typeclass instances (`BEq`, `Repr`, `DecidableEq`) have no TS analog. Stripping is safe. Deriving clauses are Lean-specific. Stripping is safe."

> "One critical exception: the `BrandedTypes.lean` branded type wrappers carry semantic information. The reverse transpiler needs the branded type registry to decide whether to emit plain `string` or a branded type alias."

> "Effect annotations DO carry information about whether a function should be `async` — the `async_` effect kind signals this. A reverse transpiler should consult effect annotations BEFORE stripping them."

---

## 9. Implementation Order

### Phase 1 (Foundation): Parser + Analyzer + Proof Erasure

- Hand-tuned Lean subset parser
- Symbol table and declaration classification
- Drop all theorems, instances, proof-carrying fields
- Test: parse every file in `lean/TSLean/Generated/`, verify correct AST

### Phase 2 (Core Patterns): Simple structure/def → TS

- Structure → interface/class
- Zero-arg inductive → string literal union
- Simple `def` → function
- Stdlib type mapping (Nat→number, Option→nullable, List→array)
- Test: `Hello.lean` → idiomatic `hello.ts`

### Phase 3 (Class Extraction): Namespace aggregation

- `structure S` + `def S.method(self: S)` → `class S`
- Constructor detection (`S.new` / `S.initial`)
- Static vs instance method disambiguation
- Test: `Classes.lean` → idiomatic `classes.ts`

### Phase 4 (Monad→Imperative): DOMonad translation

- `DOMonad σ α` → `async method(): Promise<α>`
- `get`/`set` → `this.field` reads/writes
- `{ st with field := val }` → `this.field = val`
- `throwDO`/`catchDO` → `throw`/`try-catch`
- Test: `CounterDO.lean` → idiomatic `counter-do.ts`

### Phase 5 (Polish): Stdlib operations + metadata

- Declarative stdlib mapping table
- Method-style conversions (`AssocMap.insert` → `.set()`)
- Comment metadata extraction for round-trip fidelity
- Forward transpiler modifications to emit `-- @ts-*` annotations
- Test: all `Generated/` files produce clean TS

### Phase 6 (Advanced): Edge cases

- Tuple-return → mutate-and-return
- Nested with-updates
- Branded type detection
- Platform type mapping (HttpResponse → Web Response)

---

## 10. Open Decision Questions

Before implementing, these architectural decisions need to be made:

### Q1: Parser reuse vs. new parser

Should the Lean parser be a new module in the existing `ts-lean-transpiler` project (same repo, new `src/reverse/` directory), or a separate project?

**Arguments for same repo:**
- Reuse `lean-ast.ts` types directly
- Shared test infrastructure
- Single `bun run test` validates both directions
- Forward+reverse transpiler updates stay in sync

**Arguments for separate project:**
- Cleaner separation of concerns
- Independent release cycle
- Forward transpiler contributors don't need to understand reverse

### Q2: Metadata approach

Structured comments in `.lean` files vs. sidecar `.ts-meta.json` files?

**Comments (`-- @ts-class: CounterDO extends DurableObject`):**
- Simpler, cannot get separated from code
- Parseable with regex
- Limited structure

**Sidecar JSON (`CounterDO.ts-meta.json`):**
- Richer structure (nested objects, arrays)
- Can be separated/lost
- Tooling support needed

### Q3: v1.0 target

Should the first milestone be:
- **Option A**: "Parse and reverse `Generated/Hello.lean` to idiomatic TS" (narrow but end-to-end)
- **Option B**: "Parse ALL Generated/ files but emit skeleton-only TS" (broad but shallow)

Option A gives a working demo faster. Option B validates the parser against all patterns first.

### Q4: Stack.pop problem

For tuple-return methods like `Stack.pop : Option α × Stack α`, should the default be:
- **Conservative**: Emit `pop(): [T | undefined, Stack<T>]` — correct but not idiomatic
- **Aggressive**: Emit `pop(): T | undefined` with implicit mutation — idiomatic but requires correctness proof that the returned stack is never used independently

---

## Appendix A: Lean 4 Toolchain Research

### Binaries in `/opt/lean4/lean-4.29.0-linux/bin/`

| Binary | Purpose |
|--------|---------|
| `lean` | Main compiler/elaborator |
| `lake` | Build system (v5.0.0) |
| `leanc` | C compiler wrapper (delegates to bundled clang) |
| `leanchecker` | Independent type checker for `.olean` files |
| `leanmake` | Legacy build tool wrapper |
| `clang` | Bundled LLVM/Clang C compiler |
| `ld.lld` | Bundled LLVM linker |
| `llvm-ar` | LLVM archiver |
| `cadical` | SAT solver (used by `omega` and `bv_decide` tactics) |

### `lean` Output Flags

| Flag | Output | Useful? |
|------|--------|---------|
| `-o` | `.olean` (binary environment blob) | No |
| `-i` | `.ilean` (JSON: decl positions only) | Marginal |
| `-c` | C source | No — too low-level |
| `-b` | LLVM bitcode | No — crashes (LLVM not enabled) |
| `--json` | JSON diagnostics | No — only messages |
| `--deps` | Module dependencies | Marginal — import graph |
| `--stats` | Environment statistics | No |
| `--profile` | Phase timings | No |

### What does NOT exist

| Feature | Status |
|---------|--------|
| AST export (JSON/S-expr) | Does not exist |
| LCNF text export | Does not exist |
| `--export-tlean` | Lean 3 format, does not exist in Lean 4 |
| `--dump` | No such flag |
| LLVM bitcode | Flag exists but crashes (not compiled with `-DLLVM=ON`) |

---

## Appendix B: Detailed File Analysis

### Code vs. Proof Ratios

| File | Definition lines | Theorem lines | Proof % |
|------|-----------------|---------------|---------|
| `Generated/CounterDO.lean` | 39 | 61 | 61% |
| `Generated/Classes.lean` | 50 | 60 | 55% |
| `Generated/Hello.lean` | 24 | 44 | 65% |
| `DurableObjects/Model.lean` | 56 | 116 | 67% |
| `DurableObjects/Http.lean` | 48 | 103 | 68% |
| `Stdlib/HashMap.lean` | ~120 | ~250 | 68% |
| `Runtime/Monad.lean` | ~30 | ~150 | 83% |
| `Runtime/BrandedTypes.lean` | ~50 | ~70 | 58% |

Average: **~65% of every file is theorems/proofs** that must be erased. The reverse transpiler's job is to produce idiomatic TS from the remaining ~35%.

### Key Lean Patterns and Their TS Equivalents

| Lean Pattern | Example | TS Equivalent |
|-------------|---------|---------------|
| `structure X where f : T` | `structure CounterState where count : Nat` | `interface` or class fields |
| `inductive X where \| A \| B` | `inductive HttpMethod where \| GET \| POST` | `type X = "A" \| "B"` |
| `inductive X where \| A (f:T) \| B (g:U)` | `inductive StorageValue where \| svNull \| svBool Bool` | discriminated union |
| `def X.foo (self: X) : T` | `def Counter.increment (c : Counter) : Counter` | instance method |
| `def foo : DOMonad σ α := do ...` | `def increment : DOMonad CounterState Nat := do ...` | `async` class method |
| `let st ← get` | monadic state read | `this.field` |
| `set st'` | monadic state write | `this.field = val` |
| `{ s with f := v }` | functional record update | `this.f = v` (in method context) |
| `match x with \| .A a => ... \| .B b => ...` | pattern match on inductive | `switch` or `if/else` chain |
| `theorem ...` | any theorem | **erased entirely** |
| `instance : BEq X` | typeclass instance | **erased entirely** |
| `deriving Repr, BEq` | auto-derived instances | **erased entirely** |
| `abbrev X := Y` | type alias | `type X = Y` |
| `Option α` | nullable type | `T \| undefined` |
| `List α` | linked list | `T[]` |
| `AssocMap K V` | association list map | `Map<K, V>` |

---

## Appendix C: Full Reviewer Reports

### C.1: Compiler Architecture Review (Reviewer 1)

**Verdict: The plan is 70% right and 30% dangerously wrong.**

The core insight (parse surface syntax, reuse existing types) is correct. But several architectural choices will fail in practice, and the plan underestimates the hardest problems while overestimating some easy ones.

#### On the parser decision

The decisive reason for surface syntax over LCNF/IR is that the Lean library is already written in an idiom-constrained subset. Every file opens with `namespace TSLean.X.Y` and closes with `end TSLean.X.Y`. Structures follow a rigid pattern. Methods follow a rigid pattern. DOMonad functions follow a rigid pattern. Theorems are 100% erasable.

You are not parsing arbitrary Lean 4. You are parsing a dialect. This is a massive advantage, and the plan should make this the central design principle: the parser should reject Lean syntax it does not recognize rather than trying to handle it.

#### On pipeline ordering

The original pipeline had pattern recognition after IR lowering. This is wrong. If you lower to IR first, you destroy the structural information that pattern recognition needs. At the LeanAST level, you can see that `CounterState` is a structure and `increment` operates on `DOMonad CounterState`. If you lower this to a generic IR first, you lose the semantic relationship between the structure and the DOMonad parameter.

The correct pipeline is: LeanAST → Analyzer → PatternRecognizer → (optionally IR) → TSAST → TS text. Or better: skip the IR entirely.

#### On underestimated challenges

1. **The "with-update" → mutation reconstruction is harder than stated.** `ChatRoom.broadcast` is a pure function that returns a new ChatRoom. The idiomatic TS would be `this.messages.push(msg)` inside a class method, but ONLY if the calling context treats the return value as a replacement. The pattern recognizer must understand calling context.

2. **DOMonad erasure is context-dependent.** DOMonad functions should become methods, but `CounterState.initial` is a pure function that should become a static constructor. The distinction is not always clear from the signature alone.

3. **Namespace-to-class aggregation is ambiguous.** Three different class-formation patterns exist: explicit self parameter, implicit DOMonad state, and static factories. Each needs separate handling.

4. **Type erasure has hidden complexity.** `AssocMap` has a `nodup` proof field that must be erased. `DOState σ` has `appState` and `storage` that decompose into different TS locations (class fields vs. `ctx.storage`).

#### On IR reuse

The forward IR types were designed for forward translation. The reverse direction needs representations for class aggregation, monad context, proof erasure boundaries, and library mappings — none of which exist in the forward IR. Recommendation: share type definitions where they overlap, but expect the reverse pipeline to have its own representation.

#### Five concrete changes recommended

1. Drop the separate IR stage — go from annotated LeanAST directly to TSAST
2. Move pattern recognition to the LeanAST level
3. Add an explicit "projection" pass (build TS outline before filling in bodies)
4. Make the stdlib mapping table declarative and comprehensive
5. Build golden-file tests from day one

### C.2: TypeScript Idiomaticity Review (Reviewer 2)

**Overall achievability: ~55-65% genuinely idiomatic, ~80-85% correct-and-readable.**

The ideal outputs are not translations — they are reimaginings. A general Lean-to-TS transpiler would produce functional code. What we want is a domain-aware rewriter that recognizes specific TSLean idioms and emits corresponding Cloudflare Workers patterns.

#### Specific pattern recognitions needed

**Pattern 1: DOMonad→class** — Must recognize structure used as type parameter σ, functions of type DOMonad σ α grouped by shared σ, and do-notation with get/set on that σ. The `CounterDO.lean` pattern is clean and consistent.

**Pattern 2: Functional structure + methods → mutable class** — Must detect that every method takes `(s : Stack α)` as first arg and returns modified `Stack α`. Edge case: `Stack.pop` returns a tuple. No clean TS equivalent without understanding caller context.

**Pattern 3: Zero-arg inductive → string literal union** — Detectable: an inductive where every constructor takes zero arguments. Stylistic choice: string literals rather than enum.

**Pattern 4: Proof erasure** — ~60-70% of codebase by line count is theorems. Easy syntactic detection.

#### The irreducible gaps (most to least severe)

1. **Multi-return state threading** — `Stack.pop` returns `Option α × Stack α`. Converting to mutation requires understanding caller context. A local translation cannot do this.

2. **Monadic composition that doesn't map to async/await** — `catchDO` → try/catch, `liftIO_DO` → just call function, `modifyDO` → computed field update. Each monad operation maps to a different TS construct.

3. **Veil transition system code** — Pure specification. No corresponding TS. Entire module families produce zero output.

4. **AssocMap → native Map** — API translation needed. The `nodup` field must be stripped.

5. **Branded types** — Three possible TS representations, none as natural as Lean.

6. **Higher-order typeclass patterns** — `Serializer` with `roundtrip` proof field has no TS analogue. Must detect which fields are proofs vs. data.

7. **Session types** — `WebSocket.lean` session types have no TS equivalent.

#### Difficulty by conversion pattern

| Pattern | Difficulty | % of codebase |
|---------|-----------|---------------|
| `{ s with field := expr }` → `this.field = expr` | Easy | ~40% of mutators |
| `get` → `this.field` | Easy | ~30% |
| `f :: s.items` → `this.items.unshift(x)` | Medium (List→Array) | ~10% |
| `s.items.filter pred` → `this.items.filter(pred)` | Medium | ~10% |
| Tuple-return state threading | Hard | ~10% |

### C.3: Round-Trip Feasibility Review (Reviewer 3)

**Overall Generated/ fidelity: ~72% without metadata, ~85-88% with metadata.**

#### On stripping verification additions

All verification-only additions can be safely stripped:
- Theorems: 40-60% of each file, purely verification artifacts
- Typeclass instances: no TS analog
- Deriving clauses: Lean-specific
- Proof obligations: compile-time assertions

**Critical exception:** Branded type wrappers carry semantic information. The reverse transpiler needs the branded type registry.

**Effect annotations carry async information:** The `async_` effect kind signals whether a function should be `async`. Consult before stripping.

#### On metadata annotations

Structured comment blocks are recommended. They are invisible to Lean's type checker and proof engine, so verification integrity is unaffected. Custom Lean attributes (`attribute [ts_class ...]`) are problematic — they participate in the elaboration environment.

Recommended format:
```lean
-- @ts-source: src/counter-do.ts
-- @ts-class: CounterDO extends DurableObject
-- @ts-field count: number
-- @ts-method increment: async (): Promise<number>
```

Alternative: sidecar `.ts-meta.json` file per generated `.lean` file avoids polluting Lean source, supports richer structure, but risks separation from the code it describes.

#### On scope limitation

The round-trip MUST be restricted to `Generated/` code. Attempting to reverse-transpile `DOMonad` would produce nonsensical TS — it would try to express `StateT σ (ExceptT TSError IO)` as a TS type. The runtime library types should be recognized and mapped, not reverse-transpiled.

The reverse transpiler should have a library mapping table that serves as the contract between the forward and reverse transpilers:
- `AssocMap K V` → `Map<K, V>`
- `DOMonad σ α` → `async method returning Promise<α>`
- `RateLimiter` → import from Cloudflare runtime
- `List α` → `α[]`
- `Option α` → `α | null`
- `TSError` → `Error` subclasses

#### Detailed fidelity by file

| File | Fidelity | Key loss |
|------|----------|----------|
| `Hello.lean` | ~90% | `repeatStr` rename |
| `CounterDO.lean` | ~75% | Class name, base class need metadata |
| `Classes.lean` | ~80% | `Stack.pop` tuple return |
| `Interfaces.lean` | ~85% | Typeclasses → interfaces heuristics |
| `RateLimiter.lean` | ~70% | Library wrapper translation |
| `SessionStore.lean` | ~70% | Library wrapper translation |
| `ChatRoom.lean` | ~70% | Library wrapper translation |
| `QueueProcessor.lean` | ~70% | Library wrapper translation |
| `SelfHost/effects_index.lean` | ~30% | `default` stubs unreconstructable |

**Bottom line:** The round-trip is feasible for the subset of TS that TSLean targets. With structured metadata annotations, fidelity rises to 85-88% — meaning the generated TS would be functionally equivalent and structurally recognizable, though not textually identical. The remaining 12-15% gap is inherent: formatting choices, method chaining style, ternary vs if/else, and enum numeric values are destroyed by the abstraction gap. This is acceptable for a verification pipeline where the goal is deployment-ready code that has been proven correct, not textually identical reproduction.
