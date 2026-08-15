<p align="center">
  <h1 align="center">TSLean</h1>
  <p align="center">
    <strong>TypeScript → Lean 4 transpiler under semantic reconstruction</strong>
  </p>
  <p align="center">
    <a href="#quick-start">Quick Start</a> &bull;
    <a href="#examples">Examples</a> &bull;
    <a href="#features">Features</a> &bull;
    <a href="docs/architecture.md">Architecture</a> &bull;
    <a href="docs/limitations.md">Limitations</a>
  </p>
</p>

---

![License](https://img.shields.io/badge/license-MIT-green)

## Status

TSLean is under reconstruction and currently supports an evolving TypeScript/ECMAScript subset. The semantic corpus is checked-in red evidence of known incorrect or unsupported behavior, not a completeness score. Legacy Lean runtime and stub declarations still use `sorry`; no formal soundness, completeness, or application-correctness claim is made.

Current revision, toolchain, test, corpus, todo, Lean job, and content-hash evidence is generated in [`evidence/baseline-manifest.json`](evidence/baseline-manifest.json). See the [rebuild plan](docs/REBUILD_PLAN.md) and [evidence ledger](EVIDENCE.md).

## What is TSLean?

TSLean converts a supported subset of typed TypeScript into Lean 4 code. Generated code can be checked by Lean, but the current compiler pipeline does not establish that the TypeScript program or generated model is correct.

It ships with:
- A Lean runtime library with models for Cloudflare Durable Objects
- JS standard library mappings for String, Array, Map, Set, Math, Promise, JSON, and Date operations
- **npm type stubs** for node:fs, node:path, node:http, console, process
- 7 Durable Object models with safety invariant theorems

The implemented subset includes functions, classes, interfaces, enums, generics, discriminated unions, async/await, exceptions, and multi-file modules, with known semantic gaps tracked in the corpus.

## Quick Start

```bash
git clone https://github.com/AshishKumar4/TSLean.git
cd TSLean && bun install
```

**Transpile a file:**

```bash
$ bun run src/cli.ts examples/01-hello-world/hello.ts -o output.lean
✓ examples/01-hello-world/hello.ts → output.lean
```

**Input** (`hello.ts`):
```typescript
function greet(name: string): string {
  return `Hello, ${name}!`;
}

function add(a: number, b: number): number {
  return a + b;
}

const greeting = greet("world");
```

**Output** (`output.lean`):
```lean
import TSLean.Runtime.Basic

namespace TSLean.Generated.Hello

def greet (name : String) : String := s!"Hello, {name}!"

def add (a : Float) (b : Float) : Float := a + b

def greeting : String := greet "world"

end TSLean.Generated.Hello
```

**Transpile a project:**

```bash
$ bun run src/cli.ts compile --project tsconfig.json -o lean/Generated/
[1/5] Reading project configuration
[2/5] Building dependency graph
[3/5] Transpiling types.ts → Types.lean
[4/5] Transpiling cart.ts → Cart.lean
[5/5] Done

✓ 2 file(s) transpiled, lakefile generated (0.3s)
```

**Build and verify the Lean library:**

```bash
$ cd lean && lake build
```

## Examples

10 examples from basics to advanced patterns — see the [examples/](examples/) directory:

| # | Topic | What it shows |
|---|-------|--------------|
| [01](examples/01-hello-world/) | Hello World | Pure functions, constants, string interpolation |
| [02](examples/02-types-and-interfaces/) | Types & Interfaces | Structures, optional fields, type aliases |
| [03](examples/03-classes/) | Classes | State as structures, methods as namespaced functions |
| [04](examples/04-generics/) | Generics | Implicit type params, constraints → type classes |
| [05](examples/05-error-handling/) | Error Handling | try/catch/finally → tryCatch/ExceptT |
| [06](examples/06-async/) | Async/Await | IO monad, do-notation, Promise unwrapping |
| [07](examples/07-modules/) | Multi-File Modules | Cross-file imports, dependency resolution |
| [08](examples/08-discriminated-unions/) | Discriminated Unions | Inductive types, exhaustive pattern matching |
| [09](examples/09-real-world/) | Real-World Patterns | Todo API, config parser, event system |
| [10](examples/10-advanced/) | Limitations | typeof → sorry, regex stubs, --strict flag |

## Features

### Type System

| TypeScript | Lean 4 | Notes |
|-----------|--------|-------|
| `number` | `Float` | `Nat`/`Int` when context implies |
| `string` | `String` | |
| `boolean` | `Bool` | |
| `T[]` / `Array<T>` | `Array T` | |
| `Map<K, V>` | `AssocMap K V` | Verified association list |
| `T \| undefined` | `Option T` | |
| `Promise<T>` | `IO T` | Unwrapped to monadic return |
| `Record<K, V>` | `AssocMap K V` | |
| `interface Foo { ... }` | `structure Foo where ...` | |
| Discriminated union | `inductive Foo where ...` | Auto-detected discriminant |

### Generics & Constraints

```typescript
function sort<T extends Comparable>(arr: T[]): T[] { ... }
```
```lean
def sort {T : Type} [Comparable T] (arr : Array T) : Array T := ...
```

| TypeScript | Lean 4 |
|-----------|--------|
| `<T>` | `{T : Type}` |
| `<T extends string>` | `{T : Type} [ToString T]` |
| `<T extends Comparable>` | `{T : Type} [Comparable T]` |
| `<A, B, C>` | `{A B C : Type}` |

### Effect System

The transpiler currently maps detected effects to these Lean shapes. Combined stacks describe the intended mapping; effect discovery and propagation are not yet reliable for every supported construct.

| Pattern | Mapping | Lean 4 |
|---------|---------|--------|
| No detected effects | Current | `def f (x : T) : U` |
| `async/await` | Current | `def f (x : T) : IO U` |
| `throw/try/catch` | Current when detected | `def f (x : T) : ExceptT String (IO U)` |
| Mutable state | Intended | `def f (x : T) : StateT S (IO U)` |
| State, exceptions, and IO | Intended composition | `def f : StateT S (ExceptT E (IO U))` |

Known propagation gaps include forward and parenthesized calls, higher-order, stored, indexed, destructured, and reassigned callbacks, callback effects mixed with direct IO, and effectful logical operands. These cases can leave callers incorrectly pure, discard actions, or produce ill-typed Lean; they are tracked in [`spec/corpus/counterexamples.json`](spec/corpus/counterexamples.json), especially the `effects/callbacks` group and `operators-effectful-compound-condition`.

### Discriminated Unions → Pattern Matching

```typescript
type Shape =
  | { kind: 'circle'; radius: number }
  | { kind: 'rect'; width: number; height: number };

function area(s: Shape): number {
  switch (s.kind) {
    case 'circle': return Math.PI * s.radius * s.radius;
    case 'rect':   return s.width * s.height;
  }
}
```

```lean
inductive Shape where
  | circle (radius : Float)
  | rect (width : Float) (height : Float)

def area (s : Shape) : Float :=
  match s with
  | .circle radius => 3.141592653589793 * radius * radius
  | .rect width height => width * height
```

### Error Handling

```typescript
function safeDivide(a: number, b: number): number {
  try {
    if (b === 0) throw new Error("Division by zero");
    return a / b;
  } catch (e) {
    return 0;
  } finally {
    console.log("done");
  }
}
```

```lean
def safeDivide (a b : Float) : ExceptT String (IO Float) := do
  let _tc_result ← tryCatch
    (do if b == 0 then throw "Division by zero"
        pure (a / b))
    (fun _e => pure 0)
  IO.println "done"
  pure _tc_result
```

### Classes → Structures + Methods

```typescript
class Counter {
  private count: number = 0;
  increment(): void { this.count++; }
  getCount(): number { return this.count; }
}
```

```lean
structure CounterState where
  count : Float := 0

def Counter.increment (self : CounterState) : CounterState :=
  { self with count := self.count + 1 }

def Counter.getCount (self : CounterState) : Float := self.count
```

## Architecture

```
TypeScript Source (.ts)
        │
   ┌────▼─────┐
   │  Parser   │◄── ts.TypeChecker (full type resolution)
   └────┬──────┘
        │ IRModule (types, effects, expressions)
   ┌────▼──────┐
   │  Rewrite  │    Discriminated unions → pattern matching
   └────┬──────┘
        │ IRModule (normalized)
   ┌────▼──────┐
   │  Lower    │    IR → LeanAST (type classes, monad stacks)
   └────┬──────┘
        │ LeanFile (LeanDecl[], LeanExpr[], LeanTy[])
   ┌────▼──────┐
   │  Printer  │    LeanAST → valid Lean 4 source text
   └────┬──────┘
        │
   Output (.lean)
```

For multi-file projects, the pipeline adds: tsconfig.json parsing → dependency graph (Tarjan SCC) → topological sort → parallel transpilation → lakefile generation.

See [docs/architecture.md](docs/architecture.md) for the full design.

## CLI Reference

```
tslean compile <file|dir>  [options]   Transpile TypeScript to Lean 4
tslean init [dir]                      Scaffold a new tslean project
```

| Flag | Description |
|------|-------------|
| `-o, --output <path>` | Output file or directory |
| `-w, --watch` | Watch for changes and recompile |
| `--lake` | Auto-run `lake build` after each recompile |
| `--strict` | Reject output containing `sorry`/`default` placeholders (single-file and project mode) |
| `--timing` | Show phase-by-phase timing breakdown |
| `--verify` | Generate proof obligations |
| `--project <path>` | Use tsconfig.json for multi-file compilation |
| `--namespace <ns>` | Root Lean namespace (default: `TSLean.Generated`) |
| `--lakefile` / `--no-lakefile` | Generate/skip lakefile.toml and root module |
| `--no-color` | Disable colored output |

## Standard Library Coverage

The current library contains mappings across these categories. A mapping's presence does not establish ECMAScript semantic equivalence:

| Category | Methods | Examples |
|----------|---------|---------|
| **String** (30) | length, toUpperCase, toLowerCase, trim, includes, indexOf, slice, split, replace, repeat, padStart, padEnd... | `s.includes(x)` → `TSLean.Stdlib.String.includes s x` |
| **Array** (35) | map, filter, reduce, find, sort, splice, flat, flatMap, push, pop, some, every, includes, indexOf, reverse... | `a.map(f)` → `Array.map f a` |
| **Map** (10) | get, set, has, delete, size, keys, values, entries, forEach, clear | `m.get(k)` → `AssocMap.find? m k` |
| **Set** (9) | add, has, delete, size, keys, values, entries, forEach, clear | `s.has(x)` → `AssocSet.contains s x` |
| **Math** (25+) | floor, ceil, sqrt, abs, sin, cos, tan, log, exp, pow, PI, E, random... | `Math.sqrt(x)` → `Float.sqrt x` |
| **Async** (9) | Promise.all, Promise.race, Promise.allSettled, Promise.any, setTimeout... | `Promise.all(xs)` → `TSLean.Stdlib.Async.promiseAll xs` |

Plus: JSON.parse/stringify, Date basics, parseInt/parseFloat, Number.isNaN/isFinite/isInteger.

See [docs/stdlib-reference.md](docs/stdlib-reference.md) for the complete mapping table.

## Verification Library

The `lean/` directory is a pure Lean library (**no Mathlib**, no external dependencies). It still contains legacy `sorry`-backed runtime and stub declarations:

- **Runtime types**: `TSValue`, `TSError`, `DOMonad`, branded types, coercions
- **Verified stdlib**: `AssocMap` (with `Nodup` proof), bounds-checked arrays
- **7 DO models**: Counter, Auth, RateLimiter, ChatRoom, Queue, SessionStore, Analytics
- **Transition systems**: Each DO modeled as a state machine with safety invariant proofs

```lean
-- Rate limiter never exceeds configured limit
theorem never_exceeds_limit (rl : RateLimiter) (now : Nat) :
    (cleanup rl now).window.length ≤ rl.maxRequests

-- Revoked tokens cannot authenticate
theorem revoked_cannot_authenticate (st : AuthState) (tok : Token) (now : Nat)
    (s : Session) (hfind : st.find tok = some s) (hrev : s.status = .revoked) :
    authenticate st tok now = none

-- ACID transactions: read-own-write
theorem read_own_write (tx : Transaction) (k : String) (v : StorageValue) :
    (write tx k v).read k = some v
```

## Node.js Stubs

Pre-built Lean stubs for common Node.js APIs (axiomatized for verification):

| Module | Functions |
|--------|-----------|
| **node:fs** | readFileSync, writeFileSync, existsSync, mkdirSync, readdirSync, statSync |
| **node:path** | join, resolve, dirname, basename, extname, relative, normalize |
| **node:http** | createServer, request, Method/IncomingMessage/ServerResponse types |
| **console** | log, error, warn, info, debug, time, timeEnd, assert, table, trace |
| **process** | env, argv, exit, cwd, stdout, stderr, stdin, platform, arch |

Unknown npm packages have no stub path: an import that resolves to none of the above keeps its name as `TSLean.External.<Name>`, which the lowerer then declines to emit as an import.

## Limitations

TSLean is honest about what it can and cannot express. Some TypeScript features have no Lean 4 equivalent:

| Pattern | Status | Workaround |
|---------|--------|-----------|
| `typeof x === 'string'` | `sorry` | Use discriminated unions |
| `text.match(/regex/)` | Stub | Use string operations |
| `Partial<T>` (generic) | `sorry` | Concrete types resolve fine |
| `ReturnType<F>` (generic) | `sorry` | Concrete types resolve fine |
| Generators / `yield` | `sorry` | Use arrays or recursion |

Use `--strict` to reject any output that carries a `sorry` or `default` placeholder — the check scans the emitted Lean, so it also catches placeholders the lowerer never recorded. See [docs/limitations.md](docs/limitations.md) for the full list.

## Documentation

| Document | Description |
|----------|-------------|
| [Architecture](docs/architecture.md) | Pipeline design, module descriptions, data flow |
| [Type Mapping](docs/type-mapping.md) | Current TS → Lean type mappings |
| [Stdlib Reference](docs/stdlib-reference.md) | Every mapped JS method with Lean function |
| [Limitations](docs/limitations.md) | What can't work, error codes, workarounds |
| [Contributing](docs/contributing.md) | Dev setup, how to add features, commit style |
| [Examples](examples/) | 10 worked examples from hello world to advanced |

## Building

**Requirements:** Node.js ≥ 18, Bun, Lean 4.29.0

```bash
bun install              # Install dependencies
bun run verify           # Format, lint, tests, TypeScript build, and Lean build
```

## Project Stats

Current measured counts are generated in [`evidence/baseline-manifest.json`](evidence/baseline-manifest.json) rather than duplicated here. Historical Agents SDK transpilation runs are not completeness or correctness evidence.

## License

MIT

---

*Built for the Cloudflare Formal Verification Prize.*
