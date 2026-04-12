# TSLean

**A TypeScript to Lean 4 transpiler with formal verification for Cloudflare Durable Objects.**

TSLean converts typed TypeScript into compilable, verifiable Lean 4 code. Write your application in TypeScript, transpile to Lean 4, and get machine-checked proofs that your system is correct. Ships with a complete runtime library modeling Durable Objects as verified state machines.

## Highlights

- **Full TypeScript coverage**: functions, classes, interfaces, enums, generics with constraints, discriminated unions, async/await, try/catch/finally, modules
- **Effect inference**: automatically detects IO, state mutation, exceptions and assigns the correct monad stack
- **112 Lean build jobs**, zero `sorry` in the runtime library
- **1540+ tests** with 9/10 fixpoint (TS and Lean pipelines produce identical output)
- **Multi-file support**: reads `tsconfig.json`, topological sort, lakefile generation
- **npm type stubs**: .d.ts reader + pre-built stubs for node:fs, node:path, node:http, console, process
- **Self-hosting**: TSLean can transpile all of its own 12 source modules to Lean 4

## Quick Start

```bash
git clone https://github.com/AshishKumar4/TSLean.git
cd TSLean && bun install

# Transpile a single file
npx tsx src/cli.ts compile counter.ts -o counter.lean

# Transpile a project
npx tsx src/cli.ts compile --project tsconfig.json -o lean/Generated/

# Watch mode with auto-rebuild
npx tsx src/cli.ts compile src/ -o lean/Generated/ --watch --lake

# Run tests
bun run test

# Build Lean library (requires Lean 4.29.0)
cd lean && lake build
```

## Type Translations

| TypeScript | Lean 4 |
|---|---|
| `interface Point { x: number; y: number }` | `structure Point where x : Float; y : Float` |
| `type Shape = { kind: "circle"; r: number } \| ...` | `inductive Shape where \| circle (r : Float) \| ...` |
| `type UserId = string & { __brand: "UserId" }` | `structure UserId where val : String deriving BEq` |
| `function f<T extends Comparable>(x: T): T` | `def f {T : Type} [Comparable T] (x : T) : T` |
| `Promise<T>` | `IO T` |
| `T \| undefined` | `Option T` |
| `Map<string, number>` | `AssocMap String Float` |
| `async function f()` | `def f : IO Unit := do ...` |
| `try { ... } catch (e) { ... } finally { ... }` | `tryCatch (do ...) (fun e => ...) + let cleanup` |
| `x?.prop` | `x.bind (fun v => v.prop)` |
| `a ?? b` | `a.getD b` |

## Effect System

| TypeScript Pattern | Lean 4 Monad |
|---|---|
| Pure functions | Direct (no monad) |
| `async/await` | `IO` |
| `throw/try/catch` | `ExceptT String (IO T)` |
| Mutable state | `StateT S (IO T)` |
| Combined | `StateT S (ExceptT E (IO T))` |
| Durable Object methods | `DOMonad S T = StateT S (ExceptT TSError IO) T` |

## Architecture

```
TypeScript Source (.ts)
        |
   [ Parser ] ---- ts.TypeChecker (full type resolution)
        |
   IR (types, effects, expressions)
        |
   [ Rewrite ] ---- discriminated unions, pattern normalization
        |
   [ Lower ] ---- IR -> LeanAST (type classes, monad stacks)
        |
   [ Print ] ---- LeanAST -> valid Lean 4 source
        |
   Output (.lean)
```

See [docs/architecture.md](docs/architecture.md) for the full design.

## CLI

```
tslean compile <file|dir>  [options]   Transpile TypeScript to Lean 4
tslean self-host                       Run the self-hosting pipeline
tslean verify                          Run fixpoint verification
tslean init [dir]                      Scaffold a new tslean project
```

| Flag | Description |
|---|---|
| `-o, --output <path>` | Output file or directory |
| `-w, --watch` | Watch for changes and recompile |
| `--lake` | Auto-run `lake build` after each recompile (watch mode) |
| `--strict` | Error on `sorry` instead of continuing |
| `--verify` | Generate proof obligations |
| `--project <path>` | Use tsconfig.json for multi-file compilation |
| `--namespace <ns>` | Root Lean namespace (default: `TSLean.Generated`) |
| `--lakefile` / `--no-lakefile` | Generate/skip lakefile.toml |

## Standard Library

Complete coverage of the JS standard library:

- **String**: 30 methods (includes, indexOf, slice, split, replace, trim, pad, repeat...)
- **Array**: 35 methods (map, filter, reduce, find, sort, splice, flat, flatMap...)
- **Map/Set**: full CRUD + iteration (get, set, has, delete, keys, values, entries, forEach, clear)
- **Math**: all functions (floor, ceil, sqrt, sin, cos, log, pow, random, PI, E...)
- **Number**: isNaN, isFinite, isInteger, parseInt, parseFloat, MAX_SAFE_INTEGER...
- **Promise**: all, race, allSettled, any, resolve, reject
- **JSON**: parse (via Lean.Json), stringify
- **Date**: basic timestamp operations
- **Node.js stubs**: fs, path, http, console, process (axiomatized for verification)

See [docs/stdlib-reference.md](docs/stdlib-reference.md) for the complete mapping table.

## Verification Library

The `lean/` directory is a pure Lean 4.29 library (no Mathlib, no external dependencies):

- **Runtime types and monads** -- `TSValue`, `TSError`, `DOMonad`, branded types, coercions
- **Verified standard library** -- `AssocMap` (with `Nodup` proof), bounds-checked arrays, option/result composition
- **7 Durable Object models** -- Counter, Auth, RateLimiter, ChatRoom, Queue, SessionStore, Analytics
- **Transition system verification** -- each DO modeled as a state machine with safety invariant proofs

```lean
-- Rate limiter never exceeds configured limit
theorem never_exceeds_limit (rl : RateLimiter) (now : Nat) :
    (cleanup rl now).window.length <= rl.maxRequests

-- Revoked tokens cannot authenticate
theorem revoked_cannot_authenticate (st : AuthState) (tok : Token) (now : Nat)
    (s : Session) (hfind : st.find tok = some s) (hrev : s.status = .revoked) :
    authenticate st tok now = none

-- ACID transactions: read-own-write
theorem read_own_write (tx : Transaction) (k : String) (v : StorageValue) :
    (write tx k v).read k = some v
```

## Limitations

Some TypeScript features have no Lean 4 equivalent:

- **Conditional types with `infer`** -- `ReturnType<T>`, `Parameters<T>` (concrete uses resolve; generic uses emit `sorry`)
- **Mapped types with `keyof`** -- `Partial<T>`, `Pick<T, K>` (concrete uses resolve)
- **typeof / instanceof** -- use discriminated unions with tag fields instead
- **Generators / yield** -- use arrays or explicit recursion
- **RegExp** -- opaque stub (test/match return defaults)

See [docs/limitations.md](docs/limitations.md) for the full list with error codes and workarounds.

## Documentation

- [Architecture](docs/architecture.md) -- pipeline design, module descriptions
- [Type Mapping](docs/type-mapping.md) -- complete TS-to-Lean type table
- [Standard Library](docs/stdlib-reference.md) -- every mapped JS method
- [Limitations](docs/limitations.md) -- what can't work and why
- [Contributing](docs/contributing.md) -- dev setup, how to add features

## Building

**Requirements:** Node.js >= 18, Bun, Lean 4.29.0

```bash
bun run build     # Compile to dist/
bun run test      # 1540+ tests
bun run lint      # tsc --noEmit + eslint
cd lean && lake build  # 112 Lean build jobs
```

## License

MIT
