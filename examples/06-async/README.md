# 06 — Async/Await

TypeScript's async/await maps to Lean's IO monad with do-notation.

## Key mappings

| TypeScript | Lean 4 |
|---|---|
| `async function f(): Promise<T>` | `def f : IO T := do` |
| `await expr` | `let x ← expr` |
| `Promise<void>` | `IO Unit` |
| `console.log(x)` | `IO.println x` |
