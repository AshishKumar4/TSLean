# 04 — Generics

Generic functions and types map to Lean's implicit type parameters and type classes.

## Key mappings

| TypeScript | Lean 4 |
|---|---|
| `function f<T>(x: T): T` | `def f {T : Type} (x : T) : T` |
| `interface Box<T> { value: T }` | `structure Box (T : Type) where value : T` |
| `<A, B>` | `{A B : Type}` |
| `<T extends string>` | `{T : Type} [ToString T]` |
