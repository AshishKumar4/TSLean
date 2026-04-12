# TypeScript → Lean 4 Type Mapping

## Primitive Types

| TypeScript | Lean 4 | Notes |
|-----------|--------|-------|
| `number` | `Float` | Default; `Nat` or `Int` when context implies |
| `string` | `String` | |
| `boolean` | `Bool` | |
| `void` / `undefined` | `Unit` | |
| `null` | `Unit` | |
| `never` | `Empty` | |
| `any` / `unknown` | `String` | Fallback approximation |
| `bigint` | `Int` | |
| `symbol` | `String` | No Lean equivalent |

## Compound Types

| TypeScript | Lean 4 | Example |
|-----------|--------|---------|
| `T[]` / `Array<T>` | `Array T` | `string[]` → `Array String` |
| `[A, B]` | `A × B` | Lean product type |
| `Map<K, V>` | `AssocMap K V` | Association list map |
| `Set<T>` | `Array T` | No native set in pure Lean |
| `Record<K, V>` | `AssocMap K V` | |
| `Promise<T>` | `IO T` | Unwrapped to monadic return |
| `T \| undefined` / `T \| null` | `Option T` | |
| `Result<T, E>` | `Except E T` | |
| `(a: A) => B` | `A → B` | Pure functions |
| `(...) => Promise<B>` | `A → IO B` | Async functions |

## Discriminated Unions

```typescript
type Shape = { kind: 'circle'; radius: number } | { kind: 'rect'; w: number; h: number };
```
→
```lean
inductive Shape where
  | circle (radius : Float)
  | rect (w : Float) (h : Float)
```

The discriminant field (`kind`, `type`, `tag`) is detected automatically.

## Generics

| TypeScript | Lean 4 |
|-----------|--------|
| `function f<T>(x: T): T` | `def f {T : Type} (x : T) : T` |
| `<T extends string>` | `{T : Type} [ToString T]` |
| `<T extends Comparable>` | `{T : Type} [Comparable T]` |
| `<T = string>` (default) | `{T : Type}` (default not emitted) |

## Utility Types

| TypeScript | Lean 4 | Notes |
|-----------|--------|-------|
| `Readonly<T>` | `T` | Transparent (Lean is immutable) |
| `NonNullable<T>` | `T` | Strips Option wrapper |
| `Required<T>` | `T` | Transparent |
| `Record<K, V>` | `AssocMap K V` | |
| `Partial<T>` | `sorry` (generic) | Resolved concretely by checker |
| `Pick<T, K>` | `sorry` (generic) | Resolved concretely by checker |
| `ReturnType<F>` | `sorry` (generic) | Resolved concretely by checker |

## Effects (Monad Stack)

| TypeScript Pattern | Lean 4 Effect |
|-------------------|---------------|
| `async function f(): Promise<T>` | `def f : IO T` |
| `function f() { throw ... }` | `def f : ExceptT String (IO T)` |
| `let mut x = 0; x = 1;` | `def f : StateT Unit (IO T)` |
| Combined async + throw + state | `def f : StateT S (ExceptT E (IO T))` |
| Pure function | `def f : T` |

## Classes → Structures

```typescript
class Counter {
  private count: number = 0;
  increment(): void { this.count++; }
  getCount(): number { return this.count; }
}
```
→
```lean
structure CounterState where
  count : Float := 0

def Counter.increment (self : CounterState) : CounterState :=
  { self with count := self.count + 1 }

def Counter.getCount (self : CounterState) : Float := self.count
```
