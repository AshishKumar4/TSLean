# TypeScript → Lean 4 Type Mapping

This document describes how TSLean maps TypeScript types to Lean 4 types. The mapping is implemented in `src/typemap/index.ts` (using the TypeScript compiler's `TypeChecker` for fully-resolved types) and `src/codegen/lower.ts` (for IR → Lean AST lowering).

## Primitive Types

| TypeScript | IR Tag | Lean 4 | Notes |
|-----------|--------|--------|-------|
| `number` | `Float` | `Float` | Default mapping; IEEE 754 double in both languages |
| `string` | `String` | `String` | |
| `boolean` | `Bool` | `Bool` | |
| `void` | `Unit` | `Unit` | |
| `undefined` | `Unit` | `Unit` | Standalone; `T \| undefined` maps to `Option T` |
| `null` | `Unit` | `Unit` | Standalone; `T \| null` maps to `Option T` |
| `never` | `Never` | `Empty` | Uninhabited type |
| `any` | `TypeRef("TSAny")` | `TSAny` | Opaque wrapper; see Runtime/Basic.lean |
| `unknown` | `TypeRef("TSAny")` | `TSAny` | Same as `any` — no refinement |
| `bigint` | `Int` | `Int` | Arbitrary-precision integer |
| `symbol` | `String` | `String` | No Lean equivalent; approximated as String |

### Side-by-side: Primitives

```typescript
// TypeScript
const name: string = "alice";
const age: number = 30;
const active: boolean = true;
function noop(): void {}
```
```lean
-- Lean 4
def name : String := "alice"
def age : Float := 30
def active : Bool := true
def noop : Unit := ()
```

## Compound Types

| TypeScript | IR Tag | Lean 4 | Example |
|-----------|--------|--------|---------|
| `T[]` / `Array<T>` | `Array` | `Array T` | `string[]` → `Array String` |
| `[A, B]` | `Tuple` | `A × B` | `[string, number]` → `String × Float` |
| `[A, B, C]` | `Tuple` | `A × B × C` | Right-associated product |
| `Map<K, V>` | `Map` | `AssocMap K V` | Association list (no Mathlib HashMap) |
| `Set<T>` | `Set` | `AssocSet T` | Backed by `Array T` with uniqueness |
| `Record<K, V>` | `Map` | `AssocMap K V` | Same as `Map` |
| `Promise<T>` | `Promise` | `IO T` | Unwrapped to monadic return type |
| `T \| undefined` | `Option` | `Option T` | Nullable pattern |
| `T \| null` | `Option` | `Option T` | Nullable pattern |
| `Result<T, E>` | `Result` | `Except E T` | Note: Lean puts error type first |
| `(a: A) => B` | `Function` | `A → B` | Pure function type |
| `(...) => Promise<B>` | `Function` | `A → IO B` | Async function |

### Side-by-side: Compound Types

```typescript
// TypeScript
const items: string[] = ["a", "b", "c"];
const pair: [string, number] = ["alice", 30];
const lookup: Map<string, number> = new Map();
const tags: Set<string> = new Set();
const maybeName: string | undefined = getName();
```
```lean
-- Lean 4
def items : Array String := #["a", "b", "c"]
def pair : String × Float := ("alice", 30)
def lookup : AssocMap String Float := AssocMap.empty
def tags : AssocSet String := AssocSet.empty
def maybeName : Option String := getName
```

## Discriminated Unions → Inductive Types

When a TypeScript union has a common string-literal discriminant field, TSLean converts it to a Lean `inductive` type. The parser checks fields in order: `kind`, `type`, `tag`, `ok`, `hasValue`, `_type`, `__type`.

### Basic discriminated union

```typescript
// TypeScript
type Shape =
  | { kind: 'circle'; radius: number }
  | { kind: 'rect'; w: number; h: number };
```
```lean
-- Lean 4
inductive Shape where
  | circle (radius : Float)
  | rect (w : Float) (h : Float)
```

### Pattern matching on discriminated unions

```typescript
// TypeScript
function area(s: Shape): number {
  switch (s.kind) {
    case 'circle': return Math.PI * s.radius ** 2;
    case 'rect': return s.w * s.h;
  }
}
```
```lean
-- Lean 4
def area (s : Shape) : Float :=
  match s with
  | Shape.circle radius => 3.141592653589793 * (radius * radius)
  | Shape.rect w h => w * h
```

The rewrite pass (`src/rewrite/index.ts`) transforms `PString("circle")` patterns into `PCtor("Shape.circle", [radius])` and substitutes field accesses (`s.radius` → `radius`) inside match bodies.

### Nested discriminated unions

```typescript
// TypeScript
type Expr =
  | { tag: 'lit'; value: number }
  | { tag: 'add'; left: Expr; right: Expr }
  | { tag: 'neg'; inner: Expr };
```
```lean
-- Lean 4
inductive Expr where
  | lit (value : Float)
  | add (left : Expr) (right : Expr)
  | neg (inner : Expr)
```

Recursive types are handled naturally since Lean's `inductive` supports self-reference.

## Generics

| TypeScript | Lean 4 | Notes |
|-----------|--------|-------|
| `function f<T>(x: T): T` | `def f {T : Type} (x : T) : T` | Implicit type parameter |
| `<T extends string>` | `{T : Type} [ToString T]` | Constraint → type class |
| `<T extends Comparable>` | `{T : Type} [Comparable T]` | Named constraint |
| `<T = string>` | `{T : Type}` | Default type not emitted (TS checker resolves) |
| `<T extends K[]>` | `{T : Type}` | Complex constraints simplified |

### Side-by-side: Generics

```typescript
// TypeScript
function identity<T>(x: T): T {
  return x;
}

function first<T>(arr: T[]): T | undefined {
  return arr[0];
}

interface Container<T> {
  value: T;
  map<U>(f: (x: T) => U): Container<U>;
}
```
```lean
-- Lean 4
def identity {T : Type} (x : T) : T := x

def first {T : Type} (arr : Array T) : Option T :=
  arr.get? 0

structure Container (T : Type) where
  value : T

def Container.map {T U : Type} (self : Container T) (f : T → U) : Container U :=
  { value := f self.value }
```

### Generic type applications

```typescript
// TypeScript
const result = identity<string>("hello");
const items = new Array<number>();
```
```lean
-- Lean 4
def result := @identity String "hello"
def items : Array Float := #[]
```

## Utility Types

| TypeScript | Lean 4 | Status | Notes |
|-----------|--------|--------|-------|
| `Readonly<T>` | `T` | Transparent | Lean is immutable by default |
| `NonNullable<T>` | `T` | Transparent | Strips Option wrapper |
| `Required<T>` | `T` | Transparent | All fields required by default |
| `Record<K, V>` | `AssocMap K V` | Supported | Maps to association list |
| `Partial<T>` | (resolved concretely) | Partial | TS checker resolves; generic uses → `sorry` |
| `Pick<T, K>` | (resolved concretely) | Partial | TS checker resolves; generic uses → `sorry` |
| `Omit<T, K>` | (resolved concretely) | Partial | TS checker resolves; generic uses → `sorry` |
| `ReturnType<F>` | (resolved concretely) | Partial | TS checker resolves; generic uses → `sorry` |
| `Parameters<F>` | (resolved concretely) | Partial | TS checker resolves; generic uses → `sorry` |
| `Exclude<T, U>` | (resolved concretely) | Partial | TS checker resolves; generic uses → `sorry` |
| `Extract<T, U>` | (resolved concretely) | Partial | TS checker resolves; generic uses → `sorry` |

The "partial" utility types work when the TypeScript compiler can fully resolve them at the call site. When they appear in generic positions (where the checker cannot resolve the concrete type), the lowerer emits `sorry` with a tracked entry.

## Effects → Monad Stack

The effect system maps TypeScript side-effect patterns to Lean 4 monad transformer stacks:

| TypeScript Pattern | Detected Effect | Lean 4 Return Type |
|-------------------|-----------------|---------------------|
| Pure function (no side effects) | `Pure` | `T` |
| `async function f(): Promise<T>` | `Async` | `IO T` |
| `function f() { throw new Error(...) }` | `Except` | `ExceptT String IO T` |
| Mutable state (`let x = 0; x = 1;`) | `State` | `StateT Unit IO T` |
| `console.log(...)` / `fetch(...)` | `IO` | `IO T` |
| Combined async + throw | `Combined` | `ExceptT String IO T` |
| Combined state + throw | `Combined` | `StateT S (ExceptT String IO T)` |
| Combined state + throw + async | `Combined` | `StateT S (ExceptT String IO T)` |

### Side-by-side: Effects

```typescript
// TypeScript — pure
function add(a: number, b: number): number {
  return a + b;
}
```
```lean
-- Lean 4 — pure (no monad)
def add (a : Float) (b : Float) : Float := a + b
```

```typescript
// TypeScript — async
async function fetchData(url: string): Promise<string> {
  const res = await fetch(url);
  return res.text();
}
```
```lean
-- Lean 4 — IO monad
def fetchData (url : String) : IO String := do
  let res ← WebAPI.fetch url
  pure res
```

```typescript
// TypeScript — throws
function parseAge(s: string): number {
  const n = parseInt(s);
  if (isNaN(n)) throw new Error("invalid age");
  return n;
}
```
```lean
-- Lean 4 — ExceptT
def parseAge (s : String) : ExceptT String IO Float := do
  let n := s.toNat?.getD 0
  if Float.isNaN n then throw "invalid age"
  pure n
```

### Durable Object monad

Cloudflare Durable Object classes use a specialized `DOMonad S` type, which is `StateT S (ExceptT TSError IO)`:

```typescript
// TypeScript
class Counter implements DurableObject {
  private count: number = 0;
  async fetch(req: Request): Promise<Response> {
    this.count++;
    return new Response(String(this.count));
  }
}
```
```lean
-- Lean 4
structure CounterState where
  count : Float := 0

def Counter.fetch (req : Request) : DOMonad CounterState Response := do
  let s ← get
  set { s with count := s.count + 1 }
  pure (Response.mk (toString s.count))
```

## Classes → Structures

TypeScript classes map to Lean `structure` types. Methods become namespaced `def` declarations. Mutable state fields (modified in methods) are modeled via the state monad.

```typescript
// TypeScript
class Point {
  constructor(public x: number, public y: number) {}
  distanceTo(other: Point): number {
    const dx = this.x - other.x;
    const dy = this.y - other.y;
    return Math.sqrt(dx * dx + dy * dy);
  }
}
```
```lean
-- Lean 4
structure Point where
  x : Float
  y : Float

def Point.distanceTo (self : Point) (other : Point) : Float :=
  let dx := self.x - other.x
  let dy := self.y - other.y
  Float.sqrt (dx * dx + dy * dy)
```

## Enums → Inductive Types

```typescript
// TypeScript
enum Color { Red, Green, Blue }
enum Direction { Up = "UP", Down = "DOWN" }
```
```lean
-- Lean 4
inductive Color where
  | Red | Green | Blue

inductive Direction where
  | Up | Down
```

## Interfaces → Structures

```typescript
// TypeScript
interface User {
  name: string;
  age: number;
  email?: string;
}
```
```lean
-- Lean 4
structure User where
  name : String
  age : Float
  email : Option String := none
```

Optional fields (`?`) become `Option T` with a `none` default.

## What Is NOT Supported

These TypeScript type-level features have no Lean 4 equivalent and will produce `sorry` or a simplified approximation:

| TypeScript Feature | Reason | What Happens |
|-------------------|--------|--------------|
| `T extends (...) => infer R ? R : never` | `infer` has no Lean equivalent | Concrete uses resolved by checker; generic uses → `sorry` |
| `{ [K in keyof T]: ... }` | No `keyof` operator | Concrete uses resolved; generic → `sorry` |
| `` type E = `on${string}` `` | Template literal types | Maps to `String` (no refinement) |
| `T extends U ? A : B` (distributive) | Conditional type distribution | Resolved true branch used; distribution → `sorry` |
| `typeof x` (type position) | Runtime reflection | Maps to `String` or `sorry` |
| `T & U` (non-branded) | Structural subtyping | First type used; properties may be lost |
| `(number & {})` | Quirky TS patterns | Simplified to base type |
