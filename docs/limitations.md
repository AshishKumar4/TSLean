# TSLean Limitations

An honest accounting of what TSLean cannot do, what it does imperfectly, workarounds for each limitation, and what is planned for future improvement.

## Fundamentally Inexpressible in Lean 4

These TypeScript features use type-level computation that has no equivalent in Lean 4's type system. They will never produce fully faithful translations — the gap is inherent to the target language.

### Conditional Types with `infer`

```typescript
type ReturnType<T> = T extends (...args: any[]) => infer R ? R : never;
type ElementType<T> = T extends (infer E)[] ? E : never;
```

The `infer` keyword performs pattern matching on type structure at the type level. Lean's type system has dependent types but no mechanism for destructuring arbitrary types to extract components.

**What happens:** When the TypeScript checker can resolve the concrete instantiation (e.g., `ReturnType<typeof myFunc>` where `myFunc` has a known signature), the resolved concrete type is used. When the type appears generically (e.g., `function f<T>(x: ReturnType<T>)`), the lowerer emits `sorry`.

**Workaround:** Use explicit type parameters instead of `infer`-based utility types. Write `function f<R>(x: R)` instead of `function f<T>(x: ReturnType<T>)`.

### Mapped Types with `keyof`

```typescript
type Partial<T> = { [K in keyof T]?: T[K] };
type ReadonlyMap<T> = { readonly [K in keyof T]: T[K] };
```

Lean has no `keyof` operator and no mechanism for iterating over the fields of a structure at the type level. There is no way to express "for each field in T, produce a corresponding field in the output type."

**What happens:** Same as conditional types — concrete instantiations resolved by the checker work; generic uses emit `sorry`.

**Workaround:** Define concrete types directly rather than deriving them with mapped types.

### Template Literal Types

```typescript
type EventName = `on${string}`;
type Getter<T extends string> = `get${Capitalize<T>}`;
```

Template literal types are string-level computation. Lean's `String` type has no refinement mechanism to express "strings matching a pattern."

**What happens:** Maps to `String` with no refinement. Type safety at the template-literal level is lost.

**Workaround:** Use branded types or plain `string` with runtime validation.

### Distributive Conditional Types

```typescript
type Extract<T, U> = T extends U ? T : never;
// When T is a union, this distributes: Extract<'a' | 'b' | 'c', 'a' | 'c'> = 'a' | 'c'
```

When `T` is a union, TypeScript distributes the conditional across each member. No Lean equivalent exists for this distribution.

**What happens:** The resolved true branch is used when possible. Distribution over unions is not modeled.

**Workaround:** Avoid distributive conditional types in public APIs that will be transpiled. Use explicit union types.

### Index Access Types

```typescript
type NameType = User['name'];  // string
type FirstArg<F> = F extends (a: infer A, ...args: any[]) => any ? A : never;
```

Lean structures have fields but no type-level field access operator analogous to `T[K]`.

**What happens:** Concrete uses are resolved by the checker. Generic `T[K]` patterns emit `sorry`.

**Workaround:** Use explicit type parameters for the fields you need.

## Partially Supported

These features produce output, but the output may be incomplete or semantically different from the TypeScript original.

### typeof / instanceof

```typescript
if (typeof x === 'string') { ... }
if (x instanceof Error) { ... }
```

These are runtime type tests. Lean's type system is checked at compile time; there is no `typeof` operator.

**What happens:** Emits `sorry` with error code TSL201.

**Workaround:** Use discriminated unions with a `tag`/`kind`/`type` field instead of `typeof`/`instanceof` checks. TSLean handles discriminated union pattern matching well:

```typescript
// Instead of: if (typeof x === 'string')
// Use:
type Value = { tag: 'str'; value: string } | { tag: 'num'; value: number };
function process(v: Value) {
  switch (v.tag) {
    case 'str': return v.value.toUpperCase();
    case 'num': return String(v.value);
  }
}
```

### Generators and yield

```typescript
function* range(n: number) {
  for (let i = 0; i < n; i++) yield i;
}
```

Generators are coroutine-based lazy sequences. Lean 4 has no built-in coroutine mechanism in its pure functional core.

**What happens:** Emits `sorry` with error code TSL204.

**Workaround:** Replace generators with array-producing functions or explicit recursion:

```typescript
// Instead of a generator:
function range(n: number): number[] {
  const result: number[] = [];
  for (let i = 0; i < n; i++) result.push(i);
  return result;
}
```

### Structural Subtyping

TypeScript uses structural typing: a function accepting `{ name: string }` works with any object that has a `name` field (and possibly more). Lean uses nominal typing: a `Point` is not a `Vec2` even if they have the same fields.

**What happens:** The transpiler maps to nominal types. A function expecting `Point` will only accept `Point`, not a structurally compatible type.

**Workaround:** Use type classes for shared behavior, or define a common interface/structure that all compatible types extend.

### WeakMap / WeakSet

```typescript
const cache = new WeakMap<object, string>();
```

**What happens:** Modeled as `AssocMap`/`AssocSet` — no garbage collection semantics. Keys are not weakly held.

**Workaround:** None needed for correctness verification. The semantic difference only matters for memory management, which is outside the verification scope.

### RegExp

```typescript
const re = /^hello/;
const match = str.match(re);
```

**What happens:** `RegExp` exists as an opaque structure. Pattern matching operations (`test`, `match`, `replace` with regex) use stub implementations that return default values.

**Workaround:** Use `String.includes`, `String.startsWith`, `String.endsWith` where possible — these have faithful Lean implementations.

### Dynamic Property Access

```typescript
const key = "name";
const value = obj[key];  // dynamic key
```

**What happens:** Dynamic property access where the key is a runtime value emits `sorry`. Static property access (`obj.name`) works.

**Workaround:** Use explicit field access or `Map` for dynamic key-value patterns.

## Known Rough Edges

### Mutation Overhead

Mutable variables (`let x = 0; x = 1;`) are modeled via `StateT` or `IO.Ref`. This changes the function's type signature and adds monadic overhead. A simple counter function goes from `Nat → Nat` to `StateT Unit IO Nat`.

**Impact:** Downstream Lean code that calls these functions must also operate in the monad.

**Workaround:** Prefer `const` bindings and functional patterns (map/filter/reduce) over imperative mutation. The transpiler handles `const` bindings as pure `let` expressions with no monad overhead.

### Self-Hosting Structural Diffs

When the transpiler transpiles its own source code (self-hosting / fixpoint verification), `this.method()` calls on class instances may not fully resolve in all contexts. The known diff is ~90 lines in `lower.ts`.

**Impact:** Self-hosting achieves 9/10 files identical; `lower.ts` has structural differences that do not affect correctness.

### Number Precision

TypeScript's `number` is IEEE 754 double. Lean's `Float` is also IEEE 754 double, but `Nat`/`Int` are arbitrary precision. The transpiler defaults to `Float`, which can lose precision for large integers.

**Workaround:** Use `bigint` in TypeScript for values that need arbitrary precision — it maps to `Int` in Lean. Or use explicit type annotations in your code.

### Optional Chaining Depth

```typescript
const name = user?.profile?.name;
```

Optional chaining is supported but deeply nested chains may produce verbose Lean output with nested `Option.bind` calls.

**Workaround:** None needed; the output is correct but verbose. Breaking into intermediate variables improves readability.

### Enum Value Access

Numeric enums work. String enums work. Reverse mapping (`Color[0]` → `"Red"`) is not supported.

**Workaround:** Use string enums or explicit lookup functions.

### Overloaded Functions

TypeScript function overloads (multiple signatures for one function) are not fully supported. The transpiler uses the implementation signature.

**Workaround:** Use union types or generic parameters instead of overloads.

### Decorators

TypeScript decorators (`@log`, `@injectable`) are not supported. They are metaprogramming constructs with no direct Lean equivalent.

**Workaround:** Apply the decorator's effect manually (e.g., wrap the function in a logging combinator).

## Error Codes Reference

| Code | Category | Description | Severity |
|------|----------|-------------|----------|
| TSL001 | Parser | Unknown AST node encountered | Warning |
| TSL002 | Parser | Unsupported syntax construct | Warning |
| TSL003 | Parser | Missing type annotation (cannot infer) | Warning |
| TSL004 | Parser | Cycle detected in type references | Error |
| TSL005 | Parser | Invalid import specifier | Warning |
| TSL100 | Types | Unresolved type (falls back to `TSAny`) | Warning |
| TSL101 | Types | Inexpressible type (conditional/mapped/infer) | Warning |
| TSL102 | Types | Type constraint lost in translation | Warning |
| TSL103 | Types | Intersection type erased | Warning |
| TSL200 | Lowering | Sorry emitted (general) | Warning |
| TSL201 | Lowering | typeof/instanceof not supported | Warning |
| TSL202 | Lowering | Runtime API call not mapped to stub | Warning |
| TSL203 | Lowering | Mutation pattern requires StateT | Info |
| TSL204 | Lowering | Generator/yield not supported | Warning |
| TSL205 | Lowering | Inductive field access pattern issue | Warning |
| TSL300 | Project | Source file not found | Error |
| TSL301 | Project | Circular import detected | Error |
| TSL302 | Project | Invalid tsconfig.json | Error |
| TSL400 | Lean | Lean build failed | Error |
| TSL401 | Lean | Lean type mismatch in generated code | Error |

## Sorry Tracking Categories

Every `sorry` emitted by the lowerer is tracked with a category. Run with `--timing` or check the appended comment block in the output to see the sorry summary.

| Category | Description | Typical Cause |
|----------|-------------|---------------|
| `unresolved-expr` | Expression could not be lowered | Unknown AST pattern |
| `unresolved-type` | Type could not be mapped | Inexpressible utility type |
| `runtime-api` | JS runtime API not mapped | Missing stub in stdlib |
| `type-test` | typeof/instanceof test | Runtime type check |
| `inductive-field` | Field access on inductive variant | Direct field access without match |
| `mutation` | Complex mutation pattern | Non-trivial assignment |
| `control-flow` | Unhandled control flow | labeled break/continue, goto-like |
| `generator` | Generator/yield | Coroutine pattern |
| `other` | Uncategorized | Miscellaneous |

## Roadmap

The following improvements are planned or under consideration:

- **Type class synthesis for structural subtyping** — Generate type classes from shared interface shapes to recover some structural typing.
- **Generator → LazyList** — Map generator functions to `LazyList` or `Stream` using thunked evaluation.
- **typeof elimination** — Analyze the branches of typeof checks and synthesize discriminated union wrappers.
- **Improved mutation analysis** — Detect simple mutation patterns (counter increment, accumulator append) and use pure functional equivalents instead of `StateT`.
- **Partial/Pick/Omit concrete expansion** — When the base type is known, expand utility types to concrete structures instead of emitting `sorry`.
- **Decorator support** — Map common decorators to Lean attributes or wrapper functions.
