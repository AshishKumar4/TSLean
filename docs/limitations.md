# TSLean Limitations

## Fundamentally Inexpressible in Lean 4

These TypeScript features have no equivalent in Lean 4's type system:

### Conditional Types with `infer`
```typescript
type ReturnType<T> = T extends (...args: any[]) => infer R ? R : never;
```
The `infer` keyword performs pattern matching on type structure. Lean's type system doesn't support extracting components from arbitrary types at the type level. **Concrete instantiations work** (the checker resolves them); generic uses emit `sorry`.

### Mapped Types with `keyof`
```typescript
type Partial<T> = { [K in keyof T]?: T[K] };
```
Lean has no `keyof` operator or type-level field iteration. **Concrete instantiations work**; generic uses emit `sorry`.

### Template Literal Types
```typescript
type EventName = `on${string}`;
```
Maps to `String` (no refinement types in standard Lean 4).

### Distributive Conditional Types
```typescript
type Extract<T, U> = T extends U ? T : never;
```
When `T` is a union, this distributes. No Lean equivalent for distribution over unions.

## Partially Supported

### typeof / instanceof
```typescript
if (typeof x === 'string') { ... }
```
Emits `sorry` (error code TSL201). Workaround: use discriminated union patterns with a `tag` field.

### Generators / yield
```typescript
function* range(n: number) { for (let i = 0; i < n; i++) yield i; }
```
Emits `sorry` (error code TSL204). Workaround: use `Array.range` or explicit recursion.

### Structural Subtyping
TypeScript uses structural typing; Lean uses nominal typing. A function accepting `{ name: string }` works with any object that has a `name` field in TS, but in Lean it requires an exact type match or a type class constraint.

### WeakMap / WeakSet
Modeled as regular `AssocMap`/`AssocSet` — no garbage collection semantics.

### RegExp
The `RegExp` type exists as an opaque structure. Pattern matching operations (`test`, `match`, `replace`) are stubs that return default values.

## Known Rough Edges

### Mutation
Mutable variables (`let x = 0; x = 1;`) are modeled via `StateT` / `IO.Ref`. This adds monadic overhead and changes the function signature. Prefer `const` bindings where possible.

### this.method() on Self-Hosted Code
When the transpiler transpiles its own source code, `this.method()` calls on class instances may not fully resolve in all contexts. This is visible in the fixpoint as ~90 differing lines in `lower.ts`.

### Number Precision
TypeScript's `number` is IEEE 754 double. Lean's `Float` is also IEEE 754 double, but `Nat`/`Int` are arbitrary precision. The transpiler maps to `Float` by default; use type annotations for `Nat`/`Int` when needed.

## Error Codes Reference

| Code | Description |
|------|-------------|
| TSL001 | Unknown AST node in parser |
| TSL002 | Unsupported syntax |
| TSL100 | Unresolved type |
| TSL101 | Inexpressible type (conditional/mapped/infer) |
| TSL200 | Sorry emitted by lowerer |
| TSL201 | typeof/instanceof not supported |
| TSL202 | Runtime API call not stubbed |
| TSL204 | Generator/yield not supported |
| TSL301 | Circular import detected |
