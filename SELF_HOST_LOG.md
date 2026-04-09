# TSLean Self-Hosting Log

## Summary

TSLean can transpile **all 11 of its own source files** to Lean 4, producing
**3,789 lines** of Lean code. The transpiled output captures the full structure:
algebraic data types, pattern matching, monadic effects, and generic functions.

## Self-Hosted Files

| Source File | Output Lines | Key Structures |
|------------|-------------|----------------|
| `src/ir/types.ts` (238 lines) | 368 lines | `Effect` inductive, `IRType` inductive, `IRExpr` type, smart constructors |
| `src/parser/index.ts` (1,446 lines) | 1,407 lines | `ParserCtx` class → namespace with methods, TS compiler API calls → sorry |
| `src/codegen/index.ts` (1,112 lines) | 746 lines | `Gen` class → namespace, string emission helpers |
| `src/typemap/index.ts` (361 lines) | 344 lines | `mapType` function, `irTypeToLean`, discriminated union detection |
| `src/effects/index.ts` (125 lines) | 197 lines | `inferNodeEffect`, `monadString`, effect lattice operations |
| `src/rewrite/index.ts` (296 lines) | 208 lines | `RewriteCtx` class, discriminant pattern rewriting |
| `src/stdlib/index.ts` (175 lines) | 106 lines | Method/global translation tables as AssocMap definitions |
| `src/verification/index.ts` (108 lines) | 106 lines | Proof obligation generation |
| `src/project/index.ts` (137 lines) | 137 lines | Multi-file transpilation, import graph resolution |
| `src/do-model/ambient.ts` (109 lines) | 35 lines | CF Workers ambient declarations (mostly string constants) |
| `src/cli.ts` (84 lines) | 135 lines | CLI argument parsing, file I/O |

**Total: 4,191 → 3,789 lines (90% size preservation)**

## Compilation Status

The self-hosted files don't compile out-of-the-box because they reference:
1. **TypeScript compiler API** (`ts.createProgram`, `ts.TypeChecker`) — no Lean equivalent
2. **Node.js modules** (`fs`, `path`, `child_process`) — no Lean equivalent
3. **Mutual recursion** between `Effect` and `IRType` — needs `mutual` block
4. **String template literals** with complex interpolation — Lean's `s!` is simpler
5. **Class methods** — transpiled as standalone functions in a namespace

## Codegen Limitations Discovered

### 1. Mutual Type Recursion
`Effect` references `IRType` (in `State` and `Except` constructors) and `IRType`
references `Effect` (in `Function`). TypeScript handles this naturally; Lean
requires a `mutual` block. The codegen doesn't detect cross-type mutual deps.

**Impact:** IR_Types.lean fails at `Effect.State` constructor.
**Fix needed:** Detect mutual type references and emit `mutual ... end` wrapper.

### 2. TypeScript Compiler API Calls
The parser uses `ts.createProgram`, `checker.getTypeAtLocation`, etc. These
are TypeScript-specific APIs with no Lean equivalent. They transpile as
function calls to undefined identifiers.

**Impact:** parser_index.lean references `ts.createProgram` which doesn't exist.
**Fix needed:** None practical — the TS compiler API is inherently JS-specific.
Self-hosting the parser would require implementing a TS type checker in Lean.

### 3. Class Method Dispatch
TypeScript classes with methods transpile to Lean namespaces with standalone
functions. Instance method dispatch (`this.field`) becomes explicit `self.field`
parameter passing. This works but loses the OO dispatch semantics.

**Impact:** Cosmetic — all methods work as standalone functions.
**Fix needed:** None — this is the correct Lean translation.

### 4. Generic Higher-Order Functions
Functions like `Array.filter(predicate)` where the predicate is a lambda
with captured variables transpile correctly but may need explicit type
annotations in Lean to resolve ambiguous overloads.

**Impact:** Some `Array.map`/`Array.filter` calls need `(· : T → Bool)` annotations.
**Fix needed:** Emit type annotations for lambda parameters in method calls.

### 5. String Interpolation with Complex Expressions
TypeScript template literals like `` `${expr.nested.field}` `` transpile to
`s!"..."` correctly, but complex interpolated expressions (function calls,
ternary operators) inside templates fall back to `++` concatenation.

**Impact:** Minor — `++` is valid Lean, just less idiomatic than `s!`.
**Fix needed:** Expand `trySInterp` to handle more expression types.

### 6. Node.js File System API
`fs.readFileSync`, `fs.writeFileSync`, `path.join`, etc. have no Lean
equivalents. These transpile as calls to undefined functions.

**Impact:** cli.ts and project/index.ts can't run in Lean.
**Fix needed:** Lean 4 has `IO.FS.readFile` etc. — add a mapping layer.

### 7. Map/Object Literal Types
TypeScript's `Record<string, T>` and `{ [key: string]: T }` map to
`AssocMap String T` in Lean. Object literals like `{ headers: { ... } }`
sometimes produce nested struct literals that confuse the Lean parser.

**Impact:** Counter DO and some DO files need `default` for nested structs.
**Fix needed:** Detect Record types and emit `List (String × T)` instead.

## What Works Well

1. **Algebraic data types**: TS union types → Lean inductives ✓
2. **Pattern matching**: `switch` on discriminants → `match` with PCtor patterns ✓
3. **Generic functions**: `<T>` → `{T : Type}` with correct inference ✓
4. **Branded types**: `string & {__brand}` → Lean newtype structs ✓
5. **Effect inference**: async/throw/mutation → IO/ExceptT/StateT monad stacks ✓
6. **String interpolation**: Template literals → `s!"..."` Lean syntax ✓
7. **Struct updates**: `{ ...obj, field: value }` → `{ obj with field := value }` ✓
8. **Comments**: JSDoc → `/-- doc -/` Lean doc comments ✓

## Next Steps for Full Self-Hosting

1. Add `mutual ... end` detection for cross-type recursion
2. Map `fs.readFile` → `IO.FS.readFile`, `path.join` → `System.FilePath`
3. Create a Lean 4 "TS Compiler API" stub that models type checking
4. Build a Lean 4 string manipulation library matching JS String methods
5. Implement the DO monad state threading properly in Lean
