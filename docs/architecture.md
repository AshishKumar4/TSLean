# TSLean Architecture

## Pipeline Overview

```
TypeScript Source (.ts)
        │
        ▼
┌──────────────┐    ts.TypeChecker
│   Parser     │◄──────────────── Type resolution
│  (parser/)   │
└──────┬───────┘
       │ IRModule (IR types, effects, expressions)
       ▼
┌──────────────┐
│   Rewrite    │    Pattern normalization, desugar
│  (rewrite/)  │
└──────┬───────┘
       │ IRModule (rewritten)
       ▼
┌──────────────┐
│   Lowerer    │    IR → LeanAST
│  (codegen/)  │
└──────┬───────┘
       │ LeanFile (LeanDecl[], LeanExpr[], LeanTy[])
       ▼
┌──────────────┐
│   Printer    │    LeanAST → Text
│  (codegen/)  │
└──────┬───────┘
       │ String (valid Lean 4 source)
       ▼
  Output (.lean)
```

## Key Modules

### `src/parser/index.ts`
Converts TypeScript AST nodes to the intermediate representation (IR). Uses the TypeScript compiler API (`ts.TypeChecker`) for full type resolution. Handles: functions, classes, interfaces, enums, type aliases, imports/exports, control flow, effects.

### `src/ir/types.ts`
Defines the IR type system: `IRType` (types), `IRExpr` (expressions), `IRDecl` (declarations), `Effect` (IO/State/Except), `TypeParam` (generic parameters with constraints).

### `src/typemap/index.ts`
Maps TypeScript compiler types to IR types. Handles: primitives, generics, discriminated unions, branded types, utility types (`Partial`, `Record`, etc.), intersection/union types.

### `src/effects/index.ts`
Effect inference: detects `async`, `throw`, mutable state, and assigns effect annotations (`Pure`, `IO`, `Except`, `State`, `Combined`).

### `src/rewrite/index.ts`
Pattern normalization: converts switch statements to discriminated union matches, normalizes field access patterns, simplifies control flow.

### `src/codegen/lower.ts`
Lowers IR to LeanAST. Maps IR types to Lean types, IR expressions to Lean expressions, IR declarations to Lean declarations. Handles monad transformer stacks, type class constraints, sorry degradation.

### `src/codegen/printer.ts`
Pretty-prints LeanAST to valid Lean 4 source text. Handles indentation, do-notation, let-binding chains, pattern matching, string interpolation.

### `src/codegen/lean-ast.ts`
Defines the LeanAST types: `LeanDecl`, `LeanExpr`, `LeanTy`, `LeanTyParam`, `LeanParam`.

## Lean Runtime Library (`lean/TSLean/`)

- **Runtime/**: Core types (DOMonad, BrandedTypes, Coercions, WebAPI)
- **Stdlib/**: JS standard library (String, Array, HashMap, Numeric, Async, JSON)
- **Stubs/**: npm package stubs (NodeFs, NodePath, NodeHttp, Console, Process)
- **DurableObjects/**: Cloudflare DO model and verification
- **Effects/**: Effect system (EffectKind, EffectSet)
- **Verification/**: Proof obligations and tactics
- **Generated/**: Transpiler output

## Data Flow

1. **Parse**: `ts.SourceFile` → `IRModule` (type-checked, effect-annotated)
2. **Rewrite**: `IRModule` → `IRModule` (pattern-normalized)
3. **Lower**: `IRModule` → `LeanFile` (Lean AST with type class constraints)
4. **Print**: `LeanFile` → `string` (valid Lean 4 source)

## Multi-File Pipeline

For project mode (`--project`):
1. Read `tsconfig.json` for file discovery
2. Build dependency graph with topological sort
3. Detect circular imports (Tarjan's SCC)
4. Transpile files in dependency order
5. Generate `lakefile.toml` and root barrel module
