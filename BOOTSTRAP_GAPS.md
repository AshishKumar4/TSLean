# Bootstrap Gaps: Self-Hosting Compilation Issues

## Overview

The transpiler produces **73-96%** of expected output (by line count) for self-host files,
but the output has systematic compilation errors. This document catalogs each gap.

**Transpiler output coverage:**
| Source file | TS lines | Lean lines | Coverage | Compile errors |
|-------------|----------|------------|----------|----------------|
| ir/types.ts | 382 | 368 | 96% | 14 (mutual recursion) |
| parser/index.ts | 1,461 | 1,079 | 73% | ~100 (type mismatch) |
| codegen/index.ts | 1,246 | 502 | 40% | ~17 (switch/type) |
| effects/index.ts | 209 | 196 | 93% | ~5 (type) |
| stdlib/index.ts | 177 | 106 | 59% | ~8 (string literal) |
| rewrite/index.ts | 338 | 182 | 53% | ~15 (type) |
| verification/index.ts | 113 | 103 | 90% | ~5 (type) |
| typemap/index.ts | 383 | 292 | 76% | ~20 (recursive fn) |
| project/index.ts | 132 | 118 | 88% | ~5 (IO universe) |
| cli.ts | 105 | 112 | 105% | ~3 |
| do-model/ambient.ts | 125 | 34 | 26% | ~3 (string method) |

## Gap 1: Discriminated Union Construction (CRITICAL)

**Impact:** ~60% of all errors across self-host files.

**Pattern in TS:**
```typescript
const decl: IRDecl = { tag: "FuncDef", name, typeParams, params, retType, effect, body };
```

**Current Lean output:**
```lean
let decl : String := { tag := "FuncDef", name := name, ... }
-- ERROR: `tag` is not a field of structure `String`
```

**Expected Lean output:**
```lean
let decl : IRDecl := .FuncDef name typeParams params retType effect body
```

**Root cause:** The codegen emits struct literals for IR types. But in Lean, these types
are inductives, not structures. The codegen needs to recognize inductive types and emit
constructor calls instead of struct literals.

**Fix location:** `src/codegen/index.ts`, `genStructLit()` method.

## Gap 2: `.tag` Field Access on Inductives

**Impact:** ~20% of errors.

**Pattern in TS:**
```typescript
if (e.tag === "FuncDef") { ... e.name ... }
```

**Current Lean output:**
```lean
if e.tag == "FuncDef" then ... e.name ...
-- ERROR: `tag` is not a field of `IRExpr`
```

**Expected Lean output:**
```lean
match e with
| .FuncDef name _ _ _ _ _ => ... name ...
| _ => ...
```

**Root cause:** The rewrite pass converts discriminated unions to pattern matching for
user-defined types, but not for the IR types themselves (self-referencing code).

**Fix location:** `src/rewrite/index.ts`, discriminant detection.

## Gap 3: Switch Statement Compilation (40% coverage for codegen)

**Impact:** codegen.ts has 11 switch statements; most are dropped.

**Pattern in TS:**
```typescript
switch (d.tag) {
  case "StructDef": this.emitStruct(d); break;
  case "InductiveDef": this.emitInductive(d); break;
  // ... 10+ cases
}
```

**Current Lean output:** Often reduced to a single `match` with 2-3 cases, or dropped entirely.

**Fix location:** `src/parser/index.ts`, `parseStatement()` — needs full SwitchStatement handling.

## Gap 4: Mutual Recursion in Inductive Types

**Impact:** IR_Types.lean core types.

**Pattern in TS:**
```typescript
type Effect = { tag: "State"; stateType: IRType } | ...
type IRType = { tag: "Function"; params: IRType[]; ret: IRType; effect: Effect } | ...
```

**Current Lean output:**
```lean
inductive Effect where
  | State (stateType : IRType)  -- ERROR: IRType not defined yet
```

**Expected Lean output:**
```lean
mutual
inductive Effect where | State (stateType : IRType) | ...
inductive IRType where | Function (params : Array IRType) (ret : IRType) (effect : Effect) | ...
end
```

**Fix location:** `src/codegen/index.ts`, detection of cross-referencing inductive types.
**Status:** Hand-fixed in IR_Types.lean.

## Gap 5: Universe Constraints (Type 1)

**Impact:** IO-returning functions can't take IRModule/IRDecl.

The mutual `Effect`/`IRType` generates types in `Type 1` (due to `Array IRType` nesting).
`IO` only accepts `Type`, not `Type 1`. Functions like `parseFile` that return
`IO IRModule` fail to typecheck.

**Workaround:** Use non-IO return types, or restructure to avoid deep nesting.

## Gap 6: `for ... of` → Lean Loop Patterns

**Impact:** Many imperative loops are dropped or produce broken output.

**Pattern in TS:**
```typescript
for (const d of mod.decls) { this.emitDecl(d); }
```

**Expected Lean output:**
```lean
mod.decls.forM (fun d => emitDecl d)
-- or: for d in mod.decls do emitDecl d
```

**Status:** Partially handled via `Array.forM`. Complex loop patterns with mutation still broken.

## Gap 7: Method Chains

**Pattern in TS:**
```typescript
text.split('\n').map(l => l.trim()).filter(l => l.length > 0).join('\n')
```

**Expected Lean output:**
```lean
text.splitOn "\n" |>.map String.trim |>.filter (fun l => l.length > 0) |> String.intercalate "\n"
```

**Status:** Partially handled. Deep chains sometimes produce incorrect argument order.

## Priority Order for Fixing

1. **Gap 1** (discriminated union construction) — fixes 60% of errors
2. **Gap 2** (.tag access → pattern matching) — fixes 20% of errors  
3. **Gap 3** (switch compilation) — enables codegen.ts self-hosting
4. **Gap 4** (mutual recursion) — already hand-fixed
5. **Gap 6** (for...of loops) — partially working
6. **Gap 5** (universe) — fundamental Lean limitation, needs restructuring
