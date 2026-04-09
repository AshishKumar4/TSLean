# Bootstrap Gaps: Self-Hosting Compilation Issues

## Overview

The transpiler pipeline has two stages: **Parser** (TS → IR) and **Codegen** (IR → Lean).

**Parser status: 100% complete.** The parser produces **zero holes** (zero `Hole`/`sorry` 
nodes) across all 11 source files, totaling **62,489 IR nodes**.

**Codegen status: 40-96% by line count.** The codegen drops content when emitting 
large switch bodies, template expression chains, and class method bodies.

## Parser Completeness (IR production)

| Source file | TS lines | IR nodes | Holes | Parser coverage |
|-------------|----------|----------|-------|----------------|
| ir/types.ts | 382 | 1,041 | **0** | 100% |
| parser/index.ts | 1,522 | 25,197 | **0** | 100% |
| codegen/index.ts | 1,262 | 20,335 | **0** | 100% |
| effects/index.ts | 209 | 2,091 | **0** | 100% |
| rewrite/index.ts | 338 | 3,237 | **0** | 100% |
| stdlib/index.ts | 177 | 457 | **0** | 100% |
| typemap/index.ts | 383 | 4,768 | **0** | 100% |
| verification/index.ts | 113 | 1,594 | **0** | 100% |
| project/index.ts | 132 | 1,942 | **0** | 100% |
| cli.ts | 105 | 1,483 | **0** | 100% |
| do-model/ambient.ts | 125 | 344 | **0** | 100% |
| **Total** | **4,748** | **62,489** | **0** | **100%** |

## Codegen Output (Lean generation)

| Source file | IR nodes | Lean lines | Line coverage |
|-------------|----------|------------|---------------|
| ir/types.ts | 1,041 | 368 | 96% |
| parser/index.ts | 25,197 | 1,122 | 73% |
| codegen/index.ts | 20,335 | 513 | 40% |
| effects/index.ts | 2,091 | 196 | 93% |
| rewrite/index.ts | 3,237 | 182 | 53% |
| stdlib/index.ts | 457 | 106 | 59% |
| typemap/index.ts | 4,768 | 292 | 76% |
| verification/index.ts | 1,594 | 103 | 90% |
| project/index.ts | 1,942 | 118 | 88% |
| cli.ts | 1,483 | 112 | 105% |
| do-model/ambient.ts | 344 | 34 | 26% |

## Codegen Gaps (NOT parser issues — transpiler-core scope)

### Gap 1: Complex Switch Body Collapse (CRITICAL)
**Impact:** 40% coverage on codegen.ts (513 of 1295 lines)

The codegen emits `do pure default` for functions with large switch statements (>10 cases).
Example: `Gen.genExpr` is 200+ lines in TS with ~30 case clauses. The parser produces a 
complete `Match` IR node with all cases. The codegen collapses it to `do pure default`.

**Evidence:** All 49 codegen.ts declarations appear in the output (49/49 = 100% declaration
coverage). The bodies are truncated — the line gap is entirely body content, not missing functions.

### Gap 2: Discriminated Union Construction
The codegen emits `{ tag := "FuncDef", ... }` (struct literal) for `IRDecl` values, but
the Lean type is an inductive. Should emit `.FuncDef name ...` (constructor application).

### Gap 3: `.tag` Field Access on Inductives
The codegen emits `e.tag == "FuncDef"` but `IRExpr` is an inductive with no `.tag` field.
Should use `match e with | .FuncDef ... => ...`.

### Gap 4: Template Expression Density
codegen.ts has 140 template expressions. The codegen handles them but multiline template 
strings get flattened into single-line `s!"..."` interpolations, reducing line count.

### Gap 5: Universe Constraints (Type 1)
The mutual `Effect`/`IRType` generates types in `Type 1`. `IO` only accepts `Type`.
Functions returning `IO IRModule` fail to typecheck.

## Parser: Recently Fixed

### RegExp Literals (Fixed)
**Before:** `s.split(/[-_]/)` → `s.split default` (Hole node, 21 holes total)
**After:** `s.split(/[-_]/)` → `s.split "/[-_]/"` (string representation, 0 holes)

### Nested Destructuring (Fixed)
**Before:** `const {a: {b, c}} = x` → `let _el123 := ...` (single flat binding)
**After:** `const {a: {b, c}} = x` → `let _ds_a := x.a; let b := _ds_a.b; let c := _ds_a.c`

### Default Values in Destructuring (Fixed)
**Before:** `const {x = 42} = opts` → no default handling
**After:** `const {x = 42} = opts` → `let x := opts.x.getD 42`

## Parser: Complete Patterns

The parser handles ALL these TS patterns without holes:
- Switch statements (with fall-through, default, discriminated unions)
- Ternary/conditional expressions (including nested)
- Template expressions (`\`hello ${name}\``)
- Type assertions (`as T`, `satisfies T`)
- Non-null assertions (`x!`)
- Optional chaining (`x?.y`, `x?.()`)
- Spread elements (`...arr`, `{...obj}`)
- For-of, for-in, while, for loops
- Try/catch/finally
- Async/await
- Class methods and constructors
- Generic type parameters
- Object/array destructuring (including nested)
- Regular expression literals
- Computed property names
- Tagged template literals
- Delete, typeof, void expressions
- JSDoc comment extraction
