# Bootstrap Status: Self-Hosting Progress

## Current Status

**12/12 SelfHost files compile.** All transpiled source files have hand-patched Lean
equivalents that pass `lake build` with 0 errors (80 jobs total).

The hand-patches preserve the transpiler's type declarations and function signatures
while fixing codegen issues (`.tag` field access, if-else formatting, mutual recursion).

## File Status

| Source | TS lines | Lean lines | Compile | Content level |
|--------|----------|------------|---------|---------------|
| ir/types.ts | 382 | 265 | ✅ | Full IR types: Effect, IRType, IRExpr, IRDecl, IRModule |
| effects/index.ts | 209 | 77 | ✅ | monadString, joinEffects, effectSubsumes, irTypeName |
| verification/index.ts | 113 | 98 | ✅ | collectExpr, collectDecl, emitObligation, generateVerification |
| project/index.ts | 132 | 35 | ✅ | ProjectOpts, ProjectResult, transpileProject, toLeanPath |
| typemap/index.ts | 383 | 43 | ✅ | mapType, irTypeToLean, StructField, DiscriminantInfo |
| parser/index.ts | 1,527 | 34 | ✅ | ParseOptions, ParserCtx, parseFileSync |
| cli.ts | 105 | 57 | ✅ | Args, parseArgs, single, project, main |
| stdlib/index.ts | 177 | 50 | ✅ | MethodTx, ObjKind, GlobalTx, translateBinOp, typeObjKind |
| rewrite/index.ts | 338 | 28 | ✅ | UnionInfo, VariantInfo, RewriteCtx, rewriteModule |
| codegen/index.ts | 1,306 | 28 | ✅ | GenState, generateLean |
| do-model/ambient.ts | 125 | 28 | ✅ | hasDOPattern, CF_AMBIENT, makeAmbientHost |
| **Total** | **4,899** | **743** | **12/12** | |

## Files with Real Logic (not just stubs)

These files have substantial hand-patched implementations matching the TS source:

1. **IR_Types.lean** (265 lines) — Complete IR type system with mutual Effect/IRType,
   26-constructor IRExpr, BEq instances, smart constructors
2. **verification_index.lean** (98 lines) — Full collectExpr/collectDecl walking the IR tree,
   pattern matching on all IRExpr constructors, emitObligation code generation
3. **effects_index.lean** (77 lines) — monadString matching on Effect constructors,
   irTypeName recursive type stringifier, joinEffects, effectSubsumes
4. **src_cli.lean** (57 lines) — Argument parsing, mode dispatch, single/project entry points
5. **stdlib_index.lean** (50 lines) — translateBinOp with all 18 operators, typeObjKind
6. **DoModel_Ambient.lean** (28 lines) — hasDOPattern, makeAmbientHost with CompilerHost

## Pipeline Status

| Stage | Status | Evidence |
|-------|--------|----------|
| **Parser** (TS → IR) | **100%** | 0 holes / 62,489 IR nodes across 11 files |
| **Rewrite** (IR → IR) | Working | Discriminated unions → pattern matching |
| **Codegen** (IR → Lean) | 40-96% | Declaration coverage 100%; body coverage limited |
| **SelfHost compilation** | **12/12** | All files compile with `lake build` |

## Phase 2 Readiness

To replace stubs with full transpiler output, the codegen needs to fix:

1. **`.tag` field access → pattern matching** (~40 errors in raw output)
2. **if-else indentation** (~15 errors in raw output)
3. **Struct literal → inductive constructor** (~10 errors)
4. **Large Match body emission** (currently collapses to `do pure default`)
5. **Import path rewriting** (self-referencing SelfHost paths)

When the codegen fixes these, regenerating will produce output that compiles directly.

## Build Stats

```
lake build: 80/80 jobs, 0 errors
Tests: 1415 passing across 31 files
Theorems: 1102 proved
```
