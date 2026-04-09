# Bootstrap Status: Self-Hosting Progress

## Two-Phase Plan

**Phase 1 (in progress):** Get codegen quality to <5 Lean errors per file for the easy files.
Only THEN replace the SelfHost stubs.

**Phase 2 (blocked on Phase 1):** Replace `lean/TSLean/Generated/SelfHost/*.lean` stubs with
actual transpiler output. Currently the stubs keep `lake build` working.

## Pipeline Status

| Stage | Status | Coverage |
|-------|--------|----------|
| **Parser** (TS → IR) | **100% complete** | 0 holes / 62,489 IR nodes |
| **Rewrite** (IR → IR) | Working | Discriminated unions, pattern matching |
| **Codegen** (IR → Lean) | **Bottleneck** | 40-96% by line count |

## Per-File Status

| Source | TS | Lean | Coverage | Errors | Status |
|--------|---:|-----:|---------:|-------:|--------|
| ir/types.ts | 382 | 368 | 96% | 57 | Mutual recursion (hand-fixed in IR_Types.lean) |
| effects/index.ts | 209 | 196 | 93% | 8 | `unexpected token 'if'` × 3 (codegen if-else) |
| verification/index.ts | 113 | 103 | 91% | 6 | `unexpected token 'if'` (codegen if-else) |
| project/index.ts | 132 | 118 | 89% | 14 | Missing import paths, type mismatch |
| typemap/index.ts | 383 | 292 | 76% | 10 | Recursive functions need `partial` |
| parser/index.ts | 1,527 | 1,125 | 73% | 35 | Many `.tag` field accesses on wrong types |
| **cli.ts** | **105** | **111** | **106%** | **3** | **Near-compiling: 2 if-else + 1 arg mismatch** |
| stdlib/index.ts | 177 | 106 | 59% | 24 | Object literal syntax, string-as-struct |
| rewrite/index.ts | 338 | 182 | 53% | 27 | Switch body truncation |
| codegen/index.ts | 1,306 | 522 | 39% | 12 | Large Match collapse (`do pure default`) |
| **do-model/ambient.ts** | **125** | **34** | **27%** | **2** | **Near-compiling: struct syntax + type** |

## Declaration Coverage

All declarations are preserved — the line gap is in function bodies, not missing functions:

| Source | TS functions | Lean defs | Coverage |
|--------|-------------|-----------|----------|
| codegen/index.ts | 18 + class | 49 | 100% |
| parser/index.ts | 16 + class | 59 | 100% |
| rewrite/index.ts | 5 + class | 16 | 100% |
| stdlib/index.ts | 6 | 12 | 100% |
| All others | — | — | 100% |

## Error Categories (across all files)

| Error type | Count | Root cause | Owner |
|-----------|------:|------------|-------|
| `.tag` not a field of `String` | ~40 | Codegen emits struct literal for inductives | codegen |
| `unexpected token 'if'` | ~15 | Codegen if-else indentation/newline | codegen |
| `Type mismatch` | ~10 | Wrong type inference in codegen | codegen |
| `Function expected` | ~8 | Method chain argument order | codegen |
| `expected structure` | ~5 | Object literal vs inductive | codegen |
| Mutual recursion | ~57 | Effect/IRType forward reference | codegen (hand-fixed) |
| `Failed to compile pattern` | ~3 | Incomplete match patterns | codegen |
| Missing import paths | ~5 | Cross-file import resolution | codegen |

## Nearest-to-Compiling Files

### cli.ts (3 errors)
```
line 33: Application type mismatch — loop helper wrong arg count
line 37: unexpected 'else' — if-else codegen formatting
line 77: Application type mismatch — generateVerification arg
```

### do-model/ambient.ts (2 errors)
```
line 20: regex .test method call on string literal
line 25: expected structure — CompilerHost struct update syntax
```

### effects/index.ts (8 errors)
```
3× unexpected 'if' — chained if-else codegen
2× Function expected — method call argument order
1× Type mismatch — effect type inference
1× Failed pattern matching — incomplete case
1× Application type mismatch
```

## What Would Fix the Most Files

1. **Codegen: if-else formatting** — Fix indentation so `else` appears on correct line.
   Would fix: cli.ts (1 error), effects (3 errors), verification (1 error) = 5 errors.

2. **Codegen: struct literal → constructor** — Emit `.FuncDef name ...` not `{tag := ...}`.
   Would fix: ~40 errors across parser, stdlib, typemap.

3. **Codegen: large Match emission** — Emit all switch cases, not just first 6.
   Would fix: codegen (body recovery), rewrite (body recovery).

4. **Codegen: import path rewriting** — Map `TSLean.Generated.X.Y` to SelfHost paths.
   Would fix: project (5 errors), any cross-file references.

## Parser Completeness Evidence

The parser produces **zero Hole nodes** for all 11 source files:

```
src/ir/types.ts:        0 holes / 1,041 nodes  (100%)
src/parser/index.ts:    0 holes / 25,197 nodes (100%)
src/codegen/index.ts:   0 holes / 20,335 nodes (100%)
src/effects/index.ts:   0 holes / 2,091 nodes  (100%)
src/rewrite/index.ts:   0 holes / 3,237 nodes  (100%)
src/stdlib/index.ts:    0 holes / 457 nodes    (100%)
src/typemap/index.ts:   0 holes / 4,768 nodes  (100%)
src/verification/index.ts: 0 holes / 1,594 nodes (100%)
src/project/index.ts:   0 holes / 1,942 nodes  (100%)
src/cli.ts:             0 holes / 1,483 nodes  (100%)
src/do-model/ambient.ts: 0 holes / 344 nodes   (100%)
TOTAL:                  0 holes / 62,489 nodes (100%)
```

Verified by integration tests in `tests/parser-advanced.test.ts`.

## Handled TS Patterns (parser)

✅ Switch statements (with fall-through, default, discriminated unions)
✅ Ternary/conditional expressions (including nested)
✅ Template expressions (`\`hello ${name}\``)
✅ Type assertions (`as T`, `satisfies T`)
✅ Non-null assertions (`x!`)
✅ Optional chaining (`x?.y`, `x?.()`)
✅ Spread elements (`...arr`, `{...obj}`)
✅ Regular expression literals (`/pattern/flags`)
✅ Nested destructuring (`const {a: {b, c}} = x`)
✅ Default values in destructuring (`const {x = 42} = obj`)
✅ For-of, for-in, while, for loops
✅ Try/catch/finally
✅ Async/await
✅ Class methods and constructors
✅ Generic type parameters
✅ Computed property names
✅ Tagged template literals
✅ Delete, typeof, void expressions
✅ JSDoc comment extraction
