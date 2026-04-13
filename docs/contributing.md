# Contributing to TSLean

## Development Setup

### Prerequisites

- **Node.js** >= 18
- **Bun** (package manager) — install from [bun.sh](https://bun.sh)
- **Lean 4.29.0** — the exact version the project is pinned to

### Clone and Install

```bash
git clone https://github.com/AshishKumar4/TSLean.git
cd TSLean
bun install
```

### Install Lean 4.29.0

If Lean is not already installed:

```bash
# Download and extract
curl -L "https://github.com/leanprover/lean4/releases/download/v4.29.0/lean-4.29.0-linux.zip" \
  -o /tmp/lean.zip
mkdir -p /opt/lean4
unzip -q /tmp/lean.zip -d /opt/lean4/

# Add to PATH (add to your shell profile for persistence)
export PATH="/opt/lean4/lean-4.29.0-linux/bin:$PATH"

# Verify
lean --version  # Should print: Lean (version 4.29.0, ...)
lake --version  # Should print: Lake ...
```

Alternatively, symlink the binaries:

```bash
ln -sf /opt/lean4/lean-4.29.0-linux/bin/lean /usr/local/bin/lean
ln -sf /opt/lean4/lean-4.29.0-linux/bin/lake /usr/local/bin/lake
```

### Verify Setup

```bash
# Run TypeScript tests (1557 tests across 37 test files)
bun run test

# Build the Lean library
export PATH="/opt/lean4/lean-4.29.0-linux/bin:$PATH"
cd lean && lake build
```

Both must pass before submitting changes.

## Project Structure

```
TSLean/
├── src/                    TypeScript transpiler source
│   ├── cli.ts                CLI entry point (468 lines)
│   ├── parser/               TS AST → IR (1564 lines)
│   ├── ir/                   Intermediate representation types (411 lines)
│   ├── typemap/              TS types → IR types (410 lines)
│   ├── effects/              Effect inference (209 lines)
│   ├── rewrite/              Pattern normalization (333 lines)
│   ├── codegen/              IR → Lean AST → text
│   │   ├── lean-ast.ts         LeanAST type definitions (184 lines)
│   │   ├── lower.ts            IR → LeanAST lowering (1664 lines)
│   │   ├── printer.ts          LeanAST → text (646 lines)
│   │   ├── v2.ts               V2 pipeline entry (112 lines)
│   │   └── index.ts            Public API (47 lines)
│   ├── stdlib/               JS stdlib → Lean mapping tables (240 lines)
│   ├── stubs/                .d.ts reader for npm packages (330 lines)
│   ├── do-model/             Cloudflare DO ambient types (125 lines)
│   ├── project/              Multi-file compilation
│   │   ├── index.ts            Orchestrator (147 lines)
│   │   ├── dependency-graph.ts Tarjan SCC + Kahn topo sort (204 lines)
│   │   ├── module-resolver.ts  File → Lean module name (158 lines)
│   │   ├── reader.ts           tsconfig.json reader (180 lines)
│   │   └── lakefile-gen.ts     lakefile.toml generator (67 lines)
│   ├── preprocessor/         TSC-to-JSON serializer (520 lines)
│   ├── verification/         Proof obligation generator (112 lines)
│   ├── errors.ts             Structured error codes (172 lines)
│   ├── sorry-tracker.ts      Sorry/degradation tracking (75 lines)
│   ├── timing.ts             Pipeline timing (59 lines)
│   └── utils.ts              Shared utilities (12 lines)
├── lean/                   Lean 4 runtime library
│   ├── lakefile.toml         Lake build config (pure Lean 4.29.0, no deps)
│   ├── lean-toolchain        leanprover/lean4:v4.29.0
│   └── TSLean/               Library root
│       ├── Runtime/            Core types, DOMonad, BrandedTypes, Coercions
│       ├── Stdlib/             String, Array, HashMap, HashSet, Numeric, Async, JSON
│       ├── Effects/            EffectKind, Transformer
│       ├── DurableObjects/     DO model, Http, WebSocket, RPC, Auth, etc.
│       ├── Verification/       ProofObligation, Invariants, Tactics
│       ├── Stubs/              Node.js API stubs (axiomatized)
│       ├── External/           Third-party package stubs
│       ├── Proofs/             Transpiler correctness proofs
│       ├── Generated/          Auto-generated transpiler output
│       └── Veil/               Veil DSL for DO specification
├── tests/                  Vitest test suite (37 files, 1557 tests)
│   ├── fixtures/             Test input files (.ts)
│   │   ├── basic/              hello.ts, classes.ts, interfaces.ts
│   │   ├── advanced/           optional-chaining, template-literals, etc.
│   │   ├── durable-objects/    counter, chat-room, rate-limiter, etc.
│   │   ├── generics/           generics, branded-types, discriminated-unions
│   │   ├── effects/            async, exceptions
│   │   ├── full-project/       multi-file project
│   │   └── projects/           calculator, todo-app, type-utils
│   ├── *.test.ts             Unit and integration tests
│   ├── e2e/                  End-to-end CLI tests
│   └── unit/                 Isolated unit tests
├── docs/                   Documentation (you are here)
├── scripts/                Build and verification scripts
├── package.json            Node project config
├── tsconfig.json           TypeScript compiler config
└── vitest.config.ts        Test runner config
```

## How to Add a New TypeScript Pattern

When you want the transpiler to handle a TypeScript syntax construct that currently emits `sorry` or is unrecognized:

### Step 1: Add the IR node (if needed)

If the pattern requires a new expression or declaration type:

1. Open `src/ir/types.ts`
2. Add a new variant to `IRExpr` (for expressions) or `IRDecl` (for declarations)
3. Add a smart constructor if appropriate (e.g., `export function myNewExpr(...)`)

### Step 2: Parse the TypeScript AST

1. Open `src/parser/index.ts`
2. Find the dispatch point for the relevant TypeScript node kind (look for `ts.SyntaxKind.*` switches)
3. Add a handler that constructs the new IR node
4. Use `this.checker` for type resolution and `inferNodeEffect(node, this.checker)` for effect inference

### Step 3: Handle lowering

1. Open `src/codegen/lower.ts`
2. Find the `lowerExpr()` or `lowerDecl()` method
3. Add a case for your new IR tag that produces the appropriate `LeanExpr` or `LeanDecl`

### Step 4: Handle printing (if new LeanAST node)

If you added a new `LeanExpr` or `LeanDecl` variant:

1. Open `src/codegen/lean-ast.ts` and add the variant
2. Open `src/codegen/printer.ts` and add cases in `printExpr()`/`printDecl()`

### Step 5: Add tests

1. Create a test fixture in `tests/fixtures/` (a `.ts` file demonstrating the pattern)
2. Add a test in the appropriate test file:
   - `tests/parser.test.ts` or `tests/parser-advanced.test.ts` — verify IR structure
   - `tests/codegen.test.ts` or `tests/codegen-advanced.test.ts` — verify Lean output
   - `tests/integration.test.ts` — verify full pipeline

### Step 6: Verify

```bash
bun run test                            # TypeScript tests pass
cd lean && lake build                   # Lean library still builds
```

### Example: Adding support for a new expression type

Suppose you want to handle `delete obj.key`:

```typescript
// In src/ir/types.ts — add to IRExpr union:
| ({ tag: 'Delete'; target: IRExpr } & IRNode)

// In src/parser/index.ts — in the expression dispatch:
case ts.SyntaxKind.DeleteExpression: {
  const del = node as ts.DeleteExpression;
  const target = this.parseExpr(del.expression);
  return { tag: 'Delete', target, type: TyBool, effect: IO };
}

// In src/codegen/lower.ts — in lowerExpr():
case 'Delete':
  return { tag: 'App', fn: { tag: 'Var', name: 'AssocMap.erase' },
           args: [this.lowerExpr(e.target)] };
```

## How to Add a New Stdlib Function

When a JavaScript standard library method is not yet mapped:

### Step 1: Add the Lean definition

Open the appropriate Lean file in `lean/TSLean/Stdlib/`:
- String methods → `String.lean`
- Array methods → `Array.lean`
- Map methods → `HashMap.lean`
- Set methods → `HashSet.lean`
- Math/Number → `Numeric.lean`
- Promise/Async → `Async.lean`

Write the implementation:

```lean
-- Example: adding Array.zip
namespace TSLean.Stdlib.Array

def zip (a : Array α) (b : Array β) : Array (α × β) :=
  let n := min a.size b.size
  Array.ofFn fun ⟨i, h⟩ => (a[i]!, b[i]!)

end TSLean.Stdlib.Array
```

### Step 2: Add the dispatch entry

Open `src/stdlib/index.ts` and add to the appropriate method table:

```typescript
// In ARRAY_METHODS:
zip: { leanFn: 'TSLean.Stdlib.Array.zip', resultType: TyArray(TyTuple([TyVar('α'), TyVar('β')])) },
```

For global functions, add to the `GLOBALS` table:

```typescript
'Array.zip': { leanExpr: 'TSLean.Stdlib.Array.zip' },
```

### Step 3: Verify

```bash
# Lean compiles
cd lean && lake build

# Tests pass
cd .. && bun run test

# Test the mapping end-to-end
echo 'const zipped = [1, 2].zip(["a", "b"]);' > /tmp/test.ts
npx tsx src/cli.ts /tmp/test.ts
```

### Step 4: Add a test

Add a test case in `tests/stdlib-mapping.test.ts`:

```typescript
it('maps Array.zip', () => {
  const src = `const zipped = [1, 2].zip(["a", "b"]);`;
  const lean = transpile(src);
  expect(lean).toContain('TSLean.Stdlib.Array.zip');
});
```

## Testing Guide

### Test Framework

TSLean uses [Vitest](https://vitest.dev/) with a 30-second timeout per test. Tests are in `tests/**/*.test.ts`.

### Running Tests

```bash
# Run all tests
bun run test

# Run a specific test file
bun vitest run tests/codegen.test.ts

# Run tests matching a pattern
bun vitest run -t "discriminated union"

# Run tests in watch mode (during development)
bun vitest tests/codegen.test.ts
```

### Test Categories

| Category | Files | What They Test |
|----------|-------|----------------|
| Parser | `parser.test.ts`, `parser-advanced.test.ts`, `parser-types.test.ts` | TS AST → IR conversion |
| Codegen | `codegen.test.ts`, `codegen-advanced.test.ts`, `codegen-depth.test.ts`, `codegen-v2.test.ts`, `codegen-v3.test.ts` | IR → Lean output |
| LeanAST | `lean-ast.test.ts` | LeanAST node construction and printing |
| Type mapping | `typemap.test.ts`, `unit/typemap.test.ts` | TS types → IR types |
| Effects | `effects.test.ts`, `unit/effects.test.ts` | Effect inference |
| Stdlib | `stdlib.test.ts`, `stdlib-mapping.test.ts` | Method lookup tables, end-to-end mapping |
| IR | `ir.test.ts`, `ir-v3.test.ts` | IR type constructors and helpers |
| Rewrite | `rewrite.test.ts` | Discriminated union pattern normalization |
| Verification | `verification.test.ts` | Proof obligation generation |
| Integration | `integration.test.ts`, `pipeline-full.test.ts` | Full parse → rewrite → codegen |
| Project | `project.test.ts`, `project-v3.test.ts`, `module-system.test.ts` | Multi-file, dependency graph, module resolver |
| E2E | `e2e/cli.test.ts`, `e2e/cli-subcommands.test.ts`, `e2e/advanced.test.ts`, `e2e/project.test.ts`, `e2e-v3.test.ts` | CLI spawning, full pipeline |
| Fixtures | `all-fixtures.test.ts` | All fixture files parsed + transpiled |
| Regressions | `bugfixes.test.ts`, `regression.test.ts`, `review-bugs.test.ts`, `grade-bugs.test.ts` | Specific bug fixes |
| DO ambient | `do-ambient.test.ts` | Durable Objects pattern detection |
| Generics | `generics-advanced.test.ts` | Branded types, recursive types |

### Test Patterns

**Unit test** — import a function directly, test with constructed IR nodes:

```typescript
import { mapType } from '../src/typemap/index.js';

it('maps string to String', () => {
  const result = mapType(stringType, checker);
  expect(result.tag).toBe('String');
});
```

**Fixture test** — parse a `.ts` fixture file, check IR structure:

```typescript
import { parseFile } from '../src/parser/index.js';

it('parses class with methods', () => {
  const mod = parseFile({ fileName: 'tests/fixtures/basic/classes.ts' });
  expect(mod.decls).toHaveLength(3);
  expect(mod.decls[0].tag).toBe('StructDef');
});
```

**End-to-end test** — run full pipeline, check Lean output strings:

```typescript
import { parseFile } from '../src/parser/index.js';
import { rewriteModule } from '../src/rewrite/index.js';
import { generateLean } from '../src/codegen/index.js';

it('transpiles discriminated union', () => {
  const mod = parseFile({ fileName: 'tests/fixtures/generics/discriminated-unions.ts' });
  const rewritten = rewriteModule(mod);
  const lean = generateLean(rewritten);
  expect(lean).toContain('inductive Shape');
  expect(lean).toContain('| circle');
});
```

**CLI E2E test** — spawn the transpiler as a child process:

```typescript
import { execSync } from 'child_process';

it('transpiles via CLI', () => {
  const result = execSync('npx tsx src/cli.ts tests/fixtures/basic/hello.ts', { encoding: 'utf8' });
  expect(result).toContain('def hello');
});
```

### Lean Library Testing

```bash
export PATH="/opt/lean4/lean-4.29.0-linux/bin:$PATH"
cd lean

# Full build (all modules)
lake build

# Clean build (if you get stale cache issues)
lake clean && lake build
```

The Lean build compiles all modules in `lean/TSLean/`, including the `Proofs/` directory which contains transpiler correctness theorems. Build failure indicates either a syntax error in the Lean files or an incompatibility introduced by source changes.

## Running the Fixpoint Verification

The fixpoint verifies that the TypeScript transpiler and its self-hosted Lean equivalent produce identical output for 10 target source files:

```bash
export PATH="/opt/lean4/lean-4.29.0-linux/bin:$PATH"
cd lean && lake build tslean && cd ..
bash scripts/fixpoint-verify.sh
```

**Expected result:** 9/10 files identical. `lower.ts` has known structural diffs (~90 lines) due to `this.method()` resolution limitations in the self-hosted pipeline.

A fixpoint regression (fewer than 9/10 identical) means your changes broke the self-hosting pipeline and must be investigated.

## Code Quality Rules

1. **Strict DRY** — no duplicated logic. Extract shared behavior.
2. **`bun run test` must pass** — all 1557+ tests green.
3. **`lake build` must pass** — the Lean library compiles cleanly.
4. **Fixpoint must not regress** — maintain 9/10 identical files.
5. **Every `sorry` tracked** — each sorry emitted by the lowerer must have a `SorryEntry` with category and hint via `src/sorry-tracker.ts`.
6. **No `as any` without justification** — TypeScript type safety matters in a transpiler.
7. **Strict TypeScript** — `tsc --noEmit` must pass.
8. **Simplicity over cleverness** — complexity must be justified.

## Commit Style

Follow conventional commits:

```
feat(parser): handle for-of with destructuring
fix(lower): emit correct monad stack for combined state+except
test: add regression test for branded type generics
docs: expand stdlib-reference with Math functions
refactor(codegen): extract mutual detection into separate pass
chore: update vitest to 4.1.2
```

Format: `type(scope): description`

- **feat** — new feature or capability
- **fix** — bug fix
- **test** — adding or updating tests
- **docs** — documentation only
- **refactor** — code change that neither fixes a bug nor adds a feature
- **chore** — build, dependency, or tooling changes

## Pull Request Process

1. Create a feature branch from `main`
2. Make your changes, following the code quality rules
3. Run the full verification suite:
   ```bash
   bun run test && cd lean && lake build && cd ..
   ```
4. Write a clear PR description explaining the change and motivation
5. Link any relevant issues
6. Ensure CI passes (tests + Lean build)

## Filing Issues

When filing a bug report, include:

1. **Input TypeScript** — the `.ts` source that triggers the issue
2. **Expected Lean output** — what you expected TSLean to produce
3. **Actual Lean output** — what TSLean actually produced (or the error message)
4. **TSLean version** — `npx tslean --version`
5. **Lean version** — `lean --version` (should be 4.29.0)
