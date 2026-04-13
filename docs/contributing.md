# Contributing to TSLean

## Development Setup

```bash
git clone https://github.com/AshishKumar4/ts-lean-transpiler.git
cd ts-lean-transpiler
bun install

# Run tests
bun run test

# Build Lean library
export PATH="/opt/lean4/lean-4.29.0-linux/bin:$PATH"
cd lean && lake build
```

## Project Structure

```
src/
  parser/       TypeScript AST → IR
  ir/           Intermediate representation types
  typemap/      TS types → IR types
  effects/      Effect inference
  rewrite/      Pattern normalization
  codegen/      IR → Lean AST → text
  stdlib/       JS stdlib → Lean mapping tables
  stubs/        .d.ts reader for npm packages
  project/      Multi-file compilation
  cli.ts        Command-line interface
  errors.ts     Structured error codes
  sorry-tracker.ts  Sorry/degradation tracking
  utils.ts      Shared utilities
lean/
  TSLean/       Lean 4 runtime library
tests/          Vitest test suite
docs/           Documentation
```

## Adding a New JS Method

1. Add the Lean definition in `lean/TSLean/Stdlib/` (the appropriate module)
2. Add the dispatch entry in `src/stdlib/index.ts` (the appropriate method table)
3. Run `lake build` to verify the Lean compiles
4. Run `bun run test` to verify no regressions
5. Add a test in `tests/stdlib-mapping.test.ts` for the end-to-end mapping

## Adding a New AST Pattern

1. Add the IR node tag in `src/ir/types.ts` (IRExpr or IRDecl)
2. Handle parsing in `src/parser/index.ts`
3. Handle lowering in `src/codegen/lower.ts`
4. Handle printing in `src/codegen/printer.ts` (if new LeanAST node)
5. Add fixture test in `tests/fixtures/` + test in the appropriate test file

## Running the Fixpoint Verification

The fixpoint verifies that the TS pipeline and Lean pipeline produce identical output for 10 target files:

```bash
export PATH="/opt/lean4/lean-4.29.0-linux/bin:$PATH"
cd lean && lake build tslean && cd ..
bash scripts/fixpoint-verify.sh
```

Target: 9/10 identical (lower.ts has known structural diffs).

## Code Quality Rules

- Strict DRY — no duplicated logic
- `bun run test` must pass (1540+ tests)
- `lake build` must pass (112+ jobs)
- Fixpoint must not regress below 9/10
- Every `sorry` must have a tracker entry with category and hint
- No `as any` without justification
- `--strict` TypeScript compilation

## Commit Style

```
feat(phase): description
fix(module): description
test: description
docs: description
refactor: description
chore: description
```
