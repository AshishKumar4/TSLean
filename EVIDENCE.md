# Evidence Ledger

This file is append-only. Counts describe the named revision and working-tree state; they are not correctness claims.

## 2026-08-05 — Phase 0 baseline

- Upstream revision: `3c16098c2317929700c57f7419a80c924d4948a0` (`3c16098`)
- Branch: `rebuild/semantic-core`
- Original TypeScript baseline: 24 `tsc` errors.
- Original Vitest baseline: 1,439 passed, 46 failed, 105 skipped.
- Original Lean baseline: 115 of 118 jobs completed; build failed because `IR_Types.lean` and `ir_types.lean` collide on a case-insensitive filesystem.
- Extracted semantic corpus baseline: 100 red entries. The checked corpus subsequently grew to 102 red entries; red entries are unresolved evidence, not passing conformance tests.
- Current Vitest baseline: 40 files passed; 1,601 tests passed, 8 todo, 0 failed.
- Current Lean baseline: 117 jobs completed successfully.
- Current lint status: passed.
- Current TypeScript build status: passed.
- Current Lean warnings include `sorry`-backed legacy runtime and stub declarations. No soundness or completeness claim is made.

Commands used to validate the current baseline:

```text
$ bun run test
Test Files  40 passed (40)
Tests  1601 passed | 8 todo (1609)

$ bun run lint
$ tsc --noEmit && eslint src/

$ bun run build
$ tsc

$ cd lean && lake build
Build completed successfully (117 jobs).
```

The historical failing counts above were captured before the Phase 0 repairs and are retained as the before-state. Machine-readable Phase 0 counts and explicit todos are in `evidence/baseline-input.json`; `evidence/baseline-manifest.json` records the explicit upstream revision, toolchain, and source, runtime, and corpus hashes for the immutable Phase 0 snapshot. Its source-derived validations and hash groups are read from the frozen `89c2571` tree, so current evidence checks never reinterpret or mutate the baseline. `bun run evidence:baseline:generate` and `bun run evidence:baseline:check` are explicit historical reproduction commands.

## 2026-08-05 — Local gate

Command and result:

```text
$ bun run verify
$ prettier --check 'scripts/*.mjs' 'evidence/*.json' package.json
All matched files use Prettier code style!
$ tsc --noEmit && eslint src/ scripts/*.mjs
$ vitest run
Test Files  40 passed (40)
Tests  1601 passed | 8 todo (1609)
$ tsc
$ cd lean && lake build
Build completed successfully (117 jobs).
```

The gate exited successfully. Lean emitted its existing warnings, including `declaration uses 'sorry'` in `TSLean.Runtime.Basic`, Workers stubs, `TSLean.Stubs.NodeHttp`, and `TSLean.Stubs.WebAPIs`; no warnings were suppressed. The increase from the captured 1,592-test repaired baseline to 1,601 passing tests reflects the additional Phase 0 corpus, declaration-reader, and CLI safety tests.

## 2026-08-06 — Phase 1 ECMAScript value core

The first isolated semantic slice under `lean/TSLean/JS/` passed these commands:

```text
$ cd lean && lake build TSLean.JS
Build completed successfully (10 jobs).

$ cd lean && lake env lean TSLean/JS/Tests.lean

$ cd lean && lake env lean TSLean/JS/AxiomAudit.lean

$ cd lean && if rg -n '(^|[[:space:]])(sorry|axiom|opaque|partial|unsafe|noncomputable)([[:space:]]|$)' 'TSLean/JS' 'TSLean/JS.lean'; then exit 1; fi

$ cd lean && if rg --pcre2 -n '^import (?!TSLean\.JS(?:\.|$)|Init(?:\.|$)|Std(?:\.|$))' 'TSLean/JS' 'TSLean/JS.lean'; then exit 1; fi

$ bun run evidence:generate

$ bun run evidence:check

$ bun run verify
Build completed successfully (128 jobs).

$ git diff --check
```

The Phase 1 commands generate and check `evidence/phase1-primitives-manifest.json` from the immutable `evidence/phase1-primitives-input.json`; `verify` checks that same current manifest and does not check or rewrite Phase 0 evidence. The two scans and `git diff --check` produced no output. The production `TSLean.JS` target excludes executable tests and audit commands; the full build reaches both through `TSLean.Tests`. `AxiomAudit.lean` audits all 43 exported theorems and reports at most Lean's foundational `propext` and `Quot.sound`; the new slice declares no assumptions and does not use `Classical.choice`.
