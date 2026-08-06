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

## 2026-08-06 — Phase 1 ordinary heap

The ordinary-heap slice is based on `f6b40c647d1a1e9490989884c3c33e02a6a1c619` on `rebuild/semantic-core`. Its public state API is `Heap.empty`, `Heap.size`, `Heap.get?`, `Heap.allocate`, `Heap.defineOwnProperty`, `Heap.createDataProperty`, `Heap.deleteProperty`, `Heap.preventExtensions`, and `Heap.setPrototypeOf`. Read-only object operations are `OrdinaryObject.getOwnProperty`, `OrdinaryObject.ownPropertyKeys`, and `Prototype.lookup`. Descriptor input is represented exactly by `DescriptorUpdate` and `FieldUpdate`, so an absent field remains distinct from a present `undefined`, `none` getter, or `none` setter. Failures are separated into `HeapFault`, `DefinePropertyFault`, `DescriptorSyntaxFault`, `DescriptorRejection`, and `PrototypeFault`; ordinary invariant rejection returns `false`, while malformed references and descriptor syntax return typed errors.

The representation boundary is closed: `OrderedProps`, `ObjectRecord`, and `Heap` have private constructors; ordered-property insertion/deletion and heap replacement are private; callers cannot replace a property table or reset extensibility. `OrderedProps.WellFormed` is the executable conjunction of bidirectional map/slot position agreement, duplicate-free occupied string slots, duplicate-free occupied symbol slots, duplicate-free `ownKeys`, equality of key count and map size, exact string and symbol tombstone counts, and the post-compaction bound for both order arrays. `Heap.WellFormed` additionally requires every readable object to have well-formed properties, every object-valued descriptor reference to be allocated, every present accessor reference to resolve to a function-kind object, every represented object to be ordinary, every prototype reference to be allocated, and every allocated prototype chain to terminate within `heap.size + 1` steps. Array-index keys are sorted numerically; other strings and symbols retain insertion order, with delete/reinsert moving a key to the end of its partition.

The proved heap results are allocation freshness, one-slot growth, stability of previous lookups, reference-identity object equality, empty-heap validity, unchanged heaps for rejected descriptor definitions and deletions, and nonextensible prototype rejection before candidate traversal. Preservation is not yet proved for private `OrderedProps.insert` or `OrderedProps.delete`, including threshold-crossing and deletion compaction. Duplicate-free partitioned `ownKeys` has not yet been derived as a theorem. Preservation of complete `Heap.WellFormed` is also still TODO for allocation and every successful public mutation: `defineOwnProperty`, `createDataProperty`, `deleteProperty`, `preventExtensions`, and `setPrototypeOf`. The executable adversarial, churn, ordering, descriptor, reference, and prototype tests are evidence, not substitutes for those proofs.

One local `HeapTests.lean` run measured these bounded smoke workloads:

```text
heap-scale strings keys=10000 buildMs=403 ownKeys10Ms=252
heap-scale symbols keys=10000 buildMs=320 ownKeys10Ms=136
heap-scale indices keys=10000 buildMs=248 ownKeys10Ms=283
heap-churn cycles=100000 stringSlots=62 symbolSlots=62 ms=2251
```

The smoke limits are 2,500 ms per 10,000-key construction, 1,500 ms for ten enumerations, and 7,000 ms for 100,000 string-and-symbol delete/reinsert cycles. They are machine-local regression limits, not portable complexity proofs. The implementation uses expected-O(1) hash lookup/update/insertion, amortized-O(1) deletion with bounded tombstone compaction, and O(n log n) key enumeration because array indices are sorted.

Commands and results:

```text
$ bun run js:trust
JS trust checks passed: 57 elaborated proof declarations
JS trust gate passed: 57 proof declarations

$ bun scripts/check-js-axioms.mjs --self-test
synthetic environment audit passed

$ bun run evidence:generate
$ bun run evidence:generate
$ shasum -a 256 evidence/phase1-heap-manifest.json
8a2d52b2361905023d65d1679d82d6662184d09a5e5238280d3798d954adf530  evidence/phase1-heap-manifest.json

$ bun run evidence:check

$ bun run verify
Test Files  41 passed (41)
Tests  1602 passed | 8 todo (1610)
Build completed successfully (136 jobs).

$ git diff --check
```

The manifest check also rejected a deliberately changed source hash as stale at line 69 before the canonical manifest was regenerated. `evidence/phase1-heap-input.json` and `evidence/phase1-heap-manifest.json` are new files; the Phase 0 and primitive manifests were not rewritten. `evidence:generate`, `evidence:check`, `js:trust`, and `verify` target the heap input. `evidence:primitives:generate` and `evidence:primitives:check` retain explicit primitive-history commands, while the baseline historical commands remain unchanged.

The full 136-job build still emits warnings from the legacy global runtime and generated/stub modules, including existing `sorry` declarations. Those warnings are outside the isolated `TSLean.JS` trust boundary and are not hidden or converted into a repository-wide soundness claim. The JS gate scans the complete production JS runtime and barrel for forbidden declaration tokens and non-isolated imports, then audits all 57 elaborated proof declarations against only `propext`, `Classical.choice`, and `Quot.sound`.

## 2026-08-06 — Phase 1 execution semantics

The execution slice is based on `cfeda92b09ba4990c61ef70066df61df4004674a` on `rebuild/semantic-core`. Its completion API distinguishes normal, return, throw, labeled or unlabeled break, and labeled or unlabeled continue. `Completion.bind` and `JSM.bind` invoke continuations only for normal completion. `Control.tryCatch` catches only JavaScript throws; `Control.tryFinally` always runs finalization after a JavaScript completion and lets an abrupt finalizer replace the prior completion; switch, labeled-statement, and loop handlers consume only transfers owned by that construct. `Control.whileLoop` is total and consumes one unit of machine fuel before each condition check.

The state model deliberately uses the direct total transformer `JSM P α := Machine P → RunResult P α`, rather than composing exception and state transformers whose ordering could obscure commit behavior. `RunResult.done`, `RunResult.exhausted`, and `RunResult.fault` all carry the final committed machine. Heap, lexical-cell and environment arenas, platform state, trace, and fuel therefore survive JavaScript abrupt completion and model faults according to each operation's explicit result. `Environment.withEnvironment` restores only the dynamic `currentEnv`; allocations, heap/platform changes, trace, and fuel remain committed.

`Machine.initial` creates one global environment. Cells and environments have append-only stable identities; declaration creates a TDZ cell, initialization is one-shot, nearest lexical lookup implements shadowing, and TDZ, unresolved-name, and immutable-write failures are JavaScript errors. Invalid identities, duplicate declarations, and repeated initialization are separate model faults. `External.now`, `External.random`, and synchronous modeled `External.fetch` consume pure scripted platform state and append ordered trace events. Fetch rejection is a JavaScript throw, while script exhaustion and host faults are model faults and cannot be caught by JavaScript catch.

Promises, jobs, microtasks, asynchronous fetch, callable objects, function invocation, constructors, `this`, generators, and async functions remain out of scope. The model does not claim complete ECMAScript statement, environment-record, host, or error-object semantics. The proved execution results cover the three monad laws; abrupt-bind preservation; selected catch/finally cases; fresh cell/environment allocation; nearest lexical resolution; successful mutable write; repeated-initialization rejection; trace order; indexed and exhausted scripted platform operations; and fuel decrement/exhaustion. Full machine/environment well-formedness preservation, complete control-handler matrices as theorems, closure semantics beyond stable captured environment identities, platform refinement against a real host, and a general correspondence theorem to ECMAScript are unproved boundaries.

Executable coverage includes the complete 5 × 5 prior/finalizer completion matrix; catch/finally trace order and override cases; switch, labeled break, and loop transfer ownership; committed heap/cell/trace mutation across return and throw; lexical shadowing, captured stable environments, TDZ, immutable writes, and restoration of `currentEnv` across every terminal form; repeated initialization for mutable and immutable cells; successful and rejected scripted platform operations, untaken-effect exclusion, platform-fault commitment, and catch exclusion; and bounded-loop and recursive fuel exhaustion. `ExecutionScaleTests.lean` allocates 100,000 cells, allocates 100,000 child environments, emits 100,000 events, and materializes the ordered trace. One local run completed in 8.06 seconds real time (7.49 user, 0.18 system); this is a machine-local smoke measurement, not a portable performance guarantee or complexity proof.

Commands and results:

```text
$ bun run evidence:generate
$ shasum -a 256 evidence/phase1-execution-manifest.json
a90c0e141153cba34bf6600c18b22c911afcfbb7cc0f990f813f1259dc94e650  evidence/phase1-execution-manifest.json
$ bun run evidence:generate
$ shasum -a 256 evidence/phase1-execution-manifest.json
a90c0e141153cba34bf6600c18b22c911afcfbb7cc0f990f813f1259dc94e650  evidence/phase1-execution-manifest.json

$ bun run evidence:check

$ bun run evidence:baseline:check
$ bun run evidence:primitives:check
$ bun run evidence:heap:check

$ bun run js:trust
JS trust checks passed: 93 elaborated proof declarations
JS trust gate passed: 93 proof declarations

$ bun scripts/check-js-axioms.mjs --self-test
synthetic environment audit passed

$ cd lean && /usr/bin/time -p lake env lean TSLean/JS/ExecutionScaleTests.lean
real 8.06
user 7.49
sys 0.18

$ bun run verify
Test Files  42 passed (42)
Tests  1603 passed | 8 todo (1611)
Build completed successfully (146 jobs).

$ git diff --check
```

A deliberately changed execution source hash was rejected by `evidence:check` as stale at line 69 before the canonical manifest was regenerated. `evidence/phase1-heap-input.json` now resolves every source-derived validation and hash group from immutable `cfeda92`; its checked manifest remains byte-for-byte unchanged at SHA-256 `8a2d52b2361905023d65d1679d82d6662184d09a5e5238280d3798d954adf530`. The current `evidence:generate`, `evidence:check`, and `js:trust` commands target execution evidence. Explicit baseline, primitive, and heap commands retain historical reproduction.

The full 146-job build still emits warnings from legacy global runtime and generated/stub modules, including existing `sorry` declarations. Those warnings remain outside the isolated `TSLean.JS` trust boundary and are not suppressed or presented as repository-wide soundness. The JS gate mechanically discovers and audits all 93 elaborated proof declarations in the production JS runtime while excluding support/test modules from the production barrel.
