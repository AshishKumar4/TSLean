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

## 2026-08-06 - Phase 1 callable objects

The callable-object slice is based on `9a7c7b50c5775add36cd07b9759af03a8281559e` on `rebuild/semantic-core`. Its allocation API is `Function.allocateOrdinary`, `Function.allocateArrow`, `Function.allocateBareConstructor`, `Function.allocateConstructor`, and `Function.allocateClass`. It adds checked property access through `ObjectAccess.get`, `ObjectAccess.set`, and `ObjectAccess.setStrict`; checked invocation through `Call.call`; supported constructor invocation through `Construct.construct`; ordinary prototype identity testing through `Instanceof.ordinaryHasInstance`; and complete primitive/object/function classification through `Value.typeof`. Function metadata carries stable function identity, captured environment, function kind, constructibility, constructor mode, lexical `this`, and optional home object. Constructor/prototype pairs and complete class allocations are atomic after any heritage accessor effects have committed.

`BodyHook P := RefId -> Value -> Array Value -> JSM P Unit` is the evaluator boundary. It supplies body execution without embedding a syntax evaluator in this slice: normal completion is fallthrough, explicit return is `Completion.returned`, throw remains a JavaScript throw, and escaping break/continue becomes a model fault. `Call.call` checks callable metadata, rejects class constructors under ordinary call, selects lexical `this` for arrows, and validates every returned or thrown object reference against the heap committed by the body. `Construct.construct` checks constructibility, reads the current `prototype` through ordinary accessor dispatch, allocates the receiver, applies the object-return override rule, and otherwise returns that receiver. Derived construction is explicitly unsupported: a derived constructor reaches `ModelFault.runtime (.unsupportedDerivedConstruction constructor)` before receiver allocation because `super()` and uninitialized-`this` semantics are not modeled.

The proved additions cover body fallthrough and return/throw normalization, dangling escaping-reference rejection, escaping-break rejection, function allocation freshness/size/count/stability, lexical-arrow receiver validity, constructor/prototype identities and descriptor recipes, direct prototype reachability, callable `typeof`, and checked getter dispatch. The remaining generic theorem TODO is complete `Heap.WellFormed` preservation for constructor/class pairs, the atomic class-element loop, and ordinary get/set; it depends on the private ordered-map preservation lemmas already identified in `HeapTheorems`. The executable tests do not replace that proof.

`FunctionTests.lean` exercises 15 groups: metadata identity, arrow lexical `this`, dangling body values, checked completion normalization, class elements and call rejection, accessor and null heritage, primitive heritage rejection, construction dispatch, dynamic construction prototype selection, accessor receiver/order, throwing accessor state commitment, receiver-own conflicts, `typeof`/`instanceof` and faults, validity checks, and the function-mode matrix. One isolated run completed in 0.74 seconds real time (0.95 user, 0.15 system). `FunctionScaleTests.lean` allocated 100,000 callable objects in 70 ms, checked their well-formedness in 1,031 ms, built a 10,000-edge prototype chain in 3 ms, resolved `instanceof` in 0 ms, and checked chain well-formedness in 97 ms; the complete isolated run took 1.55 seconds real time (1.42 user, 0.13 system). These are machine-local smoke measurements under limits of 5,000 ms for callable allocation and validity, 3,000 ms for chain construction, 1,000 ms for lookup, and 2,000 ms for chain validity. They are not portable performance guarantees or complexity proofs.

Commands and results:

```text
$ bun run evidence:generate
$ shasum -a 256 evidence/phase1-callable-manifest.json
2223fd8bcf3e36a433976ae42d567b820923c9db7eb7857066452664e391f883  evidence/phase1-callable-manifest.json
$ bun run evidence:generate
$ shasum -a 256 evidence/phase1-callable-manifest.json
2223fd8bcf3e36a433976ae42d567b820923c9db7eb7857066452664e391f883  evidence/phase1-callable-manifest.json

$ bun run evidence:check

$ bun run evidence:baseline:check
$ bun run evidence:primitives:check
$ bun run evidence:heap:check
$ bun run evidence:execution:check

$ bun run js:trust
JS trust checks passed: 115 elaborated proof declarations
JS trust gate passed: 115 proof declarations

$ bun scripts/check-js-axioms.mjs --self-test
synthetic environment audit passed

$ cd lean && /usr/bin/time -p lake env lean TSLean/JS/FunctionTests.lean
real 0.74
user 0.95
sys 0.15

$ cd lean && /usr/bin/time -p lake env lean TSLean/JS/FunctionScaleTests.lean
function-scale allocations=100000 buildMs=70 validityMs=1031
prototype-scale depth=10000 buildMs=3 lookupMs=0 validityMs=97
real 1.55
user 1.42
sys 0.13

$ bun run verify
Test Files  42 passed (42)
Tests  1603 passed | 8 todo (1611)
Build completed successfully (155 jobs).

$ bun pm pack --dry-run --ignore-scripts
Total files: 266
Unpacked size: 2.15MB

$ git diff --check
```

A deliberately replaced callable source hash was rejected by `evidence:check` as stale at line 69 before regeneration. `evidence/phase1-execution-input.json` now resolves every source-derived validation and hash group from immutable revision `9a7c7b50c5775add36cd07b9759af03a8281559e`; its manifest remains byte-for-byte unchanged at SHA-256 `a90c0e141153cba34bf6600c18b22c911afcfbb7cc0f990f813f1259dc94e650`. Current `evidence:generate`, `evidence:check`, and `js:trust` commands target callable evidence. Explicit baseline, primitive, heap, and execution generate/check commands retain historical reproduction.

The full 155-job build still emits warnings from legacy global runtime and generated/stub modules, including existing `sorry` declarations. Those warnings remain outside the isolated `TSLean.JS` trust boundary and are not suppressed or presented as repository-wide soundness. The JS gate scans the production JS runtime and barrel, excludes support/test modules, and mechanically discovers and audits all 115 elaborated proof declarations against only `propext`, `Classical.choice`, and `Quot.sound`.

## 2026-08-06 - Phase 1 arrays, copy, and iteration

This slice is based on `5b4da5a67288cf920bcba80d1e897000b73e90f4` on `rebuild/semantic-core`. The array API consists of `Heap.allocateArrayFromArray`, `Heap.allocateArray`, `Heap.arrayLength`, `Heap.allocateArrayIterator`, and `Heap.advanceArrayIterator`, with array behavior integrated into `Heap.getOwnProperty`, `Heap.ownPropertyKeys`, `Heap.defineOwnProperty`, `Heap.createDataProperty`, and `Heap.deleteProperty`. `ArrayCopy.slice` preserves holes while observing inherited indexed properties and getters, and `ArrayCopy.spread` consumes a live iterator so holes become explicit `undefined` and appends before completion are visible. `Iterator.arrayValues` and `Iterator.next` expose stable iterator identity and ordinary `Get` behavior. `Copy.copyDataProperties`, `Copy.objectAssign`, and `Copy.objectSpread` snapshot keys, re-read descriptors and values in order, run getters, preserve symbol keys and nested reference identity, and retain the `Set` versus `CreateDataProperty` distinction.

Primitive-to-object conversion is explicit. Nullish assignment targets throw; nullish sources are skipped. Boolean, number, bigint, symbol, and string values allocate fresh primitive wrappers. String wrappers expose immutable indexed UTF-16 code-unit properties and length, while the other wrappers have no synthetic enumerable source keys. Primitive `Object.assign` targets return their new wrapper identity.

Runtime review found no unresolved executable-semantics defect within this scoped array/copy/iterator implementation and its tests. The review did require the property-order implementation to sort `(array index, original key)` pairs and return the original stored keys instead of reconstructing keys after sorting. That refactor is present in `OrderedProps.sortedIndices`; it keeps ordering separate from key identity. This result is a source-and-test review result, not a proof-completeness claim.

The compiled scale executable exercised dense and sparse arrays of length 100,000, 100,001 iterator results including one live append, and a 10,000-key spread. Array construction took 96 ms, complete heap validation 133 ms, and own-key enumeration 184 ms. Iterator construction took 101 ms, iteration 71 ms, and final validation 183 ms. Copy-source construction took 229 ms, copying 437 ms, own-key enumeration 2 ms, and validation 15 ms. The complete executable took 2.01 seconds real time. These large-input smoke timings are consistent with the intended near-linear runtime paths; they are machine-local observations under the checked limits, not portable guarantees or complexity proofs.

The manifest records 130 discovered and allowlisted proof declarations, but proof completeness is not claimed. Ten general obligations remain explicit formal debt: four `OrderedProps` obligations for insert preservation, delete preservation, compaction preservation, and exact duplicate-free `ownKeys` correspondence; two heap obligations for public mutation and prototype-mutation preservation; one general blocked-array-shrink theorem; and three hook-conditional preservation obligations for copy operations, iterator operations, and composed `Machine.WellFormed`. The executable invariant checks and concrete theorems do not discharge those obligations. They must be proved before this runtime can support translation certificates that rely on general array, copy, iterator, heap-mutation, or machine preservation.

Commands and results:

```text
$ bun run evidence:generate
$ shasum -a 256 evidence/phase1-arrays-manifest.json
533cdabb76d201e7e52252c5ee52ca465f74dd6e2bff61da6585e082da82a4f8  evidence/phase1-arrays-manifest.json
$ bun run evidence:generate
$ shasum -a 256 evidence/phase1-arrays-manifest.json
533cdabb76d201e7e52252c5ee52ca465f74dd6e2bff61da6585e082da82a4f8  evidence/phase1-arrays-manifest.json

$ bun run evidence:check
$ bun run evidence:baseline:check
$ bun run evidence:primitives:check
$ bun run evidence:heap:check
$ bun run evidence:execution:check
$ bun run evidence:callable:check

$ bun run js:trust
JS trust checks passed: 130 elaborated proof declarations
JS trust gate passed: 130 proof declarations

$ bun scripts/check-js-axioms.mjs --self-test
synthetic environment audit passed

$ cd lean && lake build js-array-scale-tests && /usr/bin/time -p .lake/build/bin/js-array-scale-tests
Build completed successfully (44 jobs).
array-scale dense=100000 sparseLength=100000 constructionMs=96 wellFormedMs=133 ownKeysMs=184 totalMs=413
iterator-scale steps=100001 liveAppends=1 constructionMs=101 iterationMs=71 wellFormedMs=183 totalMs=355
copy-scale keys=10000 constructionMs=229 copyMs=437 ownKeysMs=2 wellFormedMs=15 totalMs=683
real 2.01
user 1.25
sys 0.19

$ bun run verify
Test Files  42 passed (42)
Tests  1603 passed | 8 todo (1611)
Build completed successfully (161 jobs).

$ bun pm pack --dry-run --ignore-scripts
Total files: 273
Unpacked size: 2.22MB

$ git diff --check
```

A deliberately changed arrays manifest hash was rejected by `evidence:check` as stale before the canonical manifest was regenerated. `evidence/phase1-callable-input.json` now resolves every source-derived validation and hash group from immutable revision `5b4da5a67288cf920bcba80d1e897000b73e90f4`; its manifest remains byte-for-byte unchanged at SHA-256 `2223fd8bcf3e36a433976ae42d567b820923c9db7eb7857066452664e391f883`. Current `evidence:generate`, `evidence:check`, and `js:trust` commands target arrays evidence. Explicit baseline, primitive, heap, execution, and callable generate/check commands retain historical reproduction.

The full 161-job build still emits warnings from legacy global runtime and generated/stub modules, including existing `sorry` declarations. Those warnings remain outside the isolated `TSLean.JS` trust boundary and are not suppressed or presented as repository-wide soundness. The direct Lean interpreter also reaches its recursion limit in the 10,000-key copy smoke workload; the checked timing command therefore builds and runs the native `js-array-scale-tests` executable. The JS gate scans the production runtime and barrel, excludes support/test modules, and audits all 130 discovered proof declarations against only `propext`, `Classical.choice`, and `Quot.sound`.

## 2026-08-06 - Phase 1 primitive conversions and operators

This slice is based on `3450468e82ccf70895ba892c636c707d851b4162` on `rebuild/semantic-core`. Its public additions are `CoercionFault`, `Numeric`, primitive `toNumber`, `toNumeric`, `toString`, `toPropertyKey`, and `toPrimitive`; same-domain numeric `add`, `subtract`, `multiply`, `divide`, `remainder`, and `lessThan?`; and primitive `add`, `subtract`, `multiply`, `divide`, `remainder`, `abstractRelationalComparison`, `<`, `>`, `<=`, and `>=`. `ToNumeric` preserves BigInt and applies `ToNumber` otherwise. Arithmetic rejects mixed Number/BigInt domains, BigInt division and remainder use truncation toward zero, zero BigInt divisors produce a RangeError-category fault, addition performs string concatenation after primitive conversion, and relational comparison preserves the specification's unordered result internally before the public operators map it to `false`.

`StringNumericValue` parsing operates on exact UTF-16 code units. It trims every ECMAScript WhiteSpace and LineTerminator code unit, accepts signed decimal and exponent forms, signed `Infinity`, and unsigned `0x`, `0o`, and `0b` forms, and rejects malformed tails, numeric separators, signed radix prefixes, `NaN` text, and lone-surrogate input. String-to-BigInt accepts trimmed signed decimal and unsigned radix-prefixed integer grammar, maps an empty trimmed string to zero, and retains arbitrary-size integer precision. Decimal Number parsing keeps 1,100 significant digits plus a sticky digit, computes exact integer round-to-nearest-even boundaries, and checks the `Float.ofScientific` candidate against that result. Number formatting uses exact binary64 ratios and an integer shortest-roundtrip search; it does not call `Float.toString`. The checked boundary set includes signed zero, infinities, NaNs, subnormal/normal transitions, maximum finite values, the `1e-6`/`1e-7` and `1e20`/`1e21` formatting transitions, values around `2^53`, overflow, underflow, and exact halfway decimal cases.

Number/BigInt equality and ordering do not convert BigInt through Float. `compareBigInt` decomposes finite binary64 values into an exact integer ratio, compares that ratio against the arbitrary-size integer, preserves signed finite ordering, handles infinities directly, and returns unordered for NaN. Mixed relational operators and loose equality use this exact path, including values outside the safe-integer range and fractional Number operands.

The Node differential test builds the `js-primitive-oracle` lake target and compares its output with JavaScript executed by Node. It made 7,133 oracle comparisons: 322 numeric-string parses, 278 binary64 formatting cases, 504 coercion/property-key/loose-equality cases, 24 selected operator/error cases, 5 focused prior-BigInt-defect cases, and 6,000 deterministic seeded operator fuzz cases. The fuzz covers all nine arithmetic and relational operators over undefined, null, booleans, arbitrary binary64 bit patterns, up-to-192-bit signed BigInts, strings, and symbols. These are executable differential observations, not a general ECMAScript correspondence proof.

The isolated scale run parsed 100,000-digit decimal, exponent, whitespace, malformed-UTF-16, and zero-BigInt inputs, then parsed and operated on 10,000-digit decimal and hexadecimal BigInts. The BigInt portion measured 31 ms; the complete interpreted run took 3.56 seconds real time (0.68 user, 0.59 system). The 30-second assertion is a machine-local smoke limit, not a portable performance guarantee or complexity theorem.

The executable TCB ledger is structured separately from proof axioms in `evidence/phase1-primitive-ops-input.json` and its generated manifest. It records Lean's `Float.ofBits`/`Float.toBits`, `Float.add`/`sub`/`mul`/`div`, executable Float less-than, and `Float.ofScientific`. Boundary and differential tests exercise these runtime primitives. No theorem claims that they implement ECMAScript correctly. Formatting, remainder, and exact Number/BigInt comparison use integer algorithms rather than trusted Float formatting, remainder, or mixed-domain conversion.

The manifest records 181 discovered proof declarations allowlisted against `propext`, `Classical.choice`, and `Quot.sound`; this count is not a completeness claim. The ten formal-debt obligations from the arrays slice are carried forward byte-for-byte: four ordered-property preservation/correspondence obligations, two heap preservation obligations, the general blocked-array-shrink obligation, and three hook-conditional copy/iterator/machine preservation obligations. Primitive executable tests and new concrete theorems do not discharge them.

Commands and results:

```text
$ bun run evidence:generate
$ shasum -a 256 evidence/phase1-primitive-ops-manifest.json
797332bca03e552b0a19d75043f771ca33966a6c366542a2bbd46d94dc2f10e9  evidence/phase1-primitive-ops-manifest.json
$ bun run evidence:generate
$ shasum -a 256 evidence/phase1-primitive-ops-manifest.json
797332bca03e552b0a19d75043f771ca33966a6c366542a2bbd46d94dc2f10e9  evidence/phase1-primitive-ops-manifest.json

$ bun run evidence:check
$ bun run evidence:baseline:check
$ bun run evidence:primitives:check
$ bun run evidence:heap:check
$ bun run evidence:execution:check
$ bun run evidence:callable:check
$ bun run evidence:arrays:check

$ bun run js:trust
JS trust checks passed: 181 elaborated proof declarations
JS trust gate passed: 181 proof declarations

$ bun scripts/check-js-axioms.mjs --self-test
synthetic environment audit passed

$ cd lean && lake build js-primitive-oracle && /usr/bin/time -p lake env lean TSLean/JS/PrimitiveScaleTests.lean
Build completed successfully (78 jobs).
primitive-bigint-scale digits=10000 ms=31
real 3.56
user 0.68
sys 0.59

$ bun run verify
Test Files  43 passed (43)
Tests  1609 passed | 8 todo (1617)
Build completed successfully (166 jobs).

$ bun pm pack --dry-run --ignore-scripts
Total files: 279
Unpacked size: 2.27MB

$ git diff --check
```

A deliberately changed primitive-ops source hash was rejected by `evidence:check` as stale at manifest line 167 before regeneration. `evidence/phase1-arrays-input.json` now resolves all source-derived validations and hash groups from immutable revision `3450468e82ccf70895ba892c636c707d851b4162`; its manifest remains byte-for-byte unchanged at SHA-256 `533cdabb76d201e7e52252c5ee52ca465f74dd6e2bff61da6585e082da82a4f8`. Current `evidence:generate`, `evidence:check`, `js:trust`, and `verify` target primitive-ops evidence. Explicit baseline, primitives, heap, execution, callable, and arrays generate/check commands preserve historical reproduction.

The primitive-ops manifest hashes are source `sha256:fa74184c0093d5e56ae5c02c7f1496bc13038d4f3ce800033d8be7966d5aa5f3`, full JS runtime `sha256:07a6194373dfe7b3aa30a70eff52e2dc5fe64d824ee21088a62299f0e5d3ed4b`, corpus `sha256:467348cdf61bd4925e41c764cab7fa289d74b2bcd1e54cba87b225f543cf09ec`, and infrastructure `sha256:b2ba80be809c030f0b392ef81bd176f442abdfd12b0e9e35290aa071e59c9097`. Infrastructure includes the evidence and trust generators, Node differential test, Lean oracle source, and lake target definition. The full build retains existing warnings and `sorry` declarations outside the isolated `TSLean.JS` trust boundary; they are neither suppressed nor presented as repository-wide soundness.

## 2026-08-06 - Phase 1 value-level abstract operations

This slice is based on `3d4da073e94666ff8576b71e80c173420299a58e` on `rebuild/semantic-core`. The public abstract-operation API adds `PreferredType`; `AbstractOperations.getMethod`, `ordinaryToPrimitive`, `toPrimitive`, `toNumber`, `toString`, `toNumeric`, `toPropertyKey`, and `toObject`; `AbstractEquality.looseEqual`, `add`, `relationalComparison`, `lessThan`, `greaterThan`, `lessThanOrEqual`, and `greaterThanOrEqual`; and `Instanceof.reachesPrototype`, `ordinaryHasInstance`, `functionPrototypeHasInstance`, and `instanceofOperator`. `RealmIntrinsics`, `prototypeFor?`, `intrinsicsRefsValid`, `bootstrapTopologyValid`, and `Machine.installRealmIntrinsics` make primitive-wrapper identities and realm installation explicit.

`GetMethod` performs observable property access, treats `undefined` and `null` as absence, and throws for every other non-callable value. `OrdinaryToPrimitive` reads and calls `valueOf`/`toString` in number/default order or `toString`/`valueOf` in string order. `ToPrimitive` dispatches `Symbol.toPrimitive`, passes the requested hint, requires a primitive result, and otherwise uses the ordinary path. The value-level conversions preserve getter/call effects and abrupt completions. `ToObject` preserves valid object identity, throws for nullish values, reports an uninitialized or invalid realm as a model fault, and allocates non-nullish wrappers with the configured realm prototype.

The checked test bootstrap constructs explicit Object, Boolean, Number, String, BigInt, and Symbol prototype identities and an explicit evaluator registry for represented wrapper builtins. Realm installation requires the exact bootstrap topology, distinct valid intrinsic references, and the required prototype kinds/internal slots. That topology is an installation condition, not a permanent immutability rule: legal later prototype mutation preserves stable intrinsic identity and kind validity, wrappers continue to use the configured intrinsic identity, and individual wrapper prototypes remain mutable. `RealmTestSupport.bootstrap` and its builtin registry are executable test support, not production bootstrap or hidden host behavior.

Abstract equality keeps object/object comparison at reference identity and performs at most one object-to-primitive conversion for primitive/object pairs. Addition converts left then right before string concatenation or same-domain numeric addition. Relational operators retain the specified coercion order and preserve the primitive layer's unordered handling. `instanceof` observes custom `Symbol.hasInstance` getter and call effects, converts its result with Boolean coercion, rejects primitive or non-callable right-hand sides as specified, and otherwise follows the current constructor `prototype` by bounded reference-identity traversal. Getter, method, and user-thrown abrupt completions retain their committed trace and state.

The Node differential test builds `js-abstract-operations-oracle` and compares all 97 deterministic Lean results and traces with Node. The scenarios cover exotic and ordinary primitive conversion, `GetMethod`, getter/call ordering and throws, loose equality, addition and relational operators, custom and ordinary `instanceof`, primitive wrappers and their builtins, copy behavior over primitive sources, intrinsic and wrapper prototype mutation, and deterministic wrapper equality samples. These observations do not establish a general ECMAScript refinement theorem.

The manifest records 199 discovered proof declarations allowlisted against `propext`, `Classical.choice`, and `Quot.sound`; this is not a completeness claim. The exact ten formal-debt obligations from arrays and primitive ops remain unchanged. One additional obligation is recorded because `AbstractOperationTheorems.lean` explicitly marks it: characterize `GetMethod` and effectful coercion hooks with a trace/state refinement relation that preserves getter and call ordering. No other abstract-operation formal debt was inferred. Bound-function exotica remain unrepresented, derived construction remains explicitly unsupported, prototype traversal is executable and heap-size bounded, and general effectful equivalence/refinement remains unproved. The four Lean Float executable assumptions from primitive ops are carried forward unchanged and remain runtime assumptions rather than proof axioms.

Commands and results:

```text
$ bun run evidence:generate
$ shasum -a 256 evidence/phase1-abstract-ops-manifest.json
563b457287b300e26aace4d305463f3120e34b00060d1e2ed970de90ce0f9e57  evidence/phase1-abstract-ops-manifest.json
$ bun run evidence:generate
$ shasum -a 256 evidence/phase1-abstract-ops-manifest.json
563b457287b300e26aace4d305463f3120e34b00060d1e2ed970de90ce0f9e57  evidence/phase1-abstract-ops-manifest.json

$ bun run evidence:check
Cannot generate evidence manifest: evidence/phase1-abstract-ops-manifest.json is stale at line 174
$ bun run evidence:generate
$ bun run evidence:check

$ bun run evidence:baseline:check
$ bun run evidence:primitives:check
$ bun run evidence:heap:check
$ bun run evidence:execution:check
$ bun run evidence:callable:check
$ bun run evidence:arrays:check
$ bun run evidence:primitive-ops:check

$ bun run js:trust
JS trust checks passed: 199 elaborated proof declarations
JS trust gate passed: 199 proof declarations

$ bun scripts/check-js-axioms.mjs --self-test
synthetic environment audit passed

$ bun run verify
Test Files  44 passed (44)
Tests  1611 passed | 8 todo (1619)
Build completed successfully (172 jobs).

$ bun pm pack --dry-run --ignore-scripts
Total files: 286
Unpacked size: 2.35MB

$ git diff --check
```

The deliberate manifest tamper changed only the checked source hash, was rejected at that exact line, and was followed by canonical regeneration. `evidence/phase1-primitive-ops-input.json` now resolves every source-derived validation and hash group from immutable revision `3d4da073e94666ff8576b71e80c173420299a58e`; its manifest remains byte-for-byte unchanged at SHA-256 `797332bca03e552b0a19d75043f771ca33966a6c366542a2bbd46d94dc2f10e9`. Current `evidence:generate`, `evidence:check`, `js:trust`, and `verify` target abstract-ops evidence. Explicit baseline, primitives, heap, execution, callable, arrays, and primitive-ops generate/check commands preserve historical reproduction.

The abstract-ops manifest hashes are source `sha256:fa74184c0093d5e56ae5c02c7f1496bc13038d4f3ce800033d8be7966d5aa5f3`, full JS runtime and barrel `sha256:fe8d344efff4f461715a03a1b508f9f1d3f135cd3534f7b65ad9f030383eed30`, corpus `sha256:467348cdf61bd4925e41c764cab7fa289d74b2bcd1e54cba87b225f543cf09ec`, and infrastructure `sha256:77a09f7cc95d2e58d2d253669d41042757625de0b14990a1c11df2a14128675f`. Infrastructure includes both Node differential tests, both Lean oracle sources, the lake targets, trust and evidence scripts, package verification wiring, the synthetic trust fixture, and package-surface test. Existing warnings and `sorry` declarations outside the isolated `TSLean.JS` trust boundary remain visible and are not presented as repository-wide soundness.

## 2026-08-07 - Generic model differential harness

This evidence is based on `be709a49dd663bef8c37545a58a80a8403381839` on `rebuild/semantic-core`. The preceding abstract-operations input now resolves its test, todo, corpus, source, runtime, and infrastructure checks from that immutable revision. Its legacy oracle and differential files remain deleted from the current tree; Git objects at `be709a4` preserve their historical validation and hashes. `evidence:abstract-ops:generate` and `evidence:abstract-ops:check` preserve explicit reproduction alongside every earlier historical command. Current `evidence:generate`, `evidence:check`, `js:trust`, and `verify` target `phase1-differential-input.json`.

The generic protocol is newline-delimited JSON. Each request carries an ID, registered operation, and one or two canonical fixtures; each response repeats the correlated ID and contains either a canonical observation or a protocol error. Number values use unsigned decimal binary64 bits, strings use exact UTF-16 code units, BigInts use canonical decimal, and object/error/symbol identities are structural rather than host stringification. Graph observations assign reference identities in encounter order across completion, trace, selected roots, prototypes, and descriptors. The suite stores no expected Node output.

The JavaScript side executes the registered source against materialized fixtures in an actual Node VM with fresh intrinsic objects. The Lean side is the compiled `js-model-oracle` process. One persistent child serves a batch and is also tested across repeated batches, explicit restart, and a fresh process. The harness rejects CR/LF record injection, malformed or excess output, bad response correlation, missing executables, timeouts, and invalid fixture domains. It allows one active batch, uses a 30-second request timeout, a 5-second close timeout, and a 64 KiB stderr limit, waits for write completion and drain before resolving, and kills a failed child before a later clean start.

The generated manifest contains 16 scenario groups, 734 fixed vectors, 6,530 generated vectors, and 7,264 Node/Lean comparisons. There are 6,088 unique operation/input pairs. The remaining 1,176 entries are intentionally preserved duplicates under `preserved-for-v1-parity`; generation does not silently deduplicate or resample them. The deleted abstract harness is anchored by 97 inventory IDs at `be709a4`.

Corpus coverage is classification accounting, not a conformance percentage: all 102 red entries are present exactly once, with 13 model-covered, 43 compiler-only, 26 model-pending, 11 proof-integrity, and 9 scale entries. Only the 13 exact model-covered entries have bidirectional links to committed model vectors. Compiler-only, pending, proof-integrity, and scale entries are not represented as model coverage.

Validation bounds are part of the measured protocol. Strings contain at most 65,536 UTF-16 code units; array indices are at most 65,535; all nonempty arrays in one graph share an aggregate dense-materialization budget of 65,536 cells. Graphs are additionally capped at 1,024 nodes and bindings, 4,096 properties per node, 65,536 elements per node, 1,024 script events and cases, and 1,024 fixture roots. Both JavaScript and Lean reject over-budget fixtures before materialization.

The differential manifest carries forward all 11 formal-debt obligations unchanged: four ordered-property obligations, two heap obligations, one blocked-array-shrink obligation, three hook-conditional preservation obligations, and one effectful-coercion refinement obligation. It also carries the four executable Float assumptions for bit conversion, arithmetic, ordering, and `Float.ofScientific`. The 199 audited declarations, executable comparisons, and invariant checks do not discharge those obligations or turn the Float assumptions into proof theorems.

Commands and results:

```text
$ bun run evidence:generate
$ shasum -a 256 evidence/phase1-differential-manifest.json
354abd947b6875df7c87ffa4e3eb0abef95cf55ee5578cf232710c4b79f59194  evidence/phase1-differential-manifest.json
$ bun run evidence:generate
$ shasum -a 256 evidence/phase1-differential-manifest.json
354abd947b6875df7c87ffa4e3eb0abef95cf55ee5578cf232710c4b79f59194  evidence/phase1-differential-manifest.json

$ bun run evidence:check
Cannot generate evidence manifest: evidence/phase1-differential-manifest.json is stale at line 191
$ bun run evidence:generate
$ bun run evidence:check

$ bun run evidence:baseline:check
$ bun run evidence:primitives:check
$ bun run evidence:heap:check
$ bun run evidence:execution:check
$ bun run evidence:callable:check
$ bun run evidence:arrays:check
$ bun run evidence:primitive-ops:check
$ bun run evidence:abstract-ops:check

$ bun run differential:check
Differential manifest is current: 7264 vectors
Legacy abstract inventory is current: 97 entries

$ bun run js:trust
JS trust checks passed: 199 elaborated proof declarations
JS trust gate passed: 199 proof declarations

$ bun scripts/check-js-axioms.mjs --self-test
synthetic environment audit passed

$ /usr/bin/time -p ./node_modules/.bin/vitest run tests/js-model-differential.test.ts
Test Files  1 passed (1)
Tests  29 passed (29)
Duration  7.67s (tests 7.20s)
real 8.56
user 4.97
sys 0.95

$ /usr/bin/time -p bun run verify
All matched files use Prettier code style!
Differential manifest is current: 7264 vectors
Legacy abstract inventory is current: 97 entries
JS trust checks passed: 199 elaborated proof declarations
JS trust gate passed: 199 proof declarations
Test Files  43 passed (43)
Tests  1632 passed | 8 todo (1640)
Build completed successfully (172 jobs).
real 102.74
user 127.29
sys 11.64

$ bun pm pack --dry-run --ignore-scripts
Total files: 304
Unpacked size: 7.73MB

$ git diff --check
```

The deliberate tamper changed only the checked source hash and was rejected at that exact manifest line before canonical regeneration. The manifest hashes source `sha256:fa74184c0093d5e56ae5c02c7f1496bc13038d4f3ce800033d8be7966d5aa5f3`, full JS runtime and oracle `sha256:a569c99166aaf9a4f7aaa2827cfac2fe3f6dc79f05397d545222b372132e2051`, corpus `sha256:467348cdf61bd4925e41c764cab7fa289d74b2bcd1e54cba87b225f543cf09ec`, differential specifications and generated inventory `sha256:ba957241f80001ed5eb3b3a71410030bd7b1759d4cb29e02babda6424a8c37ed`, and evidence, trust, generator, harness, test, package, Vitest, and lake infrastructure `sha256:eba39a3065cbdee070498d5f59c6dbccc22199d99b6af3f52d89326727d5e9c6`. The full build retains the existing warnings and `sorry` declarations outside the isolated `TSLean.JS` trust boundary; none were suppressed or changed.

## 2026-08-07 - Compact differential manifest correction

This corrective snapshot is based on `4e0953fa3a5a81b8db24077b0d28ddbcdb397655`. The generated differential manifest now commits to the complete deterministic expansion without storing the 7,264 expanded vectors. Its size is 15,544 bytes, down from 4,995,425 bytes. Its SHA-256 is `a873025e1eb9d01f02be32df63b52fe0a39761382698af7c9b03013e95821ba2`, and its canonical expanded-vector stream hash is `22627c2f8f79a9149d7cbe94de572da1592c50c08bf309c7c68704edcccf2722`.

The compact manifest retains the 16 scenario groups, 734 fixed vectors, 6,530 generated vectors, 7,264 comparisons, 6,088 unique operation/input pairs, 1,176 preserved duplicates, all operation and classification counts, 19 regression tags, and the 97-entry legacy inventory count. Tests regenerate every vector in memory, verify each compact count and hash, run every Node/Lean comparison, reject source/vector/generator digest tampering, verify stable replay IDs, and enforce a 50 KiB manifest limit. No expected outcomes or expanded fixture list are checked in.

The corrective evidence manifest is `evidence/phase1-differential-compact-manifest.json` at SHA-256 `66b643a832525bf85beeb5012ac405dcb775fdfc8bee89bd3473d7097a9bea3e`. It records differential-spec hash `sha256:d3b15082682a4e357e1b3f8c5feb0dd9a5d6a544b860987abbb7e874474c92df` and infrastructure hash `sha256:4fb40742ef0c091dc62a51cd393390e363aa76b4ed907f7146ce58e5803c5b05`. The preceding `phase1-differential-manifest.json` remains unchanged at `354abd947b6875df7c87ffa4e3eb0abef95cf55ee5578cf232710c4b79f59194`; its input now resolves hash groups from immutable `4e0953f` objects so the historical check no longer reinterprets the compact current tree.

## 2026-08-07 - Ordered-property proofs

This proof snapshot is based on `04d31a1dc46450ba532c5553b9ebadf3784f5bba` on `rebuild/semantic-core`. The preceding compact differential input now resolves all source-derived validations and hashes from that immutable revision. Its manifest remains byte-for-byte unchanged at SHA-256 `66b643a832525bf85beeb5012ac405dcb775fdfc8bee89bd3473d7097a9bea3e`, and explicit `evidence:differential-compact:generate` and `evidence:differential-compact:check` commands preserve its historical reproduction alongside every earlier evidence command. Current `evidence:generate`, `evidence:check`, `js:trust`, and `verify` target `phase2-ordered-props-input.json`.

The audit discovers these exact new general theorems under `TSLean.JS.OrderedProps`: `metadataConsistent_iff_valid`, `isWellFormed_iff_valid`, `wellFormed_iff_valid`, `insert_wellFormed`, `delete_wellFormed`, `lookup_insert_same`, `lookup_insert_ne`, `lookup_delete_same`, `lookup_delete_ne`, `mem_ownKeys_iff_lookup_isSome`, `ownKeys_nodup`, `arrayIndices_nodup`, `ownKeys_length`, `ownKeys_indices_ascending`, `ownKeys_partition`, and `ownKeys_eq_projections`.

The exact transition theorems are `arrayIndices_insert_existing`, `stringKeys_insert_existing`, `symbolKeys_insert_existing`, `ownKeys_insert_existing`, `arrayIndices_insert_nonIndex_string`, `orderedKeys_insert_fresh_string`, `arrayIndices_insert_symbol`, `orderedKeys_insert_fresh_symbol`, `arrayIndices_insert_fresh_index`, `orderedKeys_insert_fresh_index`, `orderedKeys_delete`, `arrayIndices_delete_nonIndex_string`, `arrayIndices_delete_symbol`, `arrayIndices_delete_index`, `ownKeys_delete`, `projections_delete_insert_string`, `projections_delete_insert_symbol`, and `ownKeys_delete_insert_index`.

Review approval is scoped to closing the four recorded OrderedProps obligations: complete insertion preservation including compaction branches, complete deletion preservation, string and symbol compaction preservation, and duplicate-free exact `ownKeys` correspondence and ordering. The general and transition theorem statements, elaborated-environment audit, explicit transition discovery fixture, and complete verification gate support that reduction. This approval does not claim complete `Heap.WellFormed` preservation. The seven existing obligations remain unchanged: two heap/prototype obligations, one blocked-array-shrink obligation, three hook-conditional obligations, and one effectful-coercion refinement obligation. The four executable Float assumptions are also carried forward unchanged and remain runtime assumptions rather than proof axioms.

The phase-2 manifest records source `sha256:fa74184c0093d5e56ae5c02c7f1496bc13038d4f3ce800033d8be7966d5aa5f3`, JS runtime `sha256:adb67de8f37029cb1ad7041188e72573d3c0ee7f38e9a820de9512920ba1c1fd`, corpus `sha256:467348cdf61bd4925e41c764cab7fa289d74b2bcd1e54cba87b225f543cf09ec`, differential specifications and harness `sha256:6386c60110ee9bfae81fcb9fd013faf6112254af96502accd7203221a240993e`, proof tests and audit `sha256:abf9a5876478d1d597353267b09cd914012f594122a80a909622b7b2db40303c`, and trust/evidence infrastructure `sha256:f1e4a8083768e65b30960230ccd16f5fdff7089aa8b436757110f5bc84a1b4b1`.

Commands and results:

```text
$ bun run evidence:generate
$ shasum -a 256 evidence/phase2-ordered-props-manifest.json
008bdb172fcd36a53e38369b05e90eb2782a0e7f59409f4c0e187cb0c38aba4b  evidence/phase2-ordered-props-manifest.json
$ bun run evidence:generate
$ shasum -a 256 evidence/phase2-ordered-props-manifest.json
008bdb172fcd36a53e38369b05e90eb2782a0e7f59409f4c0e187cb0c38aba4b  evidence/phase2-ordered-props-manifest.json

$ bun run evidence:check
Cannot generate evidence manifest: evidence/phase2-ordered-props-manifest.json is stale at line 170
$ bun run evidence:generate
$ bun run evidence:check

$ bun run evidence:baseline:check
$ bun run evidence:primitives:check
$ bun run evidence:heap:check
$ bun run evidence:execution:check
$ bun run evidence:callable:check
$ bun run evidence:arrays:check
$ bun run evidence:primitive-ops:check
$ bun run evidence:abstract-ops:check
$ bun run evidence:differential:check
$ bun run evidence:differential-compact:check
$ bun run evidence:ordered-props:check

$ bun run differential:check
Differential manifest is current: 7264 vectors
Legacy abstract inventory is current: 97 entries

$ bun run js:trust
JS trust checks passed: 233 elaborated proof declarations
JS trust gate passed: 233 proof declarations

$ bun scripts/check-js-axioms.mjs --self-test
synthetic environment audit passed

$ /usr/bin/time -p bun run verify
All matched files use Prettier code style!
Differential manifest is current: 7264 vectors
Legacy abstract inventory is current: 97 entries
JS trust checks passed: 233 elaborated proof declarations
JS trust gate passed: 233 proof declarations
Test Files  43 passed (43)
Tests  1633 passed | 8 todo (1641)
Build completed successfully (172 jobs).
real 148.20
user 167.24
sys 12.62

$ bun pm pack --dry-run --ignore-scripts
Total files: 304
Unpacked size: 2.93MB

$ git diff --check
```

The deliberate tamper changed only the checked source hash and was rejected at that exact manifest line before canonical regeneration. The 233 audited declarations and executable tests support only the theorem statements listed above; they do not discharge the remaining heap, prototype, array, hook-conditional, or effectful-refinement obligations. Existing warnings and `sorry` declarations outside the isolated `TSLean.JS` trust boundary remain visible and were not suppressed or changed.

## 2026-08-07 - Heap allocation preservation

This proof snapshot is based on `54ca2aac56c74745a496f23f34176fe521c1c5e3` on `rebuild/semantic-core`. The ordered-properties input now resolves every source-derived validation and hash from that immutable revision. Its manifest remains byte-for-byte unchanged at SHA-256 `008bdb172fcd36a53e38369b05e90eb2782a0e7f59409f4c0e187cb0c38aba4b`, and its explicit generate/check commands remain available with all earlier historical commands. Current `evidence:generate`, `evidence:check`, `js:trust`, and `verify` target `phase2-heap-allocation-input.json`.

Review approved these exact general preservation theorems and premises under `TSLean.JS.Heap`:

- `allocate_preserves_wellFormed`: `heap.WellFormed` and `heap.allocate prototype extensible = .ok (ref, next)` imply `next.WellFormed`.
- `allocatePrimitiveWrapper_preserves_wellFormed`: `heap.WellFormed` and `heap.allocatePrimitiveWrapper value prototype = .ok (ref, next)` imply `next.WellFormed`.
- `allocateArray_preserves_wellFormed`: `heap.WellFormed` and `heap.allocateArray elements prototype = .ok (ref, next)` imply `next.WellFormed`.
- `allocateFunction_preserves_wellFormed`: `heap.WellFormed` and `heap.allocateFunction environment kind constructible prototype homeObject constructorMode lexicalThis = .ok (ref, next)` imply `next.WellFormed`; captured-environment validity remains a machine-layer obligation.
- `allocateConstructorPair_preserves_wellFormed`: `heap.WellFormed` and `heap.allocateConstructorPair environment functionPrototype objectPrototype classConstructor constructorMode = .ok (constructor, prototype, next)` imply `next.WellFormed`; captured-environment validity remains a machine-layer obligation.
- `allocateArrayIterator_preserves_wellFormed`: `heap.WellFormed` and `heap.allocateArrayIterator target prototype = .ok (ref, next)` imply `next.WellFormed`.
- `deleteProperty_preserves_wellFormed`: for either returned `success : Bool`, `heap.WellFormed` and `heap.deleteProperty ref key = .ok (success, next)` imply `next.WellFormed`.
- `preventExtensions_preserves_wellFormed`: `heap.WellFormed` and `heap.preventExtensions ref = .ok next` imply `next.WellFormed`.

The six allocation families are ordinary objects, primitive wrappers, arrays, functions, atomic constructor/prototype pairs, and array iterators. General deletion and `preventExtensions` preservation are also approved. The generic evidence schema does not admit a `formalProgress` field, so this progress and review status are recorded here while the manifest carries only validated measurement counts.

This approval is deliberately narrower than the `heap-public-mutation-preservation` obligation. General successful `defineOwnProperty` and `createDataProperty` preservation remains open, so that obligation is not removed. General `setPrototypeOf` preservation and prototype-graph validity remain open under `heap-prototype-preservation`. The other unchanged debt is blocked array shrink, copy/assign/spread/slice hook-conditional preservation, iterator allocation and advancement under preserving hooks, composed machine hook-conditional preservation, and effectful coercion trace/state refinement. The formal debt therefore remains exactly seven obligations: two heap/prototype, one array, three hook-conditional, and one effectful-equivalence obligation. The four executable Float assumptions are carried forward unchanged as runtime assumptions, not proof axioms.

The phase-2 manifest records source `sha256:fa74184c0093d5e56ae5c02c7f1496bc13038d4f3ce800033d8be7966d5aa5f3`, JS runtime `sha256:25150fe2d245718fc511f65f39e583fefd2d54124665bb769d5fab0483fbccb5`, corpus `sha256:467348cdf61bd4925e41c764cab7fa289d74b2bcd1e54cba87b225f543cf09ec`, differential specifications and harness `sha256:6386c60110ee9bfae81fcb9fd013faf6112254af96502accd7203221a240993e`, proof tests and audit `sha256:abf9a5876478d1d597353267b09cd914012f594122a80a909622b7b2db40303c`, and trust/evidence infrastructure `sha256:628418e3e45c715b5ff7c3ad8e0f518656f0a64efbe430aba8a7b5a01c9119e`. The manifest SHA-256 is `580fb1a872b2884e94a4f320c55af237546a2e5dd7f7c1faf2996595706ead27`.

Commands and results:

```text
$ bun run evidence:generate
$ bun run evidence:check

$ bun run evidence:check
Cannot generate evidence manifest: evidence/phase2-heap-allocation-manifest.json is stale at line 170
-     "source": "sha256:0a74184c0093d5e56ae5c02c7f1496bc13038d4f3ce800033d8be7966d5aa5f3",
+     "source": "sha256:fa74184c0093d5e56ae5c02c7f1496bc13038d4f3ce800033d8be7966d5aa5f3",
$ bun run evidence:generate
$ bun run evidence:check

$ bun run evidence:baseline:check
$ bun run evidence:primitives:check
$ bun run evidence:heap:check
$ bun run evidence:execution:check
$ bun run evidence:callable:check
$ bun run evidence:arrays:check
$ bun run evidence:primitive-ops:check
$ bun run evidence:abstract-ops:check
$ bun run evidence:differential:check
$ bun run evidence:differential-compact:check
$ bun run evidence:ordered-props:check
$ bun run evidence:heap-allocation:check

$ bun run differential:check
Differential manifest is current: 7264 vectors
Legacy abstract inventory is current: 97 entries

$ bun run js:trust
JS trust checks passed: 252 elaborated proof declarations
JS trust gate passed: 252 proof declarations

$ bun scripts/check-js-axioms.mjs --self-test
synthetic environment audit passed

$ /usr/bin/time -p bun run verify
All matched files use Prettier code style!
Differential manifest is current: 7264 vectors
Legacy abstract inventory is current: 97 entries
JS trust checks passed: 252 elaborated proof declarations
JS trust gate passed: 252 proof declarations
Test Files  43 passed (43)
Tests  1633 passed | 8 todo (1641)
Build completed successfully (172 jobs).
real 115.69
user 157.02
sys 16.94

$ bun pm pack --dry-run --ignore-scripts
Total files: 304
Unpacked size: 3.0MB

$ shasum -a 256 evidence/phase2-ordered-props-manifest.json evidence/phase2-heap-allocation-manifest.json
008bdb172fcd36a53e38369b05e90eb2782a0e7f59409f4c0e187cb0c38aba4b  evidence/phase2-ordered-props-manifest.json
580fb1a872b2884e94a4f320c55af237546a2e5dd7f7c1faf2996595706ead27  evidence/phase2-heap-allocation-manifest.json

$ git diff --check
```

The deliberate tamper changed only the checked source hash and was rejected at that exact manifest line before canonical regeneration. The 252 audited declarations and complete verification gate support only the theorem statements and premises above. They do not discharge the remaining define/create, prototype, blocked-array-shrink, hook-conditional, or effectful-refinement obligations. Existing warnings and `sorry` declarations outside the isolated `TSLean.JS` trust boundary remain visible and were not suppressed or changed.

## 2026-08-07 - Array shrink closure

This proof snapshot is based on `ac8ad990e39863a9eedb3ffdcd61b8b2c663aade` on `rebuild/semantic-core`. The heap-allocation input now resolves every source-derived validation and hash from that immutable revision. Its manifest remains byte-for-byte unchanged at SHA-256 `580fb1a872b2884e94a4f320c55af237546a2e5dd7f7c1faf2996595706ead27`, and its explicit generate/check commands remain available with all earlier historical commands. Current `evidence:generate`, `evidence:check`, `js:trust`, and `verify` target `phase2-array-shrink-input.json`.

Review approved these exact public closure theorems under `TSLean.JS.Heap`:

- `defineOwnProperty_blocked_array_shrink`: a well-formed array, a valid normalized and accepted length descriptor, a strict shrink from a writable length, and `defineOwnProperty ... = .ok (false, next)` expose a blocker at or above the requested length. The old blocker is nonconfigurable; every higher old index is configurable and absent from the final properties; indices at or below the blocker, non-index strings, symbols, and both key-order projections are unchanged; the target keeps its prototype and extensibility and receives length `blocked + 1`; every other object is unchanged; accepted writability is exact, including a requested `false`; and `next.WellFormed`.
- `defineOwnProperty_unblocked_array_shrink`: under the same well-formedness, normalization, acceptance, strict-shrink, and writable-length premises, `defineOwnProperty ... = .ok (true, next)` deletes every old configurable index at or above the requested length. Lower indices, non-index strings, symbols, and both key-order projections are unchanged; the target keeps its prototype and extensibility and receives the requested length; every other object is unchanged; accepted writability is exact, including a requested `false`; and `next.WellFormed`.

`DescriptorUpdate.applyValidatedDescriptor_data_writable` supplies the shared derived fact used by both closure theorems: every successful data-to-data `applyValidatedDescriptor` result satisfies `final.writable = update.writable.apply current.writable`. The private theorems `defineOwnProperty_blocked_array_shrink_nonvacuous` and `defineOwnProperty_unblocked_array_shrink_nonvacuous` provide concrete writable-to-nonwritable witnesses. The blocked fixture returns `false`, commits length `blocked + 1`, exposes a nonwritable synthetic length descriptor, and remains well-formed; the unblocked fixture returns `true`, commits length `1` with a nonwritable synthetic length descriptor, and remains well-formed.

Allocation/delete/prevent preservation remains approved subprogress toward the broader heap obligation. `allocateArrayFromArray_preserves_wellFormed` now covers successful array-input allocation directly, alongside the six previously approved allocation families. `deleteProperty_preserves_wellFormed` covers both returned success values, and `preventExtensions_preserves_wellFormed` covers successful prevention. These results do not close general successful `defineOwnProperty` or `createDataProperty`, so `heap-public-mutation-preservation` remains open. General `setPrototypeOf` preservation and prototype-graph validity remain open under `heap-prototype-preservation`.

Review approved removing exactly `array-blocked-shrink-general`. The canonical formal debt is now exactly six obligations: `heap-public-mutation-preservation`, `heap-prototype-preservation`, `copy-hook-conditional-preservation`, `iterator-hook-conditional-preservation`, `machine-hook-conditional-preservation`, and `abstract-effectful-coercion-refinement`. No prototype, hook-conditional, or effectful-refinement debt was removed. The four executable Float assumptions and all differential metrics are carried forward unchanged as runtime evidence, not proof axioms.

The array-shrink manifest records source `sha256:fa74184c0093d5e56ae5c02c7f1496bc13038d4f3ce800033d8be7966d5aa5f3`, JS runtime `sha256:8fc060cf7c23bf15fa7c3b4dd205634b3d973adade5dca050c62a76d106cd8b6`, corpus `sha256:467348cdf61bd4925e41c764cab7fa289d74b2bcd1e54cba87b225f543cf09ec`, differential specifications and harness `sha256:6386c60110ee9bfae81fcb9fd013faf6112254af96502accd7203221a240993e`, proof tests and audit `sha256:abf9a5876478d1d597353267b09cd914012f594122a80a909622b7b2db40303c`, and trust/evidence infrastructure `sha256:941cf23075dd9109bd50a567201224cec01616f12de2ae5881a9f54aee91d05c`. The manifest SHA-256 is `3ce23701f655186504c498bfcdfc901f2ca8adebac5bd6cfad769987cbf960f4`.

Commands and results:

```text
$ bun run evidence:generate
$ bun run evidence:check

$ bun run evidence:baseline:check
$ bun run evidence:primitives:check
$ bun run evidence:heap:check
$ bun run evidence:execution:check
$ bun run evidence:callable:check
$ bun run evidence:arrays:check
$ bun run evidence:primitive-ops:check
$ bun run evidence:abstract-ops:check
$ bun run evidence:differential:check
$ bun run evidence:differential-compact:check
$ bun run evidence:ordered-props:check
$ bun run evidence:heap-allocation:check
$ bun run evidence:array-shrink:check

$ bun run differential:check
Differential manifest is current: 7264 vectors
Legacy abstract inventory is current: 97 entries

$ bun run js:trust
JS trust checks passed: 259 elaborated proof declarations
JS trust gate passed: 259 proof declarations

$ bun scripts/check-js-axioms.mjs --self-test
synthetic environment audit passed

$ /usr/bin/time -p bun run verify
All matched files use Prettier code style!
Differential manifest is current: 7264 vectors
Legacy abstract inventory is current: 97 entries
JS trust checks passed: 259 elaborated proof declarations
JS trust gate passed: 259 proof declarations
Test Files  43 passed (43)
Tests  1633 passed | 8 todo (1641)
Build completed successfully (172 jobs).
real 86.91
user 110.32
sys 8.42

$ bun pm pack --dry-run --ignore-scripts
Total files: 304
Unpacked size: 3.14MB

$ shasum -a 256 evidence/phase2-heap-allocation-manifest.json evidence/phase2-array-shrink-manifest.json
580fb1a872b2884e94a4f320c55af237546a2e5dd7f7c1faf2996595706ead27  evidence/phase2-heap-allocation-manifest.json
3ce23701f655186504c498bfcdfc901f2ca8adebac5bd6cfad769987cbf960f4  evidence/phase2-array-shrink-manifest.json

$ git diff --check
```

The 259 audited declarations and complete verification gate support only the theorem statements and premises above. They do not discharge general define/create preservation, prototype preservation, any hook-conditional obligation, or effectful coercion refinement. Existing warnings and `sorry` declarations outside the isolated `TSLean.JS` trust boundary remain visible and were not suppressed or changed.

## 2026-08-07 - Heap public mutation preservation

This proof snapshot is based on `ec7b896f0fbdb639e22d1ae69a6a89e878f51c9c` on `rebuild/semantic-core`. The array-shrink input now resolves every source-derived validation and hash from that immutable revision. Its manifest remains byte-for-byte unchanged at SHA-256 `3ce23701f655186504c498bfcdfc901f2ca8adebac5bd6cfad769987cbf960f4`, and its explicit generate/check commands remain available with all earlier historical commands. Current `evidence:generate`, `evidence:check`, `js:trust`, and `verify` target `phase2-heap-mutation-input.json`.

Review approved this exact public preservation coverage under `TSLean.JS.Heap`:

- `defineOwnProperty_preserves_wellFormed`: for every returned `success : Bool`, `heap.WellFormed` and `heap.defineOwnProperty ref key update = .ok (success, next)` imply `next.WellFormed`. This covers rejected definitions that return the original heap, ordinary/function/array-iterator storage, primitive-wrapper synthetic rejection and ordinary storage, array-index writes and extension, array-length growth and unchanged length, and both blocked and unblocked shrink commits.
- `createDataProperty_preserves_wellFormed`: for every returned `success : Bool`, the public `createDataProperty` boundary preserves complete `Heap.WellFormed` as a direct instance of the definition theorem.
- `deleteProperty_preserves_wellFormed`: both returned Boolean results preserve complete `Heap.WellFormed`.
- `preventExtensions_preserves_wellFormed`: every successful public prevention result preserves complete `Heap.WellFormed`.
- Allocation preservation remains complete for the seven exposed families: ordinary objects, primitive wrappers, empty arrays, arrays initialized from arrays, functions, atomic constructor/prototype pairs, and array iterators. `PublicMutationPreservation` exports these allocation theorems with the define/create/delete/prevent theorems as one reviewed registry.

The private witnesses `defineOwnProperty_ordinary_nonvacuous`, `defineOwnProperty_array_extension_nonvacuous`, `defineOwnProperty_wrapper_nonvacuous`, `createDataProperty_object_reference_nonvacuous`, and `defineOwnProperty_blocked_false_preservation_nonvacuous` instantiate successful ordinary definition, successful array-index extension, primitive-wrapper rejection and storage, object-reference data creation, and a blocked false shrink commit. Together with the prior blocked and unblocked shrink witnesses, they ensure the general public theorems are exercised on successful and state-committing branches rather than only unchanged-heap rejection paths.

Review approved removing exactly `heap-public-mutation-preservation`. The canonical formal debt is now exactly five obligations: `heap-prototype-preservation`, `copy-hook-conditional-preservation`, `iterator-hook-conditional-preservation`, `machine-hook-conditional-preservation`, and `abstract-effectful-coercion-refinement`. Iterator allocation is proved, but iterator advancement and its ordinary `Get` effects remain open. General `setPrototypeOf` preservation and prototype-graph validity remain open. Copy/assign/spread/slice preservation under preserving hooks, composed machine preservation under preserving hooks, and effectful coercion trace/state refinement also remain open. No prototype, iterator, hook-conditional, or effectful-refinement debt was removed.

The four executable Float assumptions are carried forward unchanged as runtime assumptions, not proof axioms. The measured suite remains 43 files, 1,633 passing tests, 8 todos, 172 Lean jobs, and 102 red corpus entries. Differential evidence remains 16 scenario groups, 734 fixed plus 6,530 generated comparisons for 7,264 total, 6,088 unique operation inputs, 1,176 preserved duplicates, 97 legacy inventory IDs, the unchanged 102-entry coverage partition, and a 65,536-cell aggregate fixture budget.

The heap-mutation manifest records source `sha256:fa74184c0093d5e56ae5c02c7f1496bc13038d4f3ce800033d8be7966d5aa5f3`, JS runtime `sha256:8b6f5ff42b89127d9d33921faf66e5ad6eddfd50a79c0852f0f7fdb420e05af3`, corpus `sha256:467348cdf61bd4925e41c764cab7fa289d74b2bcd1e54cba87b225f543cf09ec`, differential specifications and harness `sha256:6386c60110ee9bfae81fcb9fd013faf6112254af96502accd7203221a240993e`, proof tests and audit `sha256:abf9a5876478d1d597353267b09cd914012f594122a80a909622b7b2db40303c`, and trust/evidence infrastructure `sha256:2ce098f810ecbfce9a42e5d414cab5357d82b19448068004f9eed38c45f96af2`. The manifest SHA-256 is `d5285178f96b87531c7ccde070ceb12b355152f0de390a13aceebf10e835a895`.

Commands and results:

```text
$ bun run evidence:generate
$ bun run evidence:check

$ bun run evidence:baseline:check
$ bun run evidence:primitives:check
$ bun run evidence:heap:check
$ bun run evidence:execution:check
$ bun run evidence:callable:check
$ bun run evidence:arrays:check
$ bun run evidence:primitive-ops:check
$ bun run evidence:abstract-ops:check
$ bun run evidence:differential:check
$ bun run evidence:differential-compact:check
$ bun run evidence:ordered-props:check
$ bun run evidence:heap-allocation:check
$ bun run evidence:array-shrink:check
$ bun run evidence:heap-mutation:check

$ bun run differential:check
Differential manifest is current: 7264 vectors
Legacy abstract inventory is current: 97 entries

$ bun run js:trust
JS trust checks passed: 262 elaborated proof declarations
JS trust gate passed: 262 proof declarations

$ bun scripts/check-js-axioms.mjs --self-test
synthetic environment audit passed

$ /usr/bin/time -p bun run verify
All matched files use Prettier code style!
Differential manifest is current: 7264 vectors
Legacy abstract inventory is current: 97 entries
JS trust checks passed: 262 elaborated proof declarations
JS trust gate passed: 262 proof declarations
Test Files  43 passed (43)
Tests  1633 passed | 8 todo (1641)
Build completed successfully (172 jobs).
real 141.56
user 180.62
sys 23.87

$ bun pm pack --dry-run --ignore-scripts
Total files: 304
Unpacked size: 3.19MB

$ shasum -a 256 evidence/phase2-array-shrink-manifest.json evidence/phase2-heap-mutation-manifest.json
3ce23701f655186504c498bfcdfc901f2ca8adebac5bd6cfad769987cbf960f4  evidence/phase2-array-shrink-manifest.json
d5285178f96b87531c7ccde070ceb12b355152f0de390a13aceebf10e835a895  evidence/phase2-heap-mutation-manifest.json

$ git diff --check
```

The 262 audited declarations and complete verification gate support only the theorem statements and premises above. They do not discharge prototype mutation, iterator advancement, hook-conditional preservation, or effectful coercion refinement. Existing warnings and `sorry` declarations outside the isolated `TSLean.JS` trust boundary remain visible and were not suppressed or changed.

## 2026-08-07 - Prototype preservation

This proof snapshot is based on `926e4924a367d40e72f0f4d403efd6e0030d18f6` on `rebuild/semantic-core`. The heap-mutation input now resolves every source-derived validation and hash from that immutable revision. Its manifest remains byte-for-byte unchanged at SHA-256 `d5285178f96b87531c7ccde070ceb12b355152f0de390a13aceebf10e835a895`, and its explicit generate/check commands remain available with all earlier historical commands. Current `evidence:generate`, `evidence:check`, `js:trust`, and `verify` target `phase2-prototype-input.json`.

The audit adds exactly these six declarations under `TSLean.JS.Heap`: `PrototypePath.nil`, `PrototypePath.cons`, `failed_setPrototypeOf_preserves_heap`, `prototypeAcyclic_terminates`, `prototypeGraphAcyclic_iff`, and `setPrototypeOf_preserves_wellFormed`. `prototypeGraphAcyclic_iff` states that, under valid stored prototype references, the executable color checker accepts exactly the logically acyclic prototype graphs. `prototypeAcyclic_terminates` supplies finite-chain termination from reference validity and logical acyclicity. The private `reachesWithFuel_true_iff` and `reachesWithFuel_false_iff` connect the heap-sized executable traversal to logical reachability and non-reachability on well-formed heaps.

`setPrototypeOf_preserves_wellFormed` covers every ordinary returned branch: unchanged same-prototype success, nonextensible rejection, cycle rejection, successful assignment to a valid parent, and successful assignment to `null`. Malformed references and traversal faults remain errors rather than ordinary Boolean results. The concrete witnesses exercise both successful assignments and all three unchanged/rejected branches. `PublicMutationPreservation` now exports the prototype theorem beside the previously approved allocation, define/create, delete, and prevent-extensions preservation theorems.

Review approved removing exactly `heap-prototype-preservation`. The canonical formal debt is now exactly four obligations: `copy-hook-conditional-preservation`, `iterator-hook-conditional-preservation`, `machine-hook-conditional-preservation`, and `abstract-effectful-coercion-refinement`. Iterator advancement and its ordinary `Get` effects remain open, as do copy/assign/spread/slice preservation under preserving hooks, composed machine preservation under preserving hooks, and effectful coercion trace/state refinement. No hook-conditional or effectful-equivalence debt was removed.

The four executable Float assumptions are carried forward unchanged as runtime assumptions, not proof axioms. The measured suite remains 43 files, 1,633 passing tests, 8 todos, 172 Lean jobs, and 102 red corpus entries. Differential evidence remains 16 scenario groups, 734 fixed plus 6,530 generated comparisons for 7,264 total, 6,088 unique operation inputs, 1,176 preserved duplicates, 97 legacy inventory IDs, the unchanged 102-entry coverage partition, and a 65,536-cell aggregate fixture budget.

The 10,000-depth prototype regression performs a safe deep prototype assignment and rejects a deep cycle, checks the resulting heaps remain well-formed, and retains the existing deep `instanceof` lookup. One isolated run measured 4 ms to build the chain, 2 ms for the safe assignment, 2 ms for cycle rejection, 0 ms for lookup, and 187 ms for validity; the complete run took 1.35 seconds real time. The full verification replay measured 5 ms, 2 ms, 3 ms, 0 ms, and 228 ms respectively. These are machine-local regression observations under 1,000 ms assignment, rejection, and lookup limits, not portable performance guarantees or complexity proofs.

The prototype manifest records source `sha256:fa74184c0093d5e56ae5c02c7f1496bc13038d4f3ce800033d8be7966d5aa5f3`, JS runtime `sha256:a934f029dbb983df2187922874f69fac6b18eca1f36e76f466a92b0cebf805d6`, corpus `sha256:467348cdf61bd4925e41c764cab7fa289d74b2bcd1e54cba87b225f543cf09ec`, differential specifications and harness `sha256:6386c60110ee9bfae81fcb9fd013faf6112254af96502accd7203221a240993e`, proof tests and audit `sha256:abf9a5876478d1d597353267b09cd914012f594122a80a909622b7b2db40303c`, and trust/evidence infrastructure `sha256:1332dbc26b680a01815acb7e79277fe3d240567b27091e040819d0e49bf500fb`. The manifest SHA-256 is `aecb383818b16b75343b5fbeccce345e7216b5240a5ce1d32008b597e3c62722`.

Commands and results:

```text
$ bun run evidence:baseline:check
$ bun run evidence:primitives:check
$ bun run evidence:heap:check
$ bun run evidence:execution:check
$ bun run evidence:callable:check
$ bun run evidence:arrays:check
$ bun run evidence:primitive-ops:check
$ bun run evidence:abstract-ops:check
$ bun run evidence:differential:check
$ bun run evidence:differential-compact:check
$ bun run evidence:ordered-props:check
$ bun run evidence:heap-allocation:check
$ bun run evidence:array-shrink:check
$ bun run evidence:heap-mutation:check
$ bun run evidence:prototype:check

$ bun run differential:check
Differential manifest is current: 7264 vectors
Legacy abstract inventory is current: 97 entries

$ bun run js:trust
JS trust checks passed: 268 elaborated proof declarations
JS trust gate passed: 268 proof declarations

$ bun scripts/check-js-axioms.mjs --self-test
synthetic environment audit passed

$ cd lean && /usr/bin/time -p lake env lean TSLean/JS/FunctionScaleTests.lean
function-scale allocations=100000 buildMs=65 validityMs=683
prototype-scale depth=10000 buildMs=4 safeSetMs=2 cycleRejectMs=2 lookupMs=0 validityMs=187
real 1.35
user 1.19
sys 0.15

$ /usr/bin/time -p bun run verify
All matched files use Prettier code style!
Differential manifest is current: 7264 vectors
Legacy abstract inventory is current: 97 entries
JS trust checks passed: 268 elaborated proof declarations
JS trust gate passed: 268 proof declarations
Test Files  43 passed (43)
Tests  1633 passed | 8 todo (1641)
Build completed successfully (172 jobs).
real 72.53
user 104.91
sys 7.57

$ bun pm pack --dry-run --ignore-scripts
Total files: 304
Unpacked size: 3.25MB

$ shasum -a 256 evidence/phase2-heap-mutation-manifest.json evidence/phase2-prototype-manifest.json
d5285178f96b87531c7ccde070ceb12b355152f0de390a13aceebf10e835a895  evidence/phase2-heap-mutation-manifest.json
aecb383818b16b75343b5fbeccce345e7216b5240a5ce1d32008b597e3c62722  evidence/phase2-prototype-manifest.json

$ git diff --check
```

The 268 audited declarations and complete verification gate support only the theorem statements and branches above. They do not discharge iterator advancement, the three hook-conditional obligations, or effectful coercion refinement. Existing warnings and `sorry` declarations outside the isolated `TSLean.JS` trust boundary remain visible and were not suppressed or changed.

## 2026-08-08 - Hook, iterator, and copy preservation

This proof snapshot is based on `533fe9fa986c722ac13f8182a0492b0f1e4d4ff3` on `rebuild/semantic-core`. The prototype input now resolves every source-derived validation and hash from that immutable revision. Its manifest remains byte-for-byte unchanged at SHA-256 `aecb383818b16b75343b5fbeccce345e7216b5240a5ce1d32008b597e3c62722`, and its explicit generate/check commands remain available with all earlier historical commands. Current `evidence:generate`, `evidence:check`, `js:trust`, and `verify` target `phase2-hook-copy-input.json`.

The preservation contract now tracks identity continuity as well as final validity. `ObjectKind.ContinuesFrom` preserves internal-method categories, exact function and primitive-wrapper metadata, and array-iterator target identity while allowing mutable array and iterator state to advance. `Heap.ContinuesFrom` retains every old reference with a permitted same-category transition, never shrinks the heap, and preserves old value validity; `Heap.MachineReferencesPreserved` additionally retains function-environment metadata. `Cell.ContinuesFrom` preserves mutability, `EnvironmentRecord.ContinuesFrom` preserves ancestry and every existing name-to-cell binding, and `Machine.ContinuesFrom` composes heap, cell, environment, intrinsic, and current-environment continuity while allowing committed platform, trace, fuel, initialized-cell, and new-binding changes. These relations are reflexive and transitive and are connected to complete `Machine.WellFormed` preservation.

`RunResult.MachinePreserved`, `CompletionValuesValid`, `JSM.PreservesWellFormed`, `JSM.PreservesWellFormedWhen`, `JSM.PreservesResults`, and `JSM.PreservesResultsWhen` make terminal-state continuity and escaping-value validity explicit. Their composition theorems cover pure/bind, conditional preconditions, state and heap updates, trace emission, fuel, and every abrupt completion. Environment proofs cover global/child allocation, declaration, initialization, resolution, reads, writes, and dynamic-environment restoration. Control proofs cover catch, finally, combined catch/finally, switch and labeled breaks, loop control, and fuel-bounded while loops. Call normalization validates normal, returned, and thrown values and proves checked call preservation under `BodyHookPreservesWellFormed`.

The hook premise is not justified only by an inert fixture. `BodyHookPreservesWellFormed_realistic` inspects callable metadata, allocates a child activation, declares and initializes `this` and `argument0`, executes under that environment, allocates a closure capturing it, and restores the caller environment. `BodyHookPreservesWellFormed_composed` separately composes environment allocation/restoration, checked call, catch/finally, and trace emission. Normal and throwing hooks instantiate the access, iterator, and copy theorems, while `continuityBreakingProofHook_rejected` demonstrates that a well-formed but identity-breaking result does not satisfy the strengthened contract.

The heap proofs cover machine-reference continuity for public definition, creation, allocation, and iterator mutation. Array-iterator allocation and advancement preserve heap and machine validity; stepping composes the iterator-slot update with ordinary `Get`, preserving getter effects and validating yielded, done, and abrupt values. Object access proves `Get`, `Set`, strict `Set`, and `CreateDataProperty` preservation across data, getter/setter, rejection, throw, fault, and exhaustion branches. Copy proofs cover `copyDataProperties`, `Object.assign`, object spread, array slice, and iterator-based array spread, including source boxing, getter/setter calls, abrupt completion, and left-to-right composition.

The fresh-result theorems are relational rather than only executable checks. `Heap.allocate_result_fresh_kind`, `Heap.allocateArray_result_fresh_kind`, and `Heap.allocateArrayIterator_result_fresh_kind` identify the old heap frontier and exact resulting kind. `Iterator.arrayValues_normal_result`, `Copy.objectSpread_normal_result`, `ArrayCopy.slice_normal_result`, and `ArrayCopy.spread_normal_result` prove final validity and continuity, freshness against every old valid reference, exact ordinary/array/iterator kind, and result-reference validity. Concrete normal runs witness each relation.

Review approved removing exactly `copy-hook-conditional-preservation`, `iterator-hook-conditional-preservation`, and `machine-hook-conditional-preservation`. The canonical formal debt is now exactly one obligation, `abstract-effectful-coercion-refinement`. The four executable Float assumptions and all differential measurements are carried forward unchanged as runtime evidence, not proof axioms.

This debt reduction is a model-preservation result, not a compiler-support claim. Canonical `GetIterator`, custom iterables, allocated iterator-result objects, and `IteratorClose` remain an open semantic feature gap. Promises and derived `super` remain unsupported compiler/runtime features. None of those gaps is counted as discharged by the three removed preservation obligations.

The measured suite remains 43 files, 1,633 passing tests, 8 todos, 172 Lean jobs, and 102 red corpus entries. Differential evidence remains 16 scenario groups, 734 fixed plus 6,530 generated comparisons for 7,264 total, 6,088 unique operation inputs, 1,176 preserved duplicates, 97 legacy inventory IDs, the unchanged 102-entry coverage partition, and a 65,536-cell aggregate fixture budget. The manifest records source `sha256:fa74184c0093d5e56ae5c02c7f1496bc13038d4f3ce800033d8be7966d5aa5f3`, JS runtime `sha256:658b80535a5c119c0b28cc4fdfe8e9c4e98ed881078586fc4659d8226ca06535`, corpus `sha256:467348cdf61bd4925e41c764cab7fa289d74b2bcd1e54cba87b225f543cf09ec`, differential specifications and harness `sha256:6386c60110ee9bfae81fcb9fd013faf6112254af96502accd7203221a240993e`, proof tests and audit `sha256:abf9a5876478d1d597353267b09cd914012f594122a80a909622b7b2db40303c`, and trust/evidence infrastructure `sha256:493b73144dda00c1b4f76eaf986687dbecab188b8ecaa7964189055e9e51ca7e`. The manifest SHA-256 is `0aef5649d09cddef7d532a00458e3eae896523eb140efd5034910438efc75878`.

Commands and results:

```text
$ bun run evidence:baseline:check
$ bun run evidence:primitives:check
$ bun run evidence:heap:check
$ bun run evidence:execution:check
$ bun run evidence:callable:check
$ bun run evidence:arrays:check
$ bun run evidence:primitive-ops:check
$ bun run evidence:abstract-ops:check
$ bun run evidence:differential:check
$ bun run evidence:differential-compact:check
$ bun run evidence:ordered-props:check
$ bun run evidence:heap-allocation:check
$ bun run evidence:array-shrink:check
$ bun run evidence:heap-mutation:check
$ bun run evidence:prototype:check
$ bun run evidence:hook-copy:check

$ bun scripts/check-js-axioms.mjs --self-test
synthetic environment audit passed

$ /usr/bin/time -p bun run verify
All matched files use Prettier code style!
Differential manifest is current: 7264 vectors
Legacy abstract inventory is current: 97 entries
JS trust checks passed: 439 elaborated proof declarations
JS trust gate passed: 439 proof declarations
Test Files  43 passed (43)
Tests  1633 passed | 8 todo (1641)
Build completed successfully (172 jobs).
real 81.09
user 113.83
sys 7.66

$ bun pm pack --dry-run --ignore-scripts
Total files: 304
Unpacked size: 3.56MB

$ shasum -a 256 evidence/phase2-prototype-manifest.json evidence/phase2-hook-copy-manifest.json
aecb383818b16b75343b5fbeccce345e7216b5240a5ce1d32008b597e3c62722  evidence/phase2-prototype-manifest.json
0aef5649d09cddef7d532a00458e3eae896523eb140efd5034910438efc75878  evidence/phase2-hook-copy-manifest.json

$ git diff --check
```

The 439 audited declarations and complete verification gate support only the preservation, continuity, result-validity, and freshness statements above. They do not establish the remaining effectful-coercion refinement, close the iterator semantic feature gap, or add promises or derived `super` support. Existing warnings and `sorry` declarations outside the isolated `TSLean.JS` trust boundary remain visible and were not suppressed or changed.

## 2026-08-08 - Phase 2 zero formal debt

This snapshot is based on `d68dab44af677733dd23b15c0ca16937ebc3d2ae` on `rebuild/semantic-core`. The hook/copy input now resolves every source-derived validation and hash from that immutable revision. Its manifest remains available through `evidence:hook-copy:generate` and `evidence:hook-copy:check`; all earlier inputs, manifests, ledger entries, and explicit historical commands remain intact. Current `evidence:generate`, `evidence:check`, `js:trust`, and `verify` target `phase2-zero-debt-input.json`.

Review closes the 11 obligations recorded at the start of Phase 2:

- The four OrderedProps obligations are closed by general insertion, deletion, compaction, exact key-correspondence, partition, order, and duplicate-freedom theorems.
- Heap allocation coverage includes ordinary objects, primitive wrappers, arrays, array-from-array allocation, functions, constructor/prototype pairs, and array iterators, with freshness, validity, and continuity results where applicable.
- `heap-public-mutation-preservation` is closed by general `defineOwnProperty`, `createDataProperty`, `deleteProperty`, and `preventExtensions` preservation, including successful, rejected, and state-committing branches.
- `heap-prototype-preservation` is closed by logical/executable acyclicity correspondence, finite prototype-path termination, and complete `setPrototypeOf` preservation.
- `array-blocked-shrink-general` is closed by separate blocked and unblocked strict-shrink theorems that characterize deletion, blocker, length, writability, ordering, unchanged-object, and final-validity behavior.
- The three copy, iterator, and machine hook-conditional obligations are closed by the strengthened continuity and escaping-result validity contract, preservation for access/call/control/environment operations, iterator allocation and advancement, and copy/assign/spread/slice composition under preserving hooks.
- `abstract-effectful-coercion-refinement` is closed by the free `CoercionProgram` specification. Its typed operations retain complete parameters; `Executes` gives exact total big-step execution with soundness, completeness, determinism, trace-prefix/first-event equations, response consumption, and allocation accounting. Interpretation theorems connect the free programs to every production coercion, equality, relational, and `instanceof` entry point. Program-order theorems establish property-get before call, ordinary hint order, left-before-right addition, both relational orders, and custom `@@hasInstance` before ordinary fallback. Production specialization is definitional through `CoercionEffects.forJSM`, and preservation theorems carry the existing machine continuity and result-validity contract through interpreted production execution.

The trust audit reviewed 591 elaborated declarations and accepted only `propext`, `Classical.choice`, and `Quot.sound`. `CoercionProgram` is proof support rather than a second production runtime: production entry points remain the `JSM` specializations, and the production interpretation theorems connect those exact definitions to the free specification. The four Float assumptions remain unchanged executable TCB assumptions rather than proof axioms. The 7,264-comparison differential suite remains unchanged and continues to cover the same 16 groups, 734 fixed vectors, 6,530 generated vectors, 6,088 unique operation inputs, and 1,176 preserved duplicates.

Zero formal debt means that no obligation remains in the scoped Phase 2 ledger. It is not a claim of complete ECMAScript modeling or compiler correctness. Canonical iterable spread (`GetIterator`, custom iterables, allocated iterator-result objects, and `IteratorClose`), promises, and derived `super` remain semantic/model gaps. The corpus still classifies 26 entries as model-pending, and all eight compiler todos remain explicit. The 102 corpus entries remain red evidence, not passing conformance tests. Existing warnings and `sorry` declarations outside the isolated `TSLean.JS` trust boundary remain visible and are not discharged by this snapshot.

Measured commands and results:

```text
$ bun run test
Test Files  43 passed (43)
Tests  1633 passed | 8 todo (1641)

$ bun run lint
$ bun run build

$ bun run differential:check
Differential manifest is current: 7264 vectors
Legacy abstract inventory is current: 97 entries

$ cd lean && lake build
Build completed successfully (174 jobs).

$ bun run benchmark:coercion-effects
coercion-specialization public100kMs=7 public1mMs=62 generic100kMs=7 generic1mMs=64

$ bun pm pack --dry-run --ignore-scripts
Total files: 307
Unpacked size: 3.70MB
```

The optional benchmark is a machine-local smoke measurement, not a performance guarantee. The zero-debt manifest records source `sha256:fa74184c0093d5e56ae5c02c7f1496bc13038d4f3ce800033d8be7966d5aa5f3`, JS runtime `sha256:0b40e99e3e07eb37f91190aa6d27d013c4e7d497d87c61bc1d5546f8fa0b0df1`, corpus `sha256:467348cdf61bd4925e41c764cab7fa289d74b2bcd1e54cba87b225f543cf09ec`, differential specifications and harness `sha256:6386c60110ee9bfae81fcb9fd013faf6112254af96502accd7203221a240993e`, proof tests and audit `sha256:f29e2d6f841359a7361d1596d5dc8f94799b76736bd69472880d13415e09dcfe`, and trust/evidence infrastructure `sha256:6c992b11d0d2cbbee42a997ac9fdb997f772990aa8d6438f3fe2abe2f1bbaac4`. The frozen hook/copy manifest SHA-256 is `47f4d9473c30c2b2f2f4a8b685de99cc8d49048f1e4bf09ae1c87a8ad57f303f`; the zero-debt manifest SHA-256 is `b6d417de5073ffe328dec868ac48345bd73089a007be71a38050e54359780f67`.

## 2026-08-08 - Refinement core

This snapshot is based on `6c1a0861651059f44ebfa99ef2cb8e082d419bbc` on `rebuild/semantic-core`. The zero-debt input now resolves its validations and every hash group from that immutable revision, while its manifest remains byte-for-byte unchanged at SHA-256 `b6d417de5073ffe328dec868ac48345bd73089a007be71a38050e54359780f67`. Its explicit generate/check commands and all earlier inputs, manifests, ledger entries, and historical commands remain intact. Current `evidence:generate`, `evidence:check`, `js:trust`, and `verify` target `phase3-refinement-core-input.json`.

The exact public core APIs are `Refinement` with `Rel`, `valueValid`, and exact-extension `stable`; `Refinement.UniqueDecode`; `Codec` with typed `encode` and `decode` faults plus `encode_sound` and `decode_sound`; and `LawfulCodec` with `encode_total` and `complete`. `LawfulCodec.roundtrip` follows from those laws. `LawfulCodec.not_of_encode_always_errors` rules out a vacuous codec that obtains soundness only by rejecting every native value. No concrete Float, String, Bool, Array, or closed-record codec is claimed by this snapshot.

The evidence authority model exposes `Evidence.proved`, `Evidence.ofGuard`, and `Evidence.assumed`. Proved and guarded evidence contain a proof; assumed evidence deliberately returns `ProofStatus.none`. `Assumption.create` derives stable IDs and rejects empty metadata. `ValidAssumptions.create` requires a nonempty, valid set with unique IDs. `Guard.create` binds an executable check to its soundness theorem, and `GuardReceipt` is indexed by the guard and checked value. `Evidence.kind`, `metadata`, `proof?`, `and`, and `map` preserve the distinction between authority and canonical proof-free provenance. Assumption, guard, receipt, metadata, and evidence constructors are private, so callers cannot fabricate authority or invalid metadata.

`Heap.ExactExtension` requires both heaps to be well formed, monotone size, and exact preservation of every old object record. It is reflexive and transitive, implies the existing JS heap continuity relation, preserves old value validity, and frames old own-property reads, own-key enumeration, object kind, and prototype. Exact-extension theorems cover all append-only allocator families: ordinary objects, primitive wrappers, list- and array-input arrays, functions, constructor/prototype pairs, and array iterators.

The refinement trust review recursively scans the refinement tree without following symlinks, rejects forbidden declaration tokens, legacy runtime imports, non-semantic imports into semantic modules, and namespace-prefix bypasses, then audits the elaborated environment against only `propext`, `Classical.choice`, and `Quot.sound`. It found 61 refinement proof declarations. The separately maintained production registry requires 48 exact declaration names and has source digest `sha256:11f1002061e9fdcda0aa87ab475dad53400ead9992642a9338fa14635349a2b7`. Current evidence pins the audited count, required count, and digest; the trust gate validates all three. Inputs that predate this optional `refinementProofs` field remain valid and frozen.

This is a refinement foundation, not compiler consumption. `TSLean.Refinement.Execution` remains an explicitly empty reservation until both sides and their observation boundary exist. The compiler, IR, lowering, representation selection, and generated output do not consume these APIs yet. Canonical iterables and `IteratorClose`, promises, derived `super`, the 26 model-pending corpus entries, and all eight compiler todos remain semantic gaps. The four Float executable assumptions are carried forward unchanged. There is no `formalDebt` field in this snapshot.

Measured commands and results:

```text
$ bun run evidence:generate
$ bun run evidence:check

$ bun run evidence:check
Cannot generate evidence manifest: evidence/phase3-refinement-core-manifest.json is stale at line 129
-     "source": "sha256:0a74184c0093d5e56ae5c02c7f1496bc13038d4f3ce800033d8be7966d5aa5f3",
+     "source": "sha256:fa74184c0093d5e56ae5c02c7f1496bc13038d4f3ce800033d8be7966d5aa5f3",

$ bun run js:trust
JS trust checks passed: 591 elaborated proof declarations
JS trust gate passed: 591 proof declarations
Refinement trust gate passed: 61 audited proof declarations; 48 required production theorems

$ bun run test
Test Files  43 passed (43)
Tests  1636 passed | 8 todo (1644)

$ bun run verify
All matched files use Prettier code style!
Differential manifest is current: 7264 vectors
Legacy abstract inventory is current: 97 entries
JS trust checks passed: 591 elaborated proof declarations
JS trust gate passed: 591 proof declarations
Refinement trust gate passed: 61 audited proof declarations; 48 required production theorems
Test Files  43 passed (43)
Tests  1636 passed | 8 todo (1644)
Build completed successfully (181 jobs).

$ bun pm pack --dry-run --ignore-scripts
Total files: 315
Unpacked size: 3.76MB

$ git diff --check
```

Every historical evidence check from `evidence:baseline:check` through `evidence:zero-debt:check` and the current `evidence:refinement-core:check` passed. A separately tampered registry digest was rejected with the measured digest above before restoration. The refinement-core manifest records source `sha256:fa74184c0093d5e56ae5c02c7f1496bc13038d4f3ce800033d8be7966d5aa5f3`, JS runtime `sha256:0b40e99e3e07eb37f91190aa6d27d013c4e7d497d87c61bc1d5546f8fa0b0df1`, refinement runtime and barrel `sha256:645fafc4af75e614d0bb8692ec85ef0b7a629ca7f1c16c75c81c101f2f533f10`, refinement tests, audit, and registry `sha256:6b99c7438e1f6664470b52838ab09a6ee618150f9ef0ed07d6e667308a3c2c59`, corpus `sha256:467348cdf61bd4925e41c764cab7fa289d74b2bcd1e54cba87b225f543cf09ec`, differential specifications and harness `sha256:6386c60110ee9bfae81fcb9fd013faf6112254af96502accd7203221a240993e`, and trust/evidence infrastructure `sha256:1297fba5bfffc9ea635948fb9dd149a219de66aa7325eb7f768878b3026d3bdb`. The manifest SHA-256 is `c3e2016e2383e28d0dfa9b94d1602f5b66792ad46638839b1ea211f28446ce9b`.

## 2026-08-08 - Primitive refinements

This snapshot is based on `e0665cdb7f2fae5e9092ba3dacb96ae26edf2227` on `rebuild/semantic-core`. The refinement-core input now resolves its validations and every hash group from that immutable revision, while its manifest remains byte-for-byte unchanged at SHA-256 `c3e2016e2383e28d0dfa9b94d1602f5b66792ad46638839b1ea211f28446ce9b`. Its explicit generate/check commands and all earlier inputs, manifests, ledger entries, and historical commands remain intact. Current `evidence:generate`, `evidence:check`, `js:trust`, and `verify` target `phase3-primitive-refinements-input.json`.

`TSLean.Refinement.Bool` exposes the typed `DecodeFault.expectedBoolean`, exact heap-independent `refinement`, heap-neutral `encode`, domain-checking `decode`, and `codec`. Its proved laws establish exact relation and unique decoding, exact encode/decode behavior, rejection of non-Boolean primitives and objects, `LawfulCodec`, exact heap-neutral roundtrip, and commutation for truthiness, strict equality, SameValue, SameValueZero, loose equality, logical negation, and conditional selection.

`TSLean.Refinement.BigInt` exposes the typed `DecodeFault.expectedBigInt`, exact heap-independent `refinement`, heap-neutral `encode`, domain-checking `decode`, and `codec`. Its proved laws establish exact relation and unique decoding, exact encode/decode behavior, rejection of non-BigInt primitives and objects, `LawfulCodec`, exact heap-neutral roundtrip, and commutation for truthiness, strict equality, SameValue, SameValueZero, loose equality, decimal string conversion, addition, subtraction, multiplication, all four relational operators, truncating division and remainder, and both zero-divisor faults. `TSLean.Refinement.Primitive.jsm_pure_neutral` proves that lifting a pure result leaves the complete machine unchanged.

The refinement trust review found 102 elaborated proof declarations and required 89 exact production theorem names. The registry source digest is `sha256:5741008959cf36417907c55f7777d7ab9c1c59265e6a90d1367c57efa67b94ed`; the current trust gate validates the audited count, required count, and digest. The Bool and BigInt evidence is theorem-backed: it introduces no `Evidence.assumed` authority and no primitive-specific executable assumption. The four existing Float executable assumptions remain global and unchanged. There is no `formalDebt` field.

This snapshot adds proof-carrying primitive refinements, not compiler consumption. The compiler, IR, lowering, representation selection, and generated output do not import or use the Bool or BigInt codecs or commutation laws. No compiler source was changed. Float, String, Array, and closed-record codecs remain unclaimed, and `TSLean.Refinement.Execution` remains reserved. The existing model gaps, 26 model-pending corpus entries, and eight compiler todos remain unchanged.

Measured commands and results:

```text
$ bun run evidence:generate
$ bun run evidence:check
$ bun run evidence:refinement-core:check

$ bun run js:trust
JS trust checks passed: 591 elaborated proof declarations
JS trust gate passed: 591 proof declarations
Refinement trust gate passed: 102 audited proof declarations; 89 required production theorems

$ bun run test
Test Files  43 passed (43)
Tests  1636 passed | 8 todo (1644)

$ bun run verify
All matched files use Prettier code style!
Differential manifest is current: 7264 vectors
Legacy abstract inventory is current: 97 entries
JS trust checks passed: 591 elaborated proof declarations
JS trust gate passed: 591 proof declarations
Refinement trust gate passed: 102 audited proof declarations; 89 required production theorems
Test Files  43 passed (43)
Tests  1636 passed | 8 todo (1644)
Build completed successfully (183 jobs).

$ bun pm pack --dry-run --ignore-scripts
Total files: 317
Unpacked size: 3.78MB

$ git diff --check
```

Every evidence check from `evidence:baseline:check` through `evidence:refinement-core:check` and the current `evidence:primitive-refinements:check` passed. The primitive-refinements manifest records source `sha256:fa74184c0093d5e56ae5c02c7f1496bc13038d4f3ce800033d8be7966d5aa5f3`, JS runtime `sha256:0b40e99e3e07eb37f91190aa6d27d013c4e7d497d87c61bc1d5546f8fa0b0df1`, refinement runtime and barrel `sha256:60b4916485c382924729d93865cc8a72c1539216224236dc563f5c3a723da030`, refinement tests, audit, and registry `sha256:733a74e422c5726fe43c381f792eea6d0a2a9b13d4acdf7aaee7f8e04b5973c6`, corpus `sha256:467348cdf61bd4925e41c764cab7fa289d74b2bcd1e54cba87b225f543cf09ec`, differential specifications and harness `sha256:6386c60110ee9bfae81fcb9fd013faf6112254af96502accd7203221a240993e`, and trust/evidence infrastructure `sha256:9650b8b60a6301b5c5469f26bffc6a46fd72dbce4585f66cc6e579465c1661c3`. The manifest SHA-256 is `205267d456c3f9a827b4bbaee08fc01108ff77b0565d69da1fb648bfc50ee91c`.

## 2026-08-08 - String refinement

This snapshot is based on `50fedc36a2aed89cd59973ac97c0411eeae3fae5` on `rebuild/semantic-core`. The primitive-refinements input now resolves every validation and hash group from that immutable revision; its manifest remains byte-for-byte unchanged at SHA-256 `205267d456c3f9a827b4bbaee08fc01108ff77b0565d69da1fb648bfc50ee91c`. Its explicit commands and every earlier input, manifest, and ledger entry remain intact. Current `evidence:generate`, `evidence:check`, `js:trust`, and `verify` target `phase3-string-refinement-input.json`.

The String codec encodes Lean Unicode scalar strings as exact ECMAScript UTF-16 primitives without changing the heap. Decoding accepts only string primitives whose code units decode without unpaired surrogates and reports typed non-string and invalid-UTF-16 faults. The proved contracts cover scalar/UTF-16 roundtrips and injectivity, exact codec roundtrip, append and string addition, equality variants, truthiness, and primitive `ToString`.

The `validUTF16Guard` accepts exactly when the strict UTF-16 decoder returns a Lean scalar string; its evidence proves that some native string exactly refines the accepted code units, and append preserves acceptance. The separate `bmpStringGuard` accepts Lean strings only when every scalar is at most `0xffff`. Code-unit length equals Lean character length, and code-unit indexing matches Lean character indexing, only under that BMP premise. Astral scalars remain supported by the codec but encode as surrogate pairs, so those length and indexing claims do not apply globally.

Review found 596 elaborated JS proof declarations and 133 refinement proof declarations, with 119 exact production theorem names required by registry SHA-256 `7ae597b51426aa98c4a3e04d159e41eea312f80ae34abf2bb15f397e39afa4f2`. The String, Bool, and BigInt refinements introduce no `Evidence.assumed` authority and no primitive-specific executable assumptions. The four existing Float executable assumptions remain global and unchanged. There is no `formalDebt` field.

Review approval is scoped to the String refinement, its strict UTF-16 and BMP guards, the supporting JSString roundtrip theorems, tests, audit coverage, and registry entries. It does not claim compiler consumption or global Lean-string/code-unit length equivalence. The compiler, IR, lowering, representation selection, and generated output remain unchanged and do not consume the codec. Array and closed-record codecs remain unclaimed, `TSLean.Refinement.Execution` remains reserved, and the 26 model-pending corpus entries and eight compiler todos remain unchanged.

Measured commands and results:

```text
$ bun run evidence:string-refinement:generate
$ bun run evidence:string-refinement:check
$ bun run evidence:primitive-refinements:check

$ bun run js:trust
JS trust checks passed: 596 elaborated proof declarations
JS trust gate passed: 596 proof declarations
Refinement trust gate passed: 133 audited proof declarations; 119 required production theorems

$ bun run verify
All matched files use Prettier code style!
Differential manifest is current: 7264 vectors
Legacy abstract inventory is current: 97 entries
JS trust checks passed: 596 elaborated proof declarations
JS trust gate passed: 596 proof declarations
Refinement trust gate passed: 133 audited proof declarations; 119 required production theorems
Test Files  43 passed (43)
Tests  1636 passed | 8 todo (1644)
Build completed successfully (185 jobs).

$ bun pm pack --dry-run --ignore-scripts
Total files: 319
Unpacked size: 3.82MB

$ git diff --check
```

Every evidence check from `evidence:baseline:check` through the current `evidence:string-refinement:check` passed. The String-refinement manifest records source `sha256:fa74184c0093d5e56ae5c02c7f1496bc13038d4f3ce800033d8be7966d5aa5f3`, JS runtime `sha256:a1ee6f4de87c9035d609bf3e3d088e63c40beb61ddcee6015d1243fd2b382ffa`, refinement runtime and barrel `sha256:fa4bf03fdc83bc21a3cab433ffc167eb2652c3feaa908f16f466431545fd8412`, refinement tests, audit, and registry `sha256:a2016a8885d00f2a7cce5543c3767b6606f99a0bfeed68eb1c6221cbe79e83f9`, corpus `sha256:467348cdf61bd4925e41c764cab7fa289d74b2bcd1e54cba87b225f543cf09ec`, differential specifications and harness `sha256:6386c60110ee9bfae81fcb9fd013faf6112254af96502accd7203221a240993e`, and trust/evidence infrastructure `sha256:4563325e3f87e4b72c408f911f3f15c1c108a2c35dd4cf38a463a51b5615b7b1`. The manifest SHA-256 is `1e2cba1a786115e9ada050b18f0d448ef76ec76012dd220c645ac89c16cce6c0`.

## 2026-08-08 - Float refinement

This snapshot is based on `c6a87f3b5ee18040056a39225cf25ae5a2b3abce` on `rebuild/semantic-core`. The String-refinement input now resolves every validation and hash group from that immutable revision, while its manifest remains byte-for-byte unchanged at SHA-256 `1e2cba1a786115e9ada050b18f0d448ef76ec76012dd220c645ac89c16cce6c0`. Its explicit commands and every earlier input, manifest, and ledger entry remain intact. Current `evidence:generate`, `evidence:check`, `js:trust`, and `verify` target `phase3-float-refinement-input.json`.

The Float codec is observational. It encodes to a canonical Number primitive, decodes Number primitives through `Float.ofBits`, rejects every other primitive and object with a typed fault, and relates native and modeled values by `JSNumber.sameValue`. `codec_observational_roundtrip` preserves that shared observation across encode and decode; it does not provide `LawfulCodec`, `CodecComplete`, or native Float equality after roundtrip. Remainder uses the committed integer-based `JSNumber.remainder` path and the bridge roundtrip contract, so it adds no executable assumption.

The executable ledger records exactly eight assumed runtime contracts in `Float.runtimeAssumptionRegistry`: canonical bridge roundtrip, addition, subtraction, multiplication, division, strict less-than, non-strict less-than-or-equal, and strict equality. Their deterministic IDs and statements are copied exactly into the manifest. Each `Evidence.assumed` value has no proof payload. The manifest has no `formalDebt` field.

The boundary matrix uses 15 binary64 values: positive and negative zero, positive and negative one, minimum subnormal, maximum subnormal, minimum normal, positive and negative maximum finite, both infinities, and positive and negative signaling and quiet NaN encodings. The seven binary runtime contracts and the derived remainder path execute over all 225 ordered pairs; the bridge contract is checked for every matrix value and operation result. Separate tests cover exact finite/infinite bit roundtrips, NaN canonicalization, typed decode failures, truthiness, SameValue, and SameValueZero. Source review confirmed the theorem premises expose each executable contract rather than proving it, the audited registry contains the intended production statements, and no remainder or codec-completeness assumption was introduced.

This snapshot adds a Float-to-Number refinement boundary, not compiler consumption. No compiler, parser, IR, lowering, representation-selection, or code-generation source changed, and generated output does not use this codec. Array and closed-record codecs remain unclaimed, `TSLean.Refinement.Execution` remains reserved, and the existing model gaps, 26 model-pending corpus entries, and eight compiler todos remain unchanged.

Measured commands and results:

```text
$ bun run evidence:float-refinement:generate
$ bun run evidence:float-refinement:check
$ bun run evidence:string-refinement:check

$ bun run js:trust
JS trust checks passed: 596 elaborated proof declarations
JS trust gate passed: 596 proof declarations
Refinement trust gate passed: 155 audited proof declarations; 140 required production theorems

$ bun run verify
All matched files use Prettier code style!
Differential manifest is current: 7264 vectors
Legacy abstract inventory is current: 97 entries
JS trust checks passed: 596 elaborated proof declarations
JS trust gate passed: 596 proof declarations
Refinement trust gate passed: 155 audited proof declarations; 140 required production theorems
Test Files  43 passed (43)
Tests  1636 passed | 8 todo (1644)
Build completed successfully (187 jobs).

$ bun pm pack --dry-run --ignore-scripts
Total files: 321
Unpacked size: 3.85MB

$ git diff --check
```

Every evidence check from `evidence:baseline:check` through the current `evidence:float-refinement:check` passed. The Float-refinement manifest records source `sha256:fa74184c0093d5e56ae5c02c7f1496bc13038d4f3ce800033d8be7966d5aa5f3`, JS runtime `sha256:4fe149ff5f709495e20acca7deb27edfd0aca01c9d1f26b1dcd07cb9d8eb4969`, refinement runtime and barrel `sha256:fef2f61ad99859a0c0eefc4d8773f2266233c70b90cb2f55297dd547b6d839f7`, refinement tests, audit, and registry `sha256:b6e19c994a851d9f904522537bff041fc20f13cd148a3705a9e5187288511617`, corpus `sha256:467348cdf61bd4925e41c764cab7fa289d74b2bcd1e54cba87b225f543cf09ec`, differential specifications and harness `sha256:6386c60110ee9bfae81fcb9fd013faf6112254af96502accd7203221a240993e`, and trust/evidence infrastructure `sha256:ea3629588eeb78366df81c900a4ac0548ca9c54eb532b2fd3133e74e88dc8d1e`. The registry SHA-256 is `6fbe4d0b6f71b418d3b840b41bb092c3562eadb93792616d1ccf2ec0fb32d2cb`. The manifest SHA-256 is `dc61688e170faba957c4993bd78a05b21556137278c092ad2e35d3b5eb23e633`.

## Differential oracle timeout flake

The differential harness gate was non-deterministic. `tests/js-model-differential.test.ts` spawns a
real Node child through `fakeOracle`, and seven cases bounded the request at `1_000` ms (one at
`50` ms) while asserting a _non-timeout_ outcome: unexpected stdout close, unexpected exit, invalid
JSON followed by a fresh restart, unsolicited output, failed response correlation, a bounded close,
and truncated stderr. Because the suite runs serialized (`fileParallelism: false`) and this file
alone takes roughly 16 s, spawning the child can exceed one second under load. The request timeout
then won the race and the harness reported `oracle batch timed out after 1000ms` instead of the
lifecycle failure each case asserts. The tip passed in one run and failed two cases in the next, so
the gate could not be trusted either way.

The fix names the bound. `nonTimeoutRequestMs = 10_000` is used wherever the assertion is a
non-timeout outcome, comfortably above real spawn latency and well inside the 30 s `testTimeout`.
The deliberately short bounds are unchanged, because there the timeout _is_ the subject: `20` ms for
the hanging-child request and `20` ms for `closeTimeoutMs`. No harness semantics, vector, or
observation changed; the manifest still records 7264 comparisons.

This snapshot exists because `tests/js-model-differential.test.ts` belongs to the
`differentialSpecHarness` hash group, so the Float manifest became stale the moment the flake was
fixed. The Float snapshot is frozen at its own revision `9ae9975` and its manifest remains
`dc61688e170faba957c4993bd78a05b21556137278c092ad2e35d3b5eb23e633`, byte for byte. Counts are
unchanged at 43 test files, 1636 passed, 8 todo, 187 Lean jobs, 596 audited JS proofs, 155 audited
and 140 required refinement proofs, and 102 red corpus entries. Only the harness hash moves, from
`sha256:6386c60110ee9bfae81fcb9fd013faf6112254af96502accd7203221a240993e` to
`sha256:48e7e54c874b90058b563b84d5fe88f724f5f77a4f08d24ad1d4cfa069053e99`.

A stale-artifact hazard surfaced while verifying this. `lake env lean` reuses whatever `.olean`
files exist rather than rebuilding, so an orphaned artifact from a removed module can still be
imported through a stale barrel and inflate the audit. Running `lake build` before the trust gate
restores agreement between source and environment; `bun run verify` already does this, but the
audit does not enforce it on its own.

## Lean artifact freshness in the trust gate

The trust gate audited an environment whose currency it never checked. `runLeanAudit` invokes
`lake env lean`, which loads whatever `.olean` files already exist rather than rebuilding. That is
not theoretical: an orphaned `lean/.lake/build/lib/lean/TSLean/Refinement/Array.olean`, left behind
by a module whose source had been removed, stayed reachable through a stale barrel artifact and the
gate reported 167 refinement proof declarations where source contained 155. `lake build` reconciled
them. `bun run verify` masked the hazard by rebuilding first, so `bun run js:trust` alone was the
unsound entry point.

The gate now fails closed on its own. It runs `lake build` before any audit and surfaces both
stdout and stderr on failure, because Lean reports diagnostics on stdout and only `error: build
failed` on stderr. It then rejects orphaned artifacts: any compiled module under
`lean/.lake/build/lib/lean/TSLean/**` with no corresponding source. That check is load-bearing
rather than redundant, since `lake build` does not garbage-collect removed modules; it immediately
found three genuine orphans from modules deleted in `4e0953f`
(`JS/AbstractOperationsOracleTests`, `JS/CoercionEffectsRefinement`, `JS/PrimitiveOracleTests`).
Finally it asks Lean for the modules actually loaded in the audited environment and rejects any
without a source file.

Requirement wording asked for namespace-level correspondence in both directions. Neither direction
is implementable as stated and both were narrowed deliberately. Namespaces are not modules here:
`TSLean.Refinement.BigInt`, `.Bool`, `.EvidenceKind`, `.Heap.ExactExtension`, `.LawfulCodec`,
`.Codec` and `.Guard` legitimately have no source file, so the assertion is made at module
granularity, which subsumes declarations. The reverse direction would be a pure false positive:
`TSLean.JS.Function`, `TSLean.JS.Construct` and `TSLean.JS.CoercionEffectsBenchmark` are semantic by
`moduleRole` yet sit outside the audit's import closure, and each declares zero theorems.

Two regressions pin the behaviour: a fabricated orphan artifact must fail the gate with its path and
stop failing once removed, and a failing or absent `lake` must fail the gate through an injected
seam that only an in-process caller can reach. Test count moves from 1636 to 1638. Gate cost moves
from 30.1 s to 30.6 s, with an up-to-date `lake build` measured at 0.1-2 s and no caching added.

Residual, both accepted and recorded rather than fixed. `lake build` builds the default target's
closure, so a refinement module outside it would not be rebuilt; none exists today and a missing
artifact fails loudly rather than silently. The loaded-module probe cannot fire while the orphan
check holds and `LEAN_PATH` has a single TSLean root; it uniquely covers modules resolved from
outside the TSLean artifact tree and costs about 1.4 s.

## Dense array snapshot refinement

This slice was rejected twice before it landed, and the first rejection is the useful one. The
initial implementation compiled and registered ten theorems, but the trust gate had never been run
on it: `requiredDeclarations` was unsorted, because `TSLean.Refinement.Array.` sorts before
`TSLean.Refinement.Assumption.`, and the gate rejects an unsorted registry at index 0. Behind that,
seven of its ten registered theorems could be replaced by `True` with CI still green, its one
identity theorem `aliases_strictEqual` was provable with no hypotheses for a root in no heap, and
its declared `Codec` did not exist. A registry checks names; only a contract inventory checks
meaning, and the namespaces that had one caught this class of defect while the one that did not,
did not.

Two design faults sat underneath. `DenseArrayRel` carried `heap.WellFormed` inside `Rel`, unlike
every other refinement, and `Codec.decode_sound` has no well-formedness premise, so the codec was
not merely missing but unprovable as written. And `inspectDense` compared observed keys against
`denseKeys slots.length`, which materializes one `JSString` per declared index before comparing, so
a sparse array with two own keys and a declared length of 4294967295 -- reachable through public
`defineArrayLength` -- cost roughly 1.5 hours and 4.29e9 list nodes to reject. A boundary validator
that hangs on the invalid input it exists to reject is the wrong shape.

The rework removes `WellFormed` from `Rel` and carries it as an explicit hypothesis where it is
genuinely needed, and streams key comparison so work is bounded by the actual own-key count. Sparse
rejection at 2^32-1 now measures 9.9 microseconds and is flat in the declared length; dense
validation, encode and decode are linear across 50k and 100k elements at roughly 2.1x per doubling.
Identity and mutation were deleted from the slice rather than shipped unproved: `Tracked`, `set`,
`push` and `pop` are deferred to their own reviewed slice, because unproved public mutation API
behind a green proof gate is worse than shipping less.

Two claims in the original specification were false and were proved false rather than satisfied.
`LawfulCodec` cannot hold for arrays: `encode_total` quantifies over every `Array α`, Lean arrays
are unbounded, and ECMAScript caps length at 2^32-1, so the slice proves conditional totality plus
`not_lawful : ¬LawfulCodec (codec elementCodec)` as evidence that the bound is not decoration. And
guard soundness in the form `check = true → ∃ native, Rel` is false for a shape-only check, since a
one-element array holding `undefined` is shape-valid with no `Array Bool` witness; the existential
belongs in `decode_sound`, where the decoder supplies the witness rather than the caller.

A subtler vacuity survived into the third round. Six theorems required `LawfulCodec elementCodec`,
which this slice itself refutes for a nested array codec, so every completeness and totality claim
was vacuously true for `Array (Array α)` while still compiling. Four of them consume only the
completeness half, so `Codec.Complete` was factored out in `Core.lean` -- with `LawfulCodec.complete`
now spelled as that same type so the two cannot drift -- and those four are stated over it. Nested
completeness is now a real theorem, `nested_array_contract`, discharged by `codec_complete` and
proved beside `¬LawfulCodec (codec Bool.codec)`. `encode_total` and `codec_roundtrip` keep the
stronger hypothesis and say plainly in their doc-comments that they do not compose without a
per-element bound.

The kernel gained two public theorems, `allocateArrayFromArray_dense` and
`allocateArrayFromArray_ok`, because nothing characterized a freshly allocated array beyond
`objectKind?` and the private `ObjectRecord`/`Heap` constructors correctly prevent the refinement
layer from looking inside. `get?_ok_valid` lost `private` for the same reason, which removed the
representation access the previous review flagged. Across all tracked files this round removes
exactly two lines -- that `private` keyword and one doc-comment line -- and the JS audit moving
596 to 599 independently confirms no other kernel surface changed.

`array_contract_inventory` pins all twenty-nine registered Array statements as typed conjuncts, and
the defence is demonstrated rather than asserted: weakening `denseShapeGuard_sound` or
`fresh_root_distinct` to `True` leaves the production module green and fails the inventory. The
inventories themselves are now registered, for String and Float as well as Array, since deleting the
file that is the entire substitution defence previously failed nothing.

One coverage gap surfaced at approval and is closed here: `lean/TSLean/Refinement/Array.lean`
belonged to no hash group, so the new production module would have shipped unhashed, and no count
refresh would have revealed it. The generator now asserts that every module under `lean/TSLean/JS`
and `lean/TSLean/Refinement` is covered by some hash group, scoped to inputs without a pinned
revision because a frozen input describes a tree this checkout is not at. Counts move to 599 audited
JS proofs, 191 audited and 178 required refinement proofs, and 189 Lean jobs.
