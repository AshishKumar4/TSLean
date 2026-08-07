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
