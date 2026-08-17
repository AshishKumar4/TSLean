# Lean 4 to TypeScript

## Status

TSLean now has a working compiler slice from elaborated Lean 4 declarations to
TypeScript. The first fragment is deliberately small. It covers pure, total,
first-order decisions over finite algebraic data and immutable records.

The pilot compiles `TSLean.Examples.Placement.choosePlacement` to the checked-in
`examples/lean-to-typescript/placement.generated.ts`. The generated function is the
only TypeScript implementation of that decision. An exhaustive test compares all 4,096
inputs with Lean.

This establishes deterministic generation and exhaustive agreement for that finite
decision. It does not prove a general Lean-to-TypeScript refinement theorem.

## Source of truth

Lean owns every decision admitted to this pipeline. TypeScript contains generated code
and a content-bound provenance manifest. The local `bun run verify` release gate
recompiles the pilot and rejects stale output. No hosted CI workflow is committed. There
is no second handwritten decision table or handwritten TypeScript twin.

The compiler reads Lean's elaborated environment through a pinned Lean metaprogram. It
does not parse `.lean` text, scrape `#print`, consume `.ilean`, or reverse generated C.
Surface syntax, comments, and formatting are not semantic inputs.

## Pipeline

```text
pinned Lean source and imports
  -> Lean parser, elaborator, termination checker, and kernel
  -> TSLean semantic exporter
  -> versioned checked-fragment JSON IR
  -> TypeScript trust-boundary validator
  -> TypeScript AST
  -> deterministic TypeScript printer
  -> generated source and provenance manifest
```

The Lean exporter fails before code generation when a declaration leaves the fragment.
The TypeScript validator independently rejects malformed or unknown IR fields.

## Checked fragment v1

### Admitted declarations

- Safe Lean definitions accepted by Lean's termination checker.
- First-order parameters and results.
- Pure functions with no `IO`, `ST`, state monad, exception monad, FFI, or host calls.
- `Bool`.
- `Option T` where `T` is admitted and is not itself an `Option`.
- Finite, nonempty, non-indexed inductive types in `Type 0` whose constructors carry no data.
- Non-generic immutable structures in `Type 0` whose fields have admitted types.
- Non-recursive calls among admitted local definitions.
- leading `let` chains, structure construction and projection, `if`, Boolean equality, conjunction,
  disjunction, negation, and `Option.some`/`Option.none`.

### Rejected declarations

- `partial`, `unsafe`, and `opaque` definitions.
- Recursive and mutually recursive functions in v1.
- Higher-order parameters or results.
- Implicit and instance parameters.
- Dependent result types, indexed inductives, data declared in `Prop`, `Type 1`, or a higher
  universe, subtypes, and proof values.
- Constructors with payloads in v1.
- Nested `Option`; `T | undefined` cannot distinguish `none` from `some none`.
- Quotients, classical choice in executable data, axioms, theorem terms, and open terms.
- Mutable state, concurrency, clocks, randomness, storage, network calls, exceptions,
  promises, and resource handles.
- Any constant without an explicit compiler rule.
- Empty inductive types, and declaration, binder, or structure-field names outside the
  TypeScript-safe ASCII identifier subset.
- Module names outside the compiler's Lean-safe ASCII grammar: dot-separated segments beginning
  with `[A-Za-z_]` and continuing with `[A-Za-z0-9_'!?]*`. A module name selects the Lake module,
  Lean import, and provenance identity; it is not emitted as a TypeScript binding.
- Calls to definitions outside the frozen target-project module closure. Declaration namespaces
  may differ from the source module name, but every requested root must be defined by that exact module.

The exporter uses an allowlist for external constants. Unknown constants fail closed.
Adding a source construct requires a semantic rule, an unsupported-fragment regression
test, and differential tests.

## Type representation

| Lean                     | TypeScript v1        |
| ------------------------ | -------------------- |
| `Bool`                   | `boolean`            |
| finite nullary inductive | string-literal union |
| non-generic structure    | readonly interface   |
| `Option T`               | `T \| undefined`     |

`Nat`, `Int`, `Float`, `String`, lists, arrays, constructor payloads, and recursion are
not silently approximated. Each needs a separate representation decision and semantic
test suite. In particular, mapping unbounded `Nat` or `Int` to JavaScript `number` would
be unsound. A later numeric fragment must choose exact `bigint`, checked safe integers,
or an explicit bounded type.

## Runtime boundary

Generated functions are pure and contain no host, storage, clock, network, or FFI calls.
They assume each argument is related to its Lean type by the table above. A consumer
adapter must decode untrusted input to booleans, admitted string literals, and plain data
records before calling generated code. TypeScript `readonly` does not freeze an object or
exclude proxies, getters, prototype tricks, or unchecked JavaScript callers. Those are
outside the compiler correspondence claim unless an adapter validates them.

## Provenance

Provenance is recorded in two planes, and the split is enforced structurally: each input
carries a `kind`, every `kind` maps to exactly one plane, and a manifest whose input is filed
under the wrong plane is rejected at decode.

**Semantic identity** — everything the generated bytes are a function of, and the only thing
the generated header carries:

- source module and canonical declaration roots;
- the fragment version;
- every Lean source recoverable from Lake's build traces, and both projects' Lake configuration
  and `lean-toolchain` pins;
- compiler, emitter, IR, manifest, ordering, package, and Lean exporter SHA-256 values;
- the W-3 compiler registry and finite bounds artifact SHA-256 values;
- Lean toolchain identity and the exact Lean and Lake versions it reports;
- semantic IR SHA-256, one hash over the ordered semantic input closure, and the generated
  TypeScript body SHA-256.

**Environment attestation** — the machine that ran one generation, recorded in the manifest
sidecar and deliberately absent from the generated bytes:

- generation runtime identity and executable SHA-256, host platform and architecture;
- exact TypeScript version, compiler artifact, package metadata, and loaded library SHA-256 values;
- Lean and Lake executable and dynamically loaded runtime-closure SHA-256 values;
- the transitive compiled Lean module (`.olean`) closure, which Lake rebuilds from the pinned
  sources on every compilation;
- one hash over the ordered environment input closure.

A patch upgrade of Node, Bun, or the Lean binaries therefore changes the attestation and
nothing else: `--check` still passes, prints the drift, and is cleared by re-attesting the
manifest — never by editing the artifact. `--check --require-attestation` is the separate gate
that makes drift fatal for a release that must pin its generating environment too.

`generatedBodySha256` is the SHA-256 of the UTF-8 bytes produced by the TypeScript printer,
from the first generated declaration through its terminal line feed, before the provenance
header is added. The completed semantic identity includes that digest; the header then includes
the SHA-256 of the compact ordered semantic identity JSON. This ordering is deliberately
non-circular. `verifyLeanToTypeScriptArtifact` requires the exact semantic-identity-derived
header and rehashes the body.

The generated source binds the semantic identity and its input closure in its header. Compiler
runtime bytes are captured once while the compiler modules load; later filesystem bytes never
replace that snapshot in provenance. The compiler captures the PATH launcher used only for
toolchain discovery, then executes only the canonical Lake and Lean binaries returned for the
pinned toolchain. Ambient loader, Lean-path, and toolchain-override variables are removed from
compiler subprocesses. The executable loader and shared-library closure is captured in provenance,
and device, inode, size, modification time, and change time are rechecked around every tool execution.
It copies the shipped exporter, target project configuration, and target Lean sources into owned
read-only source trees before building either project. PATH wrappers and later target-source
mutations therefore cannot change the compiled bytes. It rebuilds with Lake's hash checks enabled
and rejects any changed input identity, byte closure, or module resolution; installed package files
are never build outputs. Changing Lean source, toolchain, imports, compiler code, fragment schema,
registry, bounds, or roots makes the freshness check fail until the artifact is regenerated.

The CLI rejects existing-directory destinations, paths beneath an existing non-directory, and
destination equality or containment against the other artifact and explicit source before
compilation. After compilation discovers the complete input closure, it repeats the same
canonical-path and inode relationship check against every input. Publication binds the canonical
parent directory handles, stages and fsyncs both artifacts, writes a recovery journal, and only
then replaces either destination. A failed stage or commit rolls both destinations back; a later
invocation restores the prior pair from a prepared journal or completes the published pair from a
durable committed marker before starting a new transaction. Parent-path swaps are detected, and
descriptor-relative operations cannot be redirected through a replacement path. Corrupt, stale,
or mutually inconsistent journal copies fail closed before recovery changes either destination.
An exclusive kernel lock serializes each unordered canonical artifact pair. The lock and journal
carry the same transaction, process, and process-start identity, so a contender cannot clean up a
live or foreign transaction; an interrupted owner is recovered only after that exact process is
gone. A replaced lock path invalidates the original publisher before destination replacement or
transaction cleanup.

`spec/lean-to-typescript/compiler-registry.json` is the single W-3 registry. Its model entry binds
the Lean entry point, transitive checked fragment, exhaustive oracle operation, generated source
and manifest, runtime adapter, and explicit 4,096-case bounds artifact. The release tests reject a
stale path, selector, target, adapter, non-canonical registry, or inconsistent cardinality.

Version 0.1 is explicitly Linux-only in package metadata and at the public compiler and CLI
boundary. It depends on Linux loader tracing, procfs process and directory-handle identities,
`O_DIRECTORY`/`O_NOFOLLOW`, and util-linux `/usr/bin/flock`. An unsupported operating system fails
before compiler or CLI filesystem mutation; a missing Linux mechanism fails closed when its
protected operation begins. The checked-in pilot provenance includes the exact Node, Lean, and
Lake executable bytes from its Linux release environment. Supporting another platform requires
equivalent toolchain-closure and crash-safe publication mechanisms plus newly ratified evidence;
matching semantic IR alone is insufficient.

## Evidence boundary

The Lean kernel checks the input declaration and its proofs. The fragment checker then
accepts a specific executable definition shape. The TypeScript emitter translates that
shape. These are separate claims:

1. Lean accepts the declaration as a safe definition.
2. The exporter admits it to a documented fragment.
3. The compiler emits deterministic, type-checking TypeScript.
4. Differential tests have found no disagreement on the tested domain.

Only the placement pilot has an exhaustive finite-domain comparison today. Agreement on
random or bounded inputs for a later fragment remains empirical. A compiler bug, Lean
compiler bug, TypeScript compiler bug, JavaScript engine bug, ABI mismatch, or incorrect
representation rule can still cause divergence.

Do not describe generated TypeScript as proved correct unless a separate semantics and
refinement theorem covers the exact fragment, compiler version, runtime representation,
and emitted program.

## Why direct TypeScript emission

Lean's supported native compiler emits C, with C and LLVM as Lake backends. The Lean FFI
uses an explicitly unstable ABI. Shipping Lean-compiled WebAssembly would retain the Lean
runtime and a serialization boundary; it would not produce an idiomatic TypeScript
library. A direct Lean IR or compiler IR to TypeScript backend would inherit low-level
closure, allocation, reference-counting, and runtime details that v1 does not need.

The checked semantic IR stays above Lean's compiler IR and below surface syntax. It
preserves the decisions needed by TypeScript while rejecting language features whose
runtime meaning has not been specified.

## Alternatives

### Lean to WebAssembly called from TypeScript

This offers the strongest reuse of Lean's executable semantics if a maintained Wasm
toolchain and runtime boundary exist. It also adds a runtime payload, initialization,
marshalling, debugging boundary, and platform constraints. Lake has no first-party
JavaScript or Wasm code-generation backend; Emscripten WebAssembly is instead a Tier-2
cross-compiled Lean platform. Keep this as a future runtime mode, not the source generation
path.

### Generated decision tables or JSON

Tables work well for small finite functions and make exhaustive evaluation easy. They
scale poorly to structured expressions and can become larger than the decision itself.
Use them as test or proof artifacts where appropriate, not as the universal compiler IR.

### Differential handwritten twins

Handwritten twins retain two mutable sources of truth. Differential testing can expose a
disagreement but cannot decide which side changed correctly. Once a declaration is
generated, its handwritten twin must be removed and a static gate must reject its return.

## Next phases

Each phase lands independently and keeps earlier fragments closed.

1. Define and verify portable equivalents for Linux toolchain closure, bound directory handles,
   process identity, and crash-safe pair locking before admitting a second platform.
2. Add payload-carrying algebraic data and pattern matching.
3. Add exact numeric representations with boundary tests against Lean.
4. Add structurally recursive lists and trees with a checked recursion rule.
5. Add strings only after Unicode indexing and normalization semantics are pinned.
6. Evaluate a Wasm runtime mode for programs that need more of Lean than direct source
   generation can expose cleanly.
7. Attempt a mechanized refinement theorem only after the IR and runtime representations
   stop changing.

## Stop conditions

Stop widening the compiler when any of these occurs:

- the fragment checker needs source-text heuristics or comments;
- emitted code needs a handwritten semantic twin or hidden fallback;
- a type mapping cannot state its exact runtime representation;
- a differential counterexample has no understood root cause;
- supporting a construct requires admitting arbitrary effects or opaque constants;
- generated TypeScript is materially harder to debug or ship than a Lean runtime module;
- the Lean compiler API used by the exporter cannot be pinned and regression-tested.

At a stop condition, keep the last closed fragment and use a Lean runtime boundary or a
handwritten adapter outside the compiler claim.

## Primary references

- [Lean elaboration and compilation](https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/)
- [Lean compiler IR API](https://lean-lang.org/doc/api/Lean/Compiler/IR.html)
- [Lean foreign-function interface](https://lean-lang.org/doc/reference/latest/Run-Time-Code/Foreign-Function-Interface/)
- [Lean build tools and native backends](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/)
- [TypeScript compiler API](https://github.com/microsoft/TypeScript/wiki/Using-the-Compiler-API)
