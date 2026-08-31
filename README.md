> Edited & maintained by Claude; presented as-is.

# TSLean

TSLean compiles Lean 4 to TypeScript and TypeScript to Lean 4.

The Lean-to-TypeScript compiler turns a proved Lean program into TypeScript for JavaScript
runtimes. Lean states executable behavior and invariants, the compiler emits TypeScript and
a certificate, and publication checks both against a small explicit trusted base.

The TypeScript-to-Lean compiler turns a typed TypeScript subset into Lean source. It
accepts as much TypeScript as it can translate solidly. It does not present reconstructed
Lean as a proof of the original program.

Where the two directions agree, they agree exactly. The round-trip profile states that
agreement structurally, and `tslean roundtrip` checks it by sending a program round in both
directions and running both language checkers.

Both directions share one repository, package, Lean toolchain, release gate, and evidence
system. Their compiler modules stay separate because their semantics and proof obligations
differ.

## Status

TSLean is under active development. Neither compiler accepts its source language in full.

| Direction          | Current contract                                                                                                                                                     |
| ------------------ | -------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| Lean to TypeScript | Compiles an explicit elaborated Lean fragment and rejects unsupported reachable declarations before publication. Whole-compiler refinement certificates are under construction. |
| TypeScript to Lean | Compiles a typed TypeScript subset. `--strict` accepts output only when it carries no placeholder and Lean accepts it under the pinned toolchain.                     |
| Round trip         | Checks the declared intersection of the two directions. It reports counterexamples. It states no theorem.                                                            |

The repository claims only measured properties and named theorems. It does not treat
differential agreement as proof or successful compilation as application correctness.

Current local evidence includes:

- 1,904 passing tests and 10 explicit todo tests
- 7,587 differential vectors
- a complete 184-job Lean build
- 604 JavaScript trusted-base checks
- 263 refinement trust checks and 250 refinement proofs
- three deterministic Lean-to-TypeScript example trees
- a 4,096-input exhaustive placement example

Run `bun run verify` to reproduce the complete local gate.

## Requirements

- Linux
- Lean 4.33.1 through `elan`
- Bun
- Node.js 18 or newer
- `/proc`
- `/usr/bin/flock` from util-linux

The Lean-to-TypeScript publisher uses Linux process and filesystem identity facilities. The npm package therefore declares Linux as its supported operating system.

## Install from source

```bash
git clone https://github.com/AshishKumar4/TSLean.git
cd TSLean
bun install
bun run build
```

The npm name is not published yet.

## Command line

TSLean exposes one executable and three commands.

```text
tslean ts-to-lean <file|dir> [options]
tslean lean-to-ts [options]
tslean init [dir]
```

Removed positional and `compile` forms are rejected. The CLI does not infer a direction.

### TypeScript to Lean

Compile one file:

```bash
tslean ts-to-lean src/counter.ts --output lean/Counter.lean --strict
```

Compile a project directory:

```bash
tslean ts-to-lean src --output lean/Generated --tsconfig tsconfig.json
```

Use `--strict` to accept output only when Lean accepts it. Strict compilation refuses on any
placeholder in the emitted Lean, on any Lean error, and on a toolchain it cannot run. A
strict refusal writes no output file or project tree. Point `--lean-project` at the Lake
project the elaboration runs against; it defaults to the one this package ships.

### Lean to TypeScript

```bash
tslean lean-to-ts \
  --project-root lean \
  --module TSLean.Examples.Placement \
  --source lean/TSLean/Examples/Placement.lean \
  --declaration TSLean.Examples.Placement.choosePlacement \
  --out-dir generated \
  --manifest generated/tslean.manifest.json
```

Add `--check` to compare a clean regeneration with the committed tree. Add `--require-attestation` with `--check` when environment attestation drift must also fail.

The compiler emits one TypeScript module per Lean module, one shared runtime module, source maps, and a manifest. Publication is transactional. The manifest owns the generated tree and is the only authority for stale-file deletion.

See [Lean to TypeScript](docs/lean-to-typescript.md) for the fragment and artifact contract.

### Round trip

```bash
tslean roundtrip --manifest examples/agent-core/facets/generated/tslean.manifest.json
tslean roundtrip --source examples/roundtrip/tier.ts
```

`--manifest` sends a generated package Lean → TypeScript → Lean. It compares the generated
TypeScript with both the recovered Lean and the Lean module it came from. `--source` sends
TypeScript → Lean → TypeScript and compares the source TypeScript with recovered Lean. Each
run type-checks the TypeScript, elaborates Lean, enumerates inputs, reports whether coverage
was exhaustive, and repeats the trip to see whether it settles. See [Round trip](docs/roundtrip.md).

For a manifest, the original-Lean comparison uses the manifest's recorded project path. Pass
`--source-root` only if that original project moved. TSLean refuses the source comparison if
the selected directory lacks its own `lean-toolchain`.

## Package API

The package has one root facade and explicit subpaths for TypeScript-to-Lean,
Lean-to-TypeScript, and round-trip verification.

```ts
import { compileLeanToTypeScript, compileTypeScriptToLean } from 'tslean';

import { compileTypeScriptProjectToLean } from 'tslean/typescript-to-lean';
import { verifyLeanToTypeScriptPackage } from 'tslean/lean-to-typescript';
```

```ts
import { leanAccepts, verifyLeanToTypeScriptRoundtrip, verifyTypeScriptToLeanRoundtrip } from 'tslean';
```

`compileTypeScriptToLean` returns Lean code plus every degradation marker. `compileLeanToTypeScript`
returns a generated package and its semantic and environment evidence. `leanAccepts` elaborates
generated Lean under a pinned toolchain. The two `verify…Roundtrip` functions return the checks
and the counterexamples of one round trip.

## Verification boundary

The repository verifies concrete properties:

- generated Lean is parsed and built by Lean;
- `--strict` accepts TypeScript-to-Lean output only after Lean accepts it;
- the round trip runs both language checkers, compares executable behavior against recovered
  Lean and, for a generated package, its original Lean source, over an enumerated input domain;
- differential fixtures compare modeled source and target behavior;
- Lean-to-TypeScript artifacts bind their source closure, compiler inputs, toolchain, generated bytes, and publication transaction;
- trusted-base checks reject unapproved axioms and hidden generated semantics;
- stale generated output makes freshness checks fail.

The repository does not claim:

- full TypeScript or ECMAScript support;
- full Lean support;
- an end-to-end implementation-refinement theorem;
- cryptographic collision resistance as a Lean theorem;
- application correctness from successful compilation;
- correctness of a round trip from its agreement. Agreement over a finite domain says no
  counterexample was found in that domain, and each report states the domain it covered.

## Repository layout

```text
src/parser, src/rewrite, src/codegen   TypeScript to Lean
src/lean-to-typescript                 Lean to TypeScript
src/roundtrip                          Round-trip profile and verifier
lean/TSLean/LeanToTypeScript           Lean exporter
lean/TSLean/JS                         JavaScript semantic model
evidence                               Hash-bound evidence inputs and manifests
spec                                   Differential and compiler registries
tests                                  Unit, differential, package, and trust tests
examples                               Runnable examples for both directions
```

## Development

```bash
bun run build
bun run test
bun run lint
bun run verify
```

Use the exact commands recorded in `package.json`. Do not edit generated output or evidence manifests by hand.

## Documentation

- [Architecture](docs/architecture.md)
- [Lean-to-TypeScript fragment and evidence](docs/lean-to-typescript.md)
- [Round trip](docs/roundtrip.md)
- [Compiler trust policy](docs/trust.md)
- [Limitations](docs/limitations.md)
- [Contributing](docs/contributing.md)

## License

MIT
