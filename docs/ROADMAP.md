# TSLean: roadmap to completion

Written against `48c59ed`. Every claim here was measured, not inferred; where a number is a guess it
says so. This supersedes the sequencing in `REBUILD_PLAN.md` §7 while keeping its architecture and
its trust rules unchanged.

## What "complete" means

Unchanged from the plan, restated so it can be checked:

- Every file in a pinned corpus's dependency closure is processed.
- Zero `sorry`, zero semantic `default`, zero holes, zero unapproved `TSAny` in emitted output.
- Every generated Lean module compiles.
- Differential behaviour matches Node for the modelled semantics.
- Exported theorems depend only on approved axioms, **across the transitive closure of what the
  compiler emits** — not merely inside two hand-picked namespaces.
- One Durable Object project and one Gatekeeper end-to-end with zero degradation.

## Where we actually are

| Layer | State |
|---|---|
| `TSLean.JS` semantics | 603 audited proofs, zero formal debt, 7264 Node comparisons |
| `TSLean.Refinement` | complete carrier set (Bool, BigInt, String, Float, dense Array, closed Record), 239 proofs |
| Falsifiability | Lean build gate + output-based `--strict` exist |
| Compiler | consumes **none** of the above |
| Corpus | 104 entries, 104 red; **only 24 have any executable form** |

The gap is one thing, and it is not a refactor: **generated Lean never imports `TSLean.JS`.** There
are zero matches for `import TSLean.JS` under `lean/TSLean/Generated/`. Output targets
`TSLean.Runtime.*`, where `abbrev TSAny := String`. `Refinement/Execution.lean` is an eight-line
empty reservation. The bridge does not exist.

## Five findings that reorder everything

**1. There is a second compiler in the tree, ~5,034 lines, and it cannot run.**
`src/preprocessor/tsc-to-json.ts` (602) → `lean/TSLean/JsonAST.lean` (232) →
`lean/TSLean/V2/FromJSON.lean` (2748, 13 `sorry`) → `lean/TSLean/V2/Printer.lean` (444, 8 `sorry`),
wired by `scripts/fixpoint-verify.sh` to `lean_exe tslean` via `lean/TSLean/Main.lean`. Three scripts
hardcode `/opt/lean4/lean-4.29.0-linux/bin`, which does not exist here, and there is no CI.

**2. The self-host bootstrap is fabricated.** `scripts/selfhost-adapter.ts` discards transpiler output
for 11 of 12 modules and substitutes hand-written namespaces.
`lean/TSLean/Generated/SelfHost/typemap_index.lean` is 39 hand-written lines standing in for a
512-line source. `lean/TSLean/Proofs/PipelineCorrectness.lean` then proves
`selfhost_modules_typecheck : True := by trivial` and comments that all 11 transpiled modules are
well-typed.

**3. `--verify` emits Lean that does not compile.** Two of its three obligation kinds are ill-typed
(`ArrayBounds` cites a nonexistent lemma; `OptionIsSome` calls `.isSome` on `α`), and the third is
`n / d = n / d := rfl` with an unused hypothesis. Its tests assert substrings of generated text, so
nothing noticed. All three properties are also wrong for JavaScript: `n / 0` is `Infinity`, `a[i]`
out of range is `undefined`, and `Option` is a carrier the compiler chose.

**4. Four live `Math` defects sit inside a currently-green build-gate fixture.** Measured Lean against
Node on exact bits: `Math.max(1, NaN)` gives `1.0` where Node gives `NaN`; `Math.max(0, -0)` gives
`-0` where Node gives `+0`; `Math.min(0, -0)` is likewise inverted; `Math.round(-0.5)` gives `-1`
where Node gives `-0`. Root cause is Lean's `max a b = if a ≤ b then b else a` against NaN, and
half-rounding away from zero rather than toward `+∞`. None is in the corpus.
`tests/fixtures/basic/interfaces.ts` uses `Math.sqrt` and is green today.

**5. No gate can detect the worst miscompilation we know about.** `completion-labeled-loop-discarded`
returns `0` instead of `6`. `--strict` accepts it, `lake env lean` exits 0, and the only signal is a
`unused variable` warning that the build gate deliberately filters out. The corpus's own
`priorLean.kind` field splits the 45 `compiler-only` entries into 23 `kind:"error"` (catchable by the
existing build gate today) and 22 `kind:"result"` (catchable only by executing generated Lean, which
nothing does).

## Phase A — remove what lies (no behaviour change)

Deletes roughly 18,000 lines and changes nothing any test covers. It comes first because every later
gate is weaker while these exist, and because two of them actively assert false things.

| # | Item | Lines | Why |
|---|---|---|---|
| A1 | untrack and delete `staging/` | −9751 | gitignored yet tracked; three stale copies of SelfHost output |
| A2 | delete `lean/TSLean/Proofs/` | −2417 | proves an identity function commutes with itself; contains 3 `axiom`s asserting compiler correctness and a `native_decide` injecting `Lean.ofReduceBool` |
| A3 | delete the second compiler and the fake self-host | −5034 | finding 1 and 2; includes `V2/`, `JsonAST.lean`, `Parser.lean`, `Codegen.lean`, `tsc-to-json.ts`, `selfhost-adapter.ts`, `Generated/SelfHost/` |
| A4 | delete `src/verification/` and `--verify` | −258 | finding 3 |
| A5 | delete `src/stubs/dts-reader.ts` | −586 | reachable only from its own test; emits `opaque`/`axiom` |
| A6 | delete dead stdlib method tables and utility-type cases | −225 | all four tables reachable only via uncalled `lookupMethod`; names a nonexistent `AssocSet.forM` |

Nothing here is salvageable for the real preservation work: Phase D's theorem is over different
objects entirely.

## Phase B — make the gates real

**B1. Extend the trust gate to the emitted import closure.** This is the single highest-value item in
the roadmap. The gate audits `TSLean.JS` and `TSLean.Refinement` by namespace prefix; it rejects
`TSLean.Runtime` imports *from* `TSLean.Refinement`, knowing that module is tainted, but never audits
what the compiler emits. Every generated module imports `TSLean.Runtime.Basic` and
`TSLean.Runtime.Coercions`. That closure carries **19 unaudited `axiom`s** (13 in
`Runtime/Monad.lean` alone) and 12 `sorry`-backed `Inhabited` instances. It is how a documented,
supposedly-deleted `sorry`-backed `LawfulBEq Float` survived in the shipped path until `48c59ed`.

Four changes: derive the closure from `LowerCtx.resolveImports` rather than a hand-written list; audit
by module rather than by namespace prefix; audit **all** constants, not only `Prop`-valued ones (an
`Inhabited` instance is not a `Prop`, so today's audit cannot see it); and add the converse of the
orphan check — a source with no `.olean` — so dead Lean announces itself. **It lands red on purpose.**

**B2. Delete the 12 `sorry`-backed `Inhabited` instances.** The honest fix is no instance. These types
are `opaque X : Type` and may be empty, so `Inhabited X` is a false proposition; giving it a body
would be worse, because `default : X` would silently become a real value downstream. Removing them
makes degradation sites fail to elaborate, which is the point. This turns B1 green.

**B3. Tier-1 corpus enforcement — 23 entries, one day.** Add each `kind:"error"` entry as a build-gate
fixture with a `KNOWN_BAD` row pinned to its exact diagnostic. The mechanism already exists and
already forces promotion on fix. This converts 23 entries from "cannot fail" to "pinned red" with no
new infrastructure.

**B4. Enforce the `scale` group.** Nine entries have neither tests nor todos —
`tests/corpus-schema.test.ts` only forces a todo for `baseline-suite-*` provenance. This is the
silently unenforced hole.

**B5. Runnable corpus programs.** The 22 `kind:"result"` entries are fragments; execute-and-compare
needs a program per entry. Add `spec/corpus/programs/<id>.ts` rather than a schema field, so the
schema stays stable and the file *is* the fixture.

**B6. Tier-3 execute-and-compare.** The one genuinely new piece of infrastructure, and what every
later claim depends on. Reuse `tests/differential/canonical.ts` and `compare.ts`; add a temp Lake
target and `lake env lean --run` a generated `main` printing a canonical observation. Per-entry
runtime is unmeasured; if it is seconds, this is an opt-in script like `lean:gate`, not part of
default `test`.

**B7. CI.** There is none. `verify` is a manual script and three scripts hardcode a Linux Lean path.
B1's gate is worthless unattended.

## Phase C — the refinement bridge (Phase 2 exit)

The exit criterion: `add(a: number, b: number): number` emits `Float → Float → Float` with the
commuting lemma discharged, and an untyped variant emits the model's value type and reports why.

Three measured facts shape this. `mapType` has exactly **one** importer, so the seam is narrow.
`Float.add_commutes` takes only the `Add` law, **not** the bridge — so the exit criterion's assumption
ledger has exactly one entry. And the emitted term already elaborates against the committed lemma;
what is missing is the *earning*.

- **C1. The judgment, zero output change.** `src/refinement/{types,lemmas,index}.ts`. The verdict
  attaches to a **flow**, held in a side table — not to an `IRNode` (mirror state) and never to a
  declared type (that is Cause 1). The analysis is the weakest that works: intra-declaration,
  flow-insensitive union-find over the rewritten IR, which is lexical name resolution plus
  union-find, not dataflow in the fixpoint sense. Add `IRType.Opaque` at the three `mapType` sites
  that mean "never refines", lowered to `TSAny` so bytes are identical. Wire the dead
  `src/errors.ts` `DiagnosticCollector` and add one code, `TSL104`. Acceptance is byte-identical
  output.
- **C2. Emission.** Refined flows get their carrier and one theorem per refined operation, with a
  real proof term — never a `sorry` obligation, never an unchecked comment. Degraded flows get
  `TSLean.JS.Value`. `JSValue` is **absorbing**: a refined flow joining a degraded one degrades,
  which is what lets C2 ship without codec application and therefore without `JSM`.
- **C3. Close the pinned defect.** Anonymous objects degrade instead of emitting
  `AssocMap String TSAny`, promoting the sole `KNOWN_BAD` entry. Widen that entry first — it pins
  only half its own fixture's defect today, since `scale`'s body silently becomes `default`.
- **C4. `guarded` evidence.** `TypeNarrow` establishes guards; the analysis becomes flow-sensitive on
  narrowed variables; `BigInt.divide_commutes`'s `nonzero` gets discharged. First point at which a
  verification profile can distinguish `guarded` from `assumed`.
- **C5. Lean-side fusion.** Per-operation theorems do not compose into a whole-function claim today;
  the missing pieces are `sameValue` transitivity and congruence of the arithmetic operations, both
  of which look provable with no new assumption because `sameValue` is bit equality with NaNs
  identified.

The assumption ledger is per-flow, deduplicated by the content-derived id that
`Assumption.deterministicId` already computes, mirroring `Evidence.metadata`'s normalization. A
verification profile is an allowlist of assumption ids; "forbid `assumed`" is the empty allowlist.

## Phase D — translation certificates (Phase 4)

**Translation validation, not a verified compiler.** The compiler is ~11.5k lines of TypeScript whose
lowering changes on most commits; a verified-compiler theorem must be re-proved each time, and says
nothing until the whole language is covered. A per-compilation certificate moves the trust to a small
checker: net new trusted Lean is roughly 250 reviewable lines (`Term.eval`), with `denote_correct`
*checked* rather than trusted.

- The certificate is a **closed Lean term**, not JSON, printed through the existing typed printer —
  so no new escape hatch, and the kernel shape-checks it.
- References are **de Bruijn indices**. Measured: a string-keyed uniqueness check over 200 entries
  times out `by decide` after 7.2 s, while an index-based scope check over 1000 entries completes by
  `rfl` in 0.6 s. Use `rfl`, never `decide`, never `native_decide`.
- Carrier agreement needs **no proof**: the emitted definition's type is *computed* from the
  certificate, so a wrong arity or carrier is a kernel type error.
- The obligation is `denote = printed`, discharged by `rfl`, so the printer writes **no proof text**.
  Verified rejections: wrong operator, dropped parameter, wrong carrier, omitted declaration,
  renamed declaration, `sorry` anywhere — and **parenthesisation**, because IEEE addition is not
  associative, which means a pure formatting defect is caught.
- Source semantics is a **deep embedding of Core JS** whose meaning is `TSLean.JS`, not the TS AST
  (whose meaning is its erasure, defined by an unpinned `tsc`) and not today's `IRExpr` (whose
  semantics is the compiler's own type inference). The front-end obligation — that the embedding
  faithfully desugars the source — is discharged **differentially against Node**, which is what the
  existing harness is actually for.
- Non-vacuity reuses the two mechanisms that already work: the required-proof registry and typed
  contract inventories. Coverage is enforced by making the link total (omitting a declaration is a
  type error) and by requiring the compiler to *declare* what it did not certify.

A hard precondition was cleared at `48c59ed`: a certificate emitted into an environment that can
prove `False` certifies nothing.

## Phase E — finish the semantics

Ordered by leverage per line, not by the plan's original order. E2 and E3 are fully parallel with
everything else.

| # | Item | Entries | Size |
|---|---|---|---|
| E1 | References, `GetValue`/`PutValue`, evaluation order | 3 model-pending **+ 14 compiler-only**, 5 critical | medium |
| E2 | `switch` evaluator | 5 | small/medium |
| E3 | Numeric operators: `ToInt32`/`ToUint32`, bitwise, `**` | 3 | small |
| E4 | `Math` tiers | fixes 4 unrecorded defects | small/medium |
| E5 | Array builtins over `Call.call`, `push` aliasing | 6 | medium |
| E6 | Canonical iterables: `GetIterator`, allocated result objects, `IteratorClose` | closes a recorded gap | medium |
| E7 | Host globals and a real global object | 7 | medium |
| E8 | Effects rewrite | 11 + downstream | medium/large |
| E9 | Resumable execution: generators **and** async together | 2 | large |

**E1 first among these**: it unblocks 14 compiler-only entries including the whole `alias-*` cluster,
which is the largest and highest-severity group and is entirely `kind:"result"` — silently wrong.

**E4's shape matters.** Three tiers: constants and the bit-level operations (`abs`, `sign`, `trunc`,
`floor`, `ceil`, `round`, `max`, `min`) **proved** on `JSNumber`, which fixes the four defects by
construction rather than papering over them; `sqrt` **assumed**, since IEEE-754 mandates correct
rounding; transcendentals **unmapped and degraded**, because ECMA-262 permits
implementation-dependent results and claiming bit-equality with Node would be false.

**E8 is not "recurse into lambdas."** `inferNodeEffect` discards the checker outright (`void
checker`), matches IO by text prefix, and stops at nested function scopes so a callback's effects
never reach its caller. The fix is a call-graph fixed point over checker-resolved symbols, with
effects part of the function type. It must precede the object and class groups, whose entries fail as
*monad* errors rather than object errors.

**E9 merges generators with async.** They are one construct — resumable execution — and the plan as
written builds the mechanism twice. A job queue is machine state, not a new monad: a new `AsyncJSM`
would fork ~600 audited preservation proofs. `Machine.jobs` must be first-order because
`JSM P Unit` puts `Machine` in negative position; `BodyHook` already solves exactly this by keeping
the evaluator outside the machine and re-entering by `RefId`. `await` itself needs a defunctionalized
resumable free program, for which `CoercionProgram.lean` is the in-repo precedent at scale.

## Phase F — Cloudflare, after Phase D

**The experiment of doing this early has already been run and it failed.** `lean/TSLean/DurableObjects/`
is Phase 5 attempted before Phase 4: ~2,400 lines, ~120 discharged theorems, in the default build
target. It contains `snapshot_restore_identity`, a `rfl` proof that hibernation loses nothing —
the exact opposite of the truth, since hibernation evicts the isolate. `Transaction.commit` cannot
fail, so "atomicity" is untypeable. The proofs discharge; they are about the wrong objects.

First slice: **DO storage as a capability**, with `list()` ordering and the structured-clone value
domain as the theorem. It is the only candidate that is fully observable synchronously, fits
`Machine`/`Platform`/`TraceEvent` unchanged in shape, is load-bearing for every later theorem, and is
trivially differentiable. Gates cannot be first: `TSLean.JS` has no async, and building an async model
inside the Cloudflare package instead is precisely how `TSLean.Veil/` became 2,689 lines of parallel
semantics that no compiler output touches.

`workerd` is obtainable and scriptable (`1.20260814.1`, with `darwin-arm64` and `linux-64` binaries).
It serves over a socket rather than stdio, so the NDJSON *transport* does not transfer but the
*pattern* does — the harness's real seam is `Observation` plus `observationMismatch`. Miniflare is not
an acceptable fallback: ≥v4 wraps workerd, and earlier versions are a JavaScript reimplementation,
which is worse than no oracle because it looks authoritative. If workerd proves impractical, the
honest outcome is no differential and every storage theorem marked `Assumed` with the reason.

Dependency order within F: storage → transactions → alarms → hibernation → async in `TSLean.JS` →
input gate → output gate. The first four are reachable with existing machinery. The last two are not.

## Phase G — the real corpus

One Durable Object project end-to-end, then one Gatekeeper. Zero degradation, generated Lean
compiles, differential green.

## Honest sizing

Phase A is days and mostly deletion. Phase B is the highest value per unit effort and is largely
mechanical apart from B6. Phase C is the first point at which the project does something it has never
done. Phases D and E are the bulk. F and G are gated on D.

I would not claim any completeness result before Phase C lands and the corpus has its first green
entry. The plan's own judgement stands: no completeness claim before Phase 3 closes.
