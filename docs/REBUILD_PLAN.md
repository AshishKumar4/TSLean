# Status

Phase 0 complete on branch `rebuild/semantic-core`.

# TSLean: Rebuild Plan

**Location:** `/Users/ashishsingh/TSLean` (durable, in `$HOME`)
**Upstream baseline:** `github.com/AshishKumar4/TSLean` @ `3c16098`
**Strategy:** evolve the existing pipeline in place
**Output:** idiomatic Lean, earned per value-flow
**Durability:** local commits after every verified stage

---

## 1. What actually went wrong

The prior attempt produced eleven independent review rejections. Every one has the same
shape: *"accepted for the exact prior reproducer; the neighbouring case is still wrong."*
Truthiness, aliasing, switch semantics, effect propagation and stack safety were each
"fixed" three or four times.

That is not bad luck. It is the signature of a compiler with **no semantic specification**,
where each fix is pattern-matched to a failing test. Three causes sit underneath it.

**Cause 1 — static types were used as runtime semantics.**
`number → Float`, objects → `AssocMap String TSAny`, `toBool x = (x != default)`,
`instanceof` decided from static type compatibility. TypeScript's type system is
deliberately unsound and fully erased at runtime. It cannot be the semantic oracle.
Consequences measured in the transcript: `("1" as any) === 1` → `true`; `[] === []` → `true`;
`[] || fallback` → `fallback`; a structurally-compatible literal passing `instanceof`.

**Cause 2 — the compiler owned the semantics.**
Destructuring defaults, `for...of`, switch fall-through, `finally` completions, spread
ordering, `Object.assign`, class construction and property ordering were each hand-rolled
in TypeScript, and each was wrong at least once.

**Cause 3 — the trusted base was contaminated.**
`LawfulBEq Float` was `sorry`-backed and false for `NaN`, so the imported runtime could
prove `False`. JSDoc text was interpolated into `/-- -/` without escaping `-/`, so a
source comment could inject `axiom injected : False`. Both were confirmed exploits.

Secondary but fatal in practice: tests asserted **substrings of generated Lean**, so an
agent could turn a suite green while the semantics were wrong; and scale was ignored until
it exploded (exponential alias synchronisation exhausted 4 GB at depth 4, effect discovery
was `2^d`, SCC and let-chains were quadratic, and parse/lower/print/audit each overflowed
the stack).

---

## 2. The correction

> **Push the semantics into Lean. Keep the compiler structural.**

One executable ECMAScript-subset model in Lean becomes the ground truth. The compiler
stops deciding what `&&`, `===` or `finally` mean and instead maps AST shapes onto model
combinators. A specification cannot be overfitted to.

This directly dissolves Cause 1 and Cause 2. Cause 3 is closed by construction rules in §6.

### Reconciling idiomatic output with soundness

You require idiomatic Lean from the start. The sound way to get it is to treat a
representation choice as a **claim requiring evidence**, not as a consequence of a declared
type.

```
Refinement := {
  carrier  : LeanTy          -- Float, String, Array α, a structure, ...
  inject   : carrier → JSValue
  ops      : OpTable         -- operation-by-operation correspondence
  evidence : Evidence
}

Evidence := Proved  (a discharged commuting lemma)
          | Guarded (a compiler-inserted narrowing establishes it)
          | Assumed (permitted by the active profile; recorded in the ledger)
```

Rules:

- A refinement attaches to a **value flow** established by dataflow, never to a declared type.
- If any operation in the flow lacks a commuting lemma, **that flow** degrades to `JSValue`.
  Degradation is local, visible, and reported.
- `any` and `unknown` never refine.
- Every `Assumed` refinement appears in the artifact's assumption ledger and can be
  forbidden by a verification profile.

For well-typed Gatekeeper and Durable Object code this refines almost everywhere:
`function add(a: number, b: number): number` emits `Float → Float → Float` with the lemma
discharged. The output is idiomatic. It simply cannot lie when the evidence is absent.

---

## 3. Architecture

```text
TSLean.JS            executable ECMAScript-subset semantics in Lean   [ground truth]
   ^
   | refines (with evidence)
   |
Refinement layer     Float / String / Array / closed records / structures
   ^
   |
Compiler             TS AST -> IR -> LeanAST -> printed Lean          [structural]
   |
   v
tslean-cloudflare    Workers / DO / RPC models (separate Lake package)
```

The native refinement package is a consumer of `TSLean.JS`: its relations interpret native Lean
values against the JS heap and value model without changing that model. It does not select a Lean
representation from TypeScript declarations yet, and no compiler or type-mapping behavior depends
on it. That selection remains future compiler work requiring explicit refinement evidence.

The core stays domain-neutral. No Gatekeeper, approval-queue, credential or Workshop
concepts enter it. Cloudflare semantics live in their own package; Gatekeeper policy lives
further downstream and is out of scope here.

### `TSLean.JS`

```lean
inductive JSValue
  | undef | null | bool (b : Bool) | num (f : Float)
  | str (s : String) | bigint (i : Int) | sym (id : SymbolId)
  | ref (r : RefId)              -- objects, arrays, functions, instances

structure Obj where
  props      : OrderedProps      -- integer indices ascending, then insertion order, then symbols
  proto      : Option RefId
  callable   : Option Closure
  exotic     : ExoticKind
  extensible : Bool

inductive Completion (α)
  | normal (v : α) | ret (v : JSValue)
  | brk (l : Option String) | cont (l : Option String) | thrown (v : JSValue)
```

Abstract operations carry their spec names: `ToPrimitive`, `ToNumber`, `ToString`,
`ToBoolean`, `ToPropertyKey`, `StrictEquality`, `LooseEquality`, `TypeOf`,
`InstanceOfOperator`, `OrdinaryOwnPropertyKeys`.

`JSM ε α` threads the heap, a trace of external events, and completions. External
behaviour (`fetch`, clock, random, storage) arrives as a `PlatformModel` parameter.
**Never as an axiom.**

The entire attempt-1 counterexample corpus becomes decided-once behaviour of this model:
`[] === []` is `false` by `ref` identity; `[] || x` is `[]` because `ToBoolean (ref _)` is
`true`; mutation observed through `finally` works because the heap is threaded through the
completion; `Object.assign` mutates the target and returns the same `ref`.

---

## 4. The IR contract change

This is where the type-driven assumption physically lives, so evolving in place means
changing it explicitly.

| | Today | After |
|---|---|---|
| `IRExpr.type` | resolved type that **selects** the Lean representation | `refinementHint` — evidence input only |
| Semantics | decided in the parser and lowerer | `jsSemantics`: the model combinator this node maps to |
| Representation | implied by the type | decided by the refinement judgment |
| Desugaring | hand-rolled in the parser | modelled in `TSLean.JS` |

Pipeline stages are unchanged (parse → IR → rewrite → lower → LeanAST → print). What
changes is who decides meaning.

**Risk of in-place evolution:** old semantics leak through code paths nobody touched.
**Mitigation:** the conformance corpus (§5) is the gate, it only grows, and no commit may
reduce the passing set.

---

## 5. Conformance corpus — the anti-overfit mechanism

A spec table of `{ id, source, expectation }`. Expectations are produced by executing the
source in Node. The harness compiles the source, evaluates the generated Lean, and compares
**result value, observable heap state, and the ordered external-event trace**.

Standing rules:

- A semantic fix adds **corpus entries**, never a bespoke unit test.
- Tests may assert on generated Lean text **only** for formatting. Never for semantics.
- The corpus only grows. No commit may reduce the passing set.
- No agent may weaken, skip or delete an entry.

Seeds: every counterexample recovered from the transcript — identity and aliasing,
coercion and operators, control flow and completions, effects, scoping, stdlib globals,
classes and construction, modules and namespaces, and the scale limits.

---

## 6. Trust rules (enforced by construction)

1. `compile : Input → Except (List Diagnostic) Artifact`. Total. No caught exception may
   become a placeholder.
2. The verified LeanAST path has **no `Raw` constructor**. Everything printed comes from
   typed nodes.
3. The placeholder audit runs on **parsed Lean**, not text. This closes both confirmed
   bypasses: an identifier literally named `sorry`, and false positives on `-- default`.
4. Comment content can never introduce declarations. Escaping is centralised and tested
   with the injection exploit.
5. **No fabricated instances.** `LawfulBEq Float` is deleted. JS equality is a JS function,
   not a Lean `BEq`.
6. Platform behaviour is a capability parameter, never an `axiom`.
7. `#print axioms` gate on every exported theorem. Allowlist: `propext`,
   `Classical.choice`, `Quot.sound`. Anything else fails the build.
8. Every analysis declares a complexity bound and has a scaling test that fails if exceeded.

---

## 7. Phases

Each phase ends with a commit and a recorded evidence entry. Nothing is "done" without the
exact command and its output.

### Phase 0 — Foundation *(no semantic change)*
- Clone to `/Users/ashishsingh/TSLean`, branch, **commit immediately**.
- Repo health: 24 `tsc` errors, the `IR_Types.lean`/`ir_types.lean` case collision,
  CLI test portability (`npx` → local executable), ESLint flat config.
- **Re-extract the transcript counterexample corpus** into committed `spec/corpus/`.
  The extraction agent for this was interrupted; this must be redone and is the highest
  value artifact in the rebuild.
- Honest baseline: regenerate README numbers from a manifest, delete contradictory claims
  (1,557 vs 1,588 tests; 112 vs 118 jobs; "0 sorry in runtime").
- Local gate script: build, tests, `lake build`, corpus, axiom manifest.
- **Exit:** green TypeScript build, green Lean build, corpus committed, baseline honest.

### Phase 1 — `TSLean.JS` *(compiler untouched)*
- Values, heap, ordered properties, completions, abstract operations, `JSM`.
- Delete `LawfulBEq Float`, every fabricated instance, every `sorry`-backed `Inhabited`.
- Differential-test **the model alone** against Node using the corpus, with no compiler in
  the loop.
- **Exit:** model passes the corpus; zero `sorry` in `TSLean.JS`; axiom allowlist clean.

### Phase 2 — Refinement judgment
- `Refinement`, the three evidence kinds, and the commuting-lemma library for `Float`,
  `String`, `Bool`, `Array`, and closed records.
- Dataflow that establishes refinements and degrades locally with a diagnostic.
- **Exit:** `add(a: number, b: number): number` emits `Float → Float → Float` with the lemma
  discharged; an untyped variant emits `JSValue` and reports why.

### Phase 3 — Rewire the pipeline *(in place)*
Migrate construct groups in dependency order, each gated by the corpus:
values and operators → control flow and completions → functions and closures →
objects, arrays and property order → classes and prototypes → destructuring and spread →
exceptions → iteration → modules, namespaces and enums → async.
Strip raw-string printing; make `compile` total; delete superseded special cases as each
group lands.
- **Exit:** corpus fully green; old type-driven paths deleted.

### Phase 4 — Proof linkage
- Replace the toy preservation theorem (it relates two near-identical 10-constructor toy
  ASTs and connects to nothing in the real pipeline).
- Per-compilation certificate plus a small Lean checker; per-function native-link theorems
  so a printer defect makes Lean reject the file.
- Replace vacuous obligations (`n / d = n / d := rfl`) with source-linked obligations that
  **fail** when unproved.
- **Exit:** certificate checked in Lean; obligations non-vacuous; axiom gate green.

### Phase 5 — `tslean-cloudflare` *(separate Lake package)*
Compatibility profile; HTTP values and linear bodies; RPC capabilities, visibility and
ownership; DO lifecycle, storage, transactions, input/output gates, alarms; WebSocket
hibernation; Dynamic Workers outbound policy. Differential against `workerd`.

### Phase 6 — Real corpus
One Durable Object project end-to-end, then one Gatekeeper. Zero degradation, generated
Lean compiles, differential green.

---

## 8. Process rules

- **Commit after every verified stage.** This is the rule whose absence destroyed the prior
  attempt.
- `EVIDENCE.md`: every claim paired with the exact command and its output.
- Sub-agent reports are **not** trusted. The corpus and the gate script decide.
- Reviews re-run the full corpus, not just the diff.
- Complexity budgets are acceptance criteria, not aspirations.

---

## 9. Honest sizing and residual risk

The prior attempt consumed an entire long session and reached roughly Phase 0 plus a
partial, unsound Phase 3. It never began Phases 1, 2, 4, 5 or 6. This plan front-loads the
semantics work that attempt skipped, so early phases will feel slower and later phases
should stop producing whack-a-mole rejections.

Phases 0–2 are the ones that determine whether this succeeds. I would not claim any
completeness result before Phase 3 closes.

**Residual risk accepted:** local-only commits survive the temp-purge failure that just
occurred, but not disk or machine loss.


---

# Plan Feedback

I've reviewed this plan and have 1 piece of feedback:

## 1. General feedback about the plan
> So would we finally have a WELL ORGANIZED, WELL DESIGNED TS/assemblyscript -> Lean compiler for formally proving if a typescript software/codebase is perfect and bug free?

---
