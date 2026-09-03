import TSLean.LeanToTypeScript.Semantics.Relation

/-!
# Effects, as store passing

`StateM σ α`, `ExceptT ε (StateM σ) α` and `EStateM ε σ α` reach the target as *synchronous
store-passing functions*: a computation is a function from the store to a pair of its answer and the
next store, and a bind is a `let` that names the pair and reads both halves back. Nothing about that
needs a new IR form or a new evaluation rule — a pair is a mapped Lean structure, a `let` is a `let`,
and a field read is a field read — so this module is not an extension of the machine model. It is the
proof that the encoding does what the monad says.

Three things are established here.

* The *type images*: what `Ty` a computation in each of the three monads reaches the target as.
* The *pair representation*: a pair value reaches the target as an object whose own keys are `fst`
  then `snd`, in that order, which is what makes reading the two halves back well defined.
* The *threading theorem*: the emitted bind enters the first computation exactly once, on the store
  it was given, and enters the continuation exactly once, on the answer and the *next* store, in
  that order. Every event either computation records is recorded, in order, and no event is
  introduced between them.

The threading theorem is what rules out the failure a reordered or duplicated store would cause, and
it is stated on the trace as well as on the value, so a lowering that read the store twice or ran the
continuation first would fail it even where the answer happened to agree.
-/

namespace TSLean.LeanToTypeScript.Semantics

open TSLean.JS

namespace Effect

/-! ## The type images -/

/-- The image of `StateM σ α`: a function from the store to the pair of the answer and the next
store. -/
def state (store value : Ir.Ty) : Ir.Ty := .function [store] (.pair value store)

/-- The image of `ExceptT ε (StateM σ) α` and of `EStateM ε σ α`, which share it: the answer half is
the `Except` image, so a raised error is a value in the pair rather than a second control path. The
store is threaded either way, which is what `EStateM`'s own `Result.error` carries. -/
def exceptState (error store value : Ir.Ty) : Ir.Ty :=
  .function [store] (.pair (.except error value) store)

/-- A pure computation's image is the image of a computation, so `pure` needs no separate form. -/
theorem state_pure_image (store value : Ir.Ty) :
    state store value = .function [store] (.pair value store) := rfl

/-- The two effect images differ in exactly one position: the answer half. -/
theorem exceptState_eq_state (error store value : Ir.Ty) :
    exceptState error store value = state store (.except error value) := rfl

/-! ## The pair, and reading its halves back -/

/-- The pair value a computation answers with: the answer and the next store, as the two declared
fields of the mapped `Prod` structure, in declaration order. -/
def pairValue (value store : Ir.Ty) (answer next : Source.Value) : Source.Value :=
  .record (.pair value store) [("fst", answer), ("snd", next)]

/-- A pair is a one-constructor mapped structure whose declared fields are `fst` then `snd`. This is
what makes the two field reads below total, and it is decided by `constructorsOf`, so the source
semantics, the lowering and the emitter all read one answer. -/
theorem pair_constructors (program : Ir.Program) (value store : Ir.Ty) :
    program.constructorsOf (.pair value store)
      = some [⟨"mk", [⟨"fst", value⟩, ⟨"snd", store⟩]⟩] := rfl

/-- Reading the answer half answers the answer. -/
theorem pair_fst (program : Ir.Program) (fuel : Nat) (scope : List Source.Value)
    (trace : Source.Trace) (value store : Ir.Ty) (answer next : Source.Value) :
    Source.eval program fuel (pairValue value store answer next :: scope) trace
        (.fieldGet (.varRef 0) "fst")
      = .value answer trace := by
  simp [Source.eval, Source.lookup, pairValue, Source.fieldValue?]

/-- Reading the store half answers the next store. -/
theorem pair_snd (program : Ir.Program) (fuel : Nat) (scope : List Source.Value)
    (trace : Source.Trace) (value store : Ir.Ty) (answer next : Source.Value) :
    Source.eval program fuel (pairValue value store answer next :: scope) trace
        (.fieldGet (.varRef 0) "snd")
      = .value next trace := by
  simp [Source.eval, Source.lookup, pairValue, Source.fieldValue?]

/-- A pair reaches the target as an object carrying exactly `fst` then `snd`, in that order, each a
standard data property. The order is observable — ECMAScript own-key order is insertion order for
string keys — so it is part of the representation rather than a detail. -/
theorem pairValue_represents {program : Ir.Program} {state : Target.State} {value store : Ir.Ty}
    {answer next : Source.Value} {answerImage nextImage : Value} {ref : RefId}
    (answerRelated : Relation.Represents program state answer answerImage)
    (nextRelated : Relation.Represents program state next nextImage)
    (shape : Relation.HasOwnFields state.heap ref
      [("fst", answerImage), ("snd", nextImage)]) :
    Relation.Represents program state (pairValue value store answer next) (.object ref) := by
  unfold pairValue Relation.Represents
  refine ⟨ref, [("fst", answerImage), ("snd", nextImage)], rfl, ?_, shape⟩
  unfold Relation.RepresentsFields
  refine ⟨answerImage, [("snd", nextImage)], rfl, answerRelated, ?_⟩
  unfold Relation.RepresentsFields
  refine ⟨nextImage, [], rfl, nextRelated, ?_⟩
  unfold Relation.RepresentsFields
  rfl

/-! ## The emitted bind, and the store it threads

`bindBody` is the body the emitter builds for a bind, over a scope that holds the store at index `0`,
the continuation at index `1` and the first computation at index `2` — the layout an emitted
`(first, rest) => (store) => …` closure leaves behind. It names the first computation's pair with a
`let`, then applies the continuation to the answer and the next store.

The theorem below is about that exact term. It is not a claim about an idealised bind: the emitter
has one bind shape, and this is it.
-/

/-- The emitted body of a bind: name the first computation's pair, then continue on both halves. -/
def bindBody : Ir.Expr :=
  .letBind "step" (.apply (.varRef 2) [.varRef 0])
    (.apply (.varRef 2) [.fieldGet (.varRef 0) "fst", .fieldGet (.varRef 0) "snd"])

/--
The emitted bind threads the store exactly once, in order.

Given a first computation that answers a pair on the store it is handed, the bind enters it once,
reads both halves of the pair it answered, and enters the continuation once on the answer and the
*next* store. The trace the whole bind produces is the first computation's trace followed by the
continuation's, with nothing between them, so a lowering that entered the continuation first, or
re-entered the first computation to re-read the store, would fail this statement even where the
answer agreed.
-/
theorem bind_threads (program : Ir.Program) (fuel : Nat) (trace : Source.Trace)
    (value store : Ir.Ty) (storeValue : Source.Value)
    (firstCaptured : List Source.Value) (firstParameters : List Ir.Field) (firstBody : Ir.Expr)
    (restCaptured : List Source.Value) (restParameters : List Ir.Field) (restBody : Ir.Expr)
    (answer next : Source.Value) (afterFirst : Source.Trace)
    (firstRun : Source.applyClosure program fuel trace firstCaptured firstParameters firstBody
        [storeValue]
      = .value (pairValue value store answer next) afterFirst) :
    Source.eval program fuel
        [storeValue, .closure restCaptured restParameters restBody,
          .closure firstCaptured firstParameters firstBody] trace bindBody
      = Source.applyClosure program fuel afterFirst restCaptured restParameters restBody
          [answer, next] := by
  unfold bindBody
  rw [Source.eval.eq_def]
  simp only [Source.evalList.eq_def, Source.eval.eq_def, Source.lookup,
    List.getElem?_cons_zero, List.getElem?_cons_succ]
  rw [firstRun]
  rfl

/--
A first computation that faults or exhausts stops the bind there: the continuation is not entered,
and the trace is the one the first computation produced. This is the other half of "exactly once" —
the emitted bind cannot recover a store the first computation never produced.
-/
theorem bind_stops (program : Ir.Program) (fuel : Nat) (trace : Source.Trace)
    (storeValue : Source.Value)
    (firstCaptured : List Source.Value) (firstParameters : List Ir.Field) (firstBody : Ir.Expr)
    (restCaptured : List Source.Value) (restParameters : List Ir.Field) (restBody : Ir.Expr)
    (stopped : Source.Outcome)
    (halted : (∃ fault after, stopped = .fault fault after) ∨ ∃ after, stopped = .exhausted after)
    (firstRun : Source.applyClosure program fuel trace firstCaptured firstParameters firstBody
        [storeValue] = stopped) :
    Source.eval program fuel
        [storeValue, .closure restCaptured restParameters restBody,
          .closure firstCaptured firstParameters firstBody] trace bindBody = stopped := by
  unfold bindBody
  rw [Source.eval.eq_def]
  simp only [Source.evalList.eq_def, Source.eval.eq_def, Source.lookup,
    List.getElem?_cons_zero, List.getElem?_cons_succ]
  rw [firstRun]
  rcases halted with ⟨fault, after, rfl⟩ | ⟨after, rfl⟩ <;> rfl

/-! ## Deciding a computation's answer, and what an `Eff`-to-IR compiler still owes

A bind threads the store; deciding what the answer *was* is a `match` on it. For
`ExceptT ε (StateM σ)` and `EStateM ε σ` the answer half is the `Except` image, so the shape every
effectful program is written in — `match ← act with | .error e => … | .ok v => …` — is a
payload-carrying `match` in return position. That shape had no lowering in this model: `Compile.expr`
refused it by name, so nothing above it could be lowered either.

It has one now. `Compile.returnBody` lowers it to `Target.Body.branch`, `Preservation.branchBody`
proves the lowering refines the source match, and `Preservation.evalArms_refines` is the scope lemma
the arms need: the payload the branch names with `const`s, reversed onto the enclosing scope, is
exactly the scope `Source.evalCases` binds — which is what makes the continuation's view of the store
binder above the payload the same on both sides. `Option`, `Except`, `JsonValue` and every declared
`enum` are covered, so deciding an answer, a raised error and a decoded value are all inside the
theorem.

Three constraints on such a compiler are left, and they are constraints rather than gaps: each is a
shape refused by name today, so a program that needs one is refused instead of published.

* A recursive traversal that takes a `List` apart in return position — `match xs with | [] => … | x ::
  rest => …` — is refused with `Fault.listMatch`: a list's alternatives are decided by array length
  and its payload is read with `subject[0]` and `subject.slice(1)`, which is a third dispatch shape
  with its own allocation, not a tag comparison and two own-property reads. A traversal written with
  the six higher-order list opcodes is covered instead, because those enter a real function object
  once per element.
* A `match` on the pair a computation answers is refused with `Fault.structureMatch`, because
  `Source.eval` gives a structure's value the `record` form. Reading `fst` and `snd` with field reads
  is what is modeled, and it is what `bindBody` above does.
* A bind chain inside an inline arrow has no emitted form: `emitExpression` refuses a `let` outside
  return position, so every effectful body has to be a declared function — which is what `bindBody`
  is. Lifting each chain into a declaration, or growing the emitter a block-bodied arrow, is a
  decision for that compiler and not something this model can settle.

`Program.HostSubstrate` stays the premise of every real effect, one row per host operation, and
`Preservation.ListsFit` stays owed by every list-producing row. Neither is changed by any of this.
-/

end Effect

end TSLean.LeanToTypeScript.Semantics
