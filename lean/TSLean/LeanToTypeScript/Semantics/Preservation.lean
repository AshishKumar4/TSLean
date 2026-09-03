import TSLean.Refinement.Primitive
import TSLean.Refinement.String
import TSLean.LeanToTypeScript.Semantics.Allocation
import TSLean.LeanToTypeScript.Semantics.Closure
import TSLean.LeanToTypeScript.Semantics.Compile
import TSLean.LeanToTypeScript.Semantics.Opcode

/-!
# Preservation, one theorem per admitted IR operation

`Op.Preserves` states, for each operation of `Ir.Op`, the correspondence that operation's own
lowering claims: given that each subexpression's lowering refines it from every aligned
configuration, the lowered whole refines the whole. `registry` is a total function on `Ir.Op`, so an
operation with no theorem does not compile.

`Family.Preserves` does the same for the three declaration families.

## The engine is a parameter

Every statement here is indexed by a `Runtime`. The `operation` row takes the opcode's own law,
`Ir.Opcode.Preserves`, as a hypothesis, and `Opcode.registry` discharges it from the opcode's
recorded assumption closure. Nothing about the engine is re-derived here and nothing is assumed:
what the twenty first-order opcodes owe is consumed, not restated.

The six higher-order list opcodes take no engine law at all. Their callback is a real function
object, so `value.map((element) => transform(element))` enters it once per element; both sides run
that entry, and the correspondence between them is the one `invoke_refines` proves, at one unit of
fuel and one application event per element, in element order.
-/

namespace TSLean.LeanToTypeScript.Semantics

open TSLean.JS

namespace Preservation

/-- A source configuration and a target configuration that agree: a valid heap, live callable
payloads, representing scopes, and a refining ordered trace. -/
structure Aligned (program : Ir.Program) (sourceScope : List Source.Value)
    (targetScope : List Value) (trace : Source.Trace) (state : Target.State) : Prop where
  heapValid : state.heap.WellFormed
  closuresValid : state.ClosuresWellFormed
  scope : Relation.RepresentsList program state sourceScope targetScope
  trace : Relation.RefinesTrace program state trace state.trace

/-- One lowered expression refines its source from every aligned configuration. -/
def Everywhere (program : Ir.Program) (target : Target.Program)
    (runtime : Runtime) (fuel : Nat)
    (expression : Ir.Expr) (emitted : Target.Expr) : Prop :=
  ∀ (sourceScope : List Source.Value) (targetScope : List Value) (trace : Source.Trace)
    (state : Target.State),
    Aligned program sourceScope targetScope trace state →
    Relation.Refines program state
      (Source.eval program fuel sourceScope trace expression)
      (Target.eval target runtime fuel targetScope state emitted)

/-- One lowered argument list refines its source from every aligned configuration. -/
def EverywhereList (program : Ir.Program) (target : Target.Program)
    (runtime : Runtime) (fuel : Nat)
    (expressions : List Ir.Expr) (emitted : List Target.Expr) : Prop :=
  ∀ (sourceScope : List Source.Value) (targetScope : List Value) (trace : Source.Trace)
    (state : Target.State),
    Aligned program sourceScope targetScope trace state →
    Relation.RefinesList program state
      (Source.evalList program fuel sourceScope trace expressions)
      (Target.evalList target runtime fuel targetScope state emitted)

/-- One lowered field list refines its source from every aligned configuration. -/
def EverywhereFields (program : Ir.Program) (target : Target.Program)
    (runtime : Runtime) (fuel : Nat)
    (fields : List (String × Ir.Expr)) (emitted : List (String × Target.Expr)) : Prop :=
  ∀ (sourceScope : List Source.Value) (targetScope : List Value) (trace : Source.Trace)
    (state : Target.State),
    Aligned program sourceScope targetScope trace state →
    Relation.RefinesFields program state
      (Source.evalFields program fuel sourceScope trace fields)
      (Target.evalProperties target runtime fuel targetScope state emitted)

/-- One lowered function body refines its source from every aligned configuration. -/
def EverywhereBody (program : Ir.Program) (target : Target.Program)
    (runtime : Runtime) (fuel : Nat)
    (body : Ir.Expr) (emitted : Target.Body) : Prop :=
  ∀ (sourceScope : List Source.Value) (targetScope : List Value) (trace : Source.Trace)
    (state : Target.State),
    Aligned program sourceScope targetScope trace state →
    Relation.Refines program state
      (Source.eval program fuel sourceScope trace body)
      (Target.evalBody target runtime fuel targetScope state emitted)

/-- Every declared function has a lowered counterpart, declaring the same number of parameters. -/
def Lowered (program : Ir.Program) (target : Target.Program) : Prop :=
  ∀ (name : String) (parameters : List Ir.Field) (result : Ir.Ty) (recursion : Ir.Recursion)
    (body : Ir.Expr),
    program.function? name = some (parameters, result, recursion, body) →
    ∃ emitted, target.find? name = some emitted ∧ emitted.parameters = parameters.length

/-- Every declared function's lowered body refines it, at this fuel. -/
def EveryFunction (program : Ir.Program) (target : Target.Program) (runtime : Runtime)
    (fuel : Nat) : Prop :=
  ∀ (name : String) (parameters : List Ir.Field) (result : Ir.Ty) (recursion : Ir.Recursion)
    (body : Ir.Expr) (emitted : Target.Function),
    program.function? name = some (parameters, result, recursion, body) →
    target.find? name = some emitted →
    EverywhereBody program target runtime fuel body emitted.body

/--
Every list an evaluation produces is short enough to be an ECMAScript array.

ECMAScript caps an array's length at `Heap.maxArrayLength`. The emitted `[head, ...tail]`,
`[...left, ...right]` and array-method forms raise a `RangeError` beyond that cap rather than
producing a longer array, and a Lean `List` has no such cap, so this is a boundary of the
representation rather than a claim about it. Every list-producing row names it as a premise the
caller owes, instead of quietly assuming the allocation succeeds.
-/
def ListsFit (program : Ir.Program) : Prop :=
  ∀ (fuel : Nat) (scope : List Source.Value) (trace : Source.Trace) (expression : Ir.Expr)
    (element : Ir.Ty) (elements : List Source.Value) (next : Source.Trace),
    Source.eval program fuel scope trace expression = .value (.array element elements) next →
    elements.length ≤ Heap.maxArrayLength

/-! ## Support -/

/-- The empty list represents the empty list. -/
theorem represents_nil {program : Ir.Program} {state : Target.State} :
    Relation.RepresentsList program state [] [] := by
  unfold Relation.RepresentsList; rfl

/-- One representing pair is a one-element representing list. -/
theorem represents_singleton {program : Ir.Program} {state : Target.State} {value : Source.Value}
    {target : Value} (related : Relation.Represents program state value target) :
    Relation.RepresentsList program state [value] [target] := by
  unfold Relation.RepresentsList
  exact ⟨target, [], rfl, related, represents_nil⟩

/-- Two representing pairs are a two-element representing list. -/
theorem represents_pair {program : Ir.Program} {state : Target.State}
    {first second : Source.Value} {firstTarget secondTarget : Value}
    (firstRelated : Relation.Represents program state first firstTarget)
    (secondRelated : Relation.Represents program state second secondTarget) :
    Relation.RepresentsList program state [first, second] [firstTarget, secondTarget] := by
  unfold Relation.RepresentsList
  exact ⟨firstTarget, [secondTarget], rfl, firstRelated, represents_singleton secondRelated⟩

/-- Representation of a list is closed under concatenation. -/
theorem represents_append {program : Ir.Program} {state : Target.State} :
    ∀ (left : List Source.Value) (leftTarget : List Value) (rightSource : List Source.Value)
      (rightTarget : List Value),
      Relation.RepresentsList program state left leftTarget →
      Relation.RepresentsList program state rightSource rightTarget →
      Relation.RepresentsList program state (left ++ rightSource) (leftTarget ++ rightTarget)
  | [], leftTarget, rightSource, rightTarget, leftRelated, rightRelated => by
      unfold Relation.RepresentsList at leftRelated
      subst leftRelated
      simpa using rightRelated
  | head :: tail, leftTarget, rightSource, rightTarget, leftRelated, rightRelated => by
      unfold Relation.RepresentsList at leftRelated
      obtain ⟨target, restTargets, targetsEq, headRelated, tailRelated⟩ := leftRelated
      subst targetsEq
      unfold Relation.RepresentsList
      exact ⟨target, restTargets ++ rightTarget, rfl, headRelated,
        represents_append tail restTargets rightSource rightTarget tailRelated rightRelated⟩

/-- Representation of a list survives reversal, which is how a call binds its parameters. -/
theorem represents_reverse {program : Ir.Program} {state : Target.State} :
    ∀ (values : List Source.Value) (targets : List Value),
      Relation.RepresentsList program state values targets →
      Relation.RepresentsList program state values.reverse targets.reverse
  | [], targets, related => by
      unfold Relation.RepresentsList at related
      subst related
      exact represents_nil
  | head :: tail, targets, related => by
      unfold Relation.RepresentsList at related
      obtain ⟨target, restTargets, targetsEq, headRelated, tailRelated⟩ := related
      subst targetsEq
      simp only [List.reverse_cons]
      exact represents_append tail.reverse restTargets.reverse [head] [target]
        (represents_reverse tail restTargets tailRelated) (represents_singleton headRelated)

/-- A one-element representing list is one representing pair. -/
theorem representsList_one {program : Ir.Program} {state : Target.State} {value : Source.Value}
    {targets : List Value} (related : Relation.RepresentsList program state [value] targets) :
    ∃ target, targets = [target] ∧ Relation.Represents program state value target := by
  unfold Relation.RepresentsList at related
  obtain ⟨target, restTargets, targetsEq, headRelated, tailRelated⟩ := related
  unfold Relation.RepresentsList at tailRelated
  subst tailRelated
  exact ⟨target, targetsEq, headRelated⟩

/-- A two-element representing list is two representing pairs. -/
theorem representsList_two {program : Ir.Program} {state : Target.State}
    {first second : Source.Value} {targets : List Value}
    (related : Relation.RepresentsList program state [first, second] targets) :
    ∃ firstTarget secondTarget, targets = [firstTarget, secondTarget] ∧
      Relation.Represents program state first firstTarget ∧
      Relation.Represents program state second secondTarget := by
  unfold Relation.RepresentsList at related
  obtain ⟨firstTarget, restTargets, targetsEq, firstRelated, tailRelated⟩ := related
  obtain ⟨secondTarget, restEq, secondRelated⟩ := representsList_one tailRelated
  subst restEq
  exact ⟨firstTarget, secondTarget, targetsEq, firstRelated, secondRelated⟩

/-- A three-element representing list is three representing pairs. -/
theorem representsList_three {program : Ir.Program} {state : Target.State}
    {first second third : Source.Value} {targets : List Value}
    (related : Relation.RepresentsList program state [first, second, third] targets) :
    ∃ firstTarget secondTarget thirdTarget,
      targets = [firstTarget, secondTarget, thirdTarget] ∧
        Relation.Represents program state first firstTarget ∧
        Relation.Represents program state second secondTarget ∧
        Relation.Represents program state third thirdTarget := by
  unfold Relation.RepresentsList at related
  obtain ⟨firstTarget, restTargets, targetsEq, firstRelated, tailRelated⟩ := related
  obtain ⟨secondTarget, thirdTarget, restEq, secondRelated, thirdRelated⟩ :=
    representsList_two tailRelated
  subst restEq
  exact ⟨firstTarget, secondTarget, thirdTarget, targetsEq, firstRelated, secondRelated,
    thirdRelated⟩

/-- Positional scope lookup agrees on both sides. -/
theorem lookup_represents {program : Ir.Program} {state : Target.State} :
    ∀ (sourceScope : List Source.Value) (targetScope : List Value) (index : Nat),
      Relation.RepresentsList program state sourceScope targetScope →
      ∀ value, Source.lookup sourceScope index = some value →
        ∃ target, Target.lookup targetScope index = some target ∧
          Relation.Represents program state value target
  | [], _, _, related, _, found => by
      unfold Relation.RepresentsList at related
      subst related
      exact absurd found (by simp [Source.lookup])
  | head :: rest, targetScope, index, related, value, found => by
      unfold Relation.RepresentsList at related
      obtain ⟨target, restTargets, targetsEq, headRelated, tailRelated⟩ := related
      subst targetsEq
      match index with
      | 0 =>
          simp only [Source.lookup, List.getElem?_cons_zero, Option.some.injEq] at found
          subst found
          exact ⟨target, by simp [Target.lookup], headRelated⟩
      | position + 1 =>
          simp only [Source.lookup, List.getElem?_cons_succ] at found
          obtain ⟨image, lookupEq, related⟩ :=
            lookup_represents rest restTargets position tailRelated value found
          exact ⟨image, by simpa [Target.lookup] using lookupEq, related⟩

/-- The empty trace refines the empty trace. -/
theorem refinesTrace_nil {program : Ir.Program} {state : Target.State} :
    Relation.RefinesTrace program state [] [] := by
  unfold Relation.RefinesTrace; rfl

/-- Trace refinement survives appending one refining event, declared or anonymous. -/
theorem refinesTrace_append {program : Ir.Program} {state : Target.State} :
    ∀ (trace : Source.Trace) (targetTrace : Target.Trace) (event : Source.Event)
      (entry : Target.Event),
      Relation.RefinesTrace program state trace targetTrace →
      Relation.RefinesEvent program state event entry →
      Relation.RefinesTrace program state (trace ++ [event]) (targetTrace ++ [entry])
  | [], targetTrace, event, entry, related, eventRelated => by
      unfold Relation.RefinesTrace at related
      subst related
      unfold Relation.RefinesTrace
      exact ⟨entry, [], rfl, eventRelated, refinesTrace_nil⟩
  | head :: rest, targetTrace, event, entry, related, eventRelated => by
      unfold Relation.RefinesTrace at related
      obtain ⟨headEntry, restTarget, targetEq, headRelated, tailRelated⟩ := related
      subst targetEq
      unfold Relation.RefinesTrace
      exact ⟨headEntry, restTarget ++ [entry], rfl, headRelated,
        refinesTrace_append rest restTarget event entry tailRelated eventRelated⟩

/-- A JavaScript call with exactly the declared number of arguments binds them unchanged. -/
theorem bindArguments_exact :
    ∀ (arguments : List Value) (parameters : Nat), parameters = arguments.length →
      Target.bindArguments parameters arguments = arguments
  | [], 0, _ => rfl
  | [], _ + 1, count => by simp at count
  | _ :: _, 0, count => by simp at count
  | value :: rest, count + 1, lengths => by
      simp only [Target.bindArguments]
      rw [bindArguments_exact rest count (by simpa using lengths)]

/-- Reading a declared field of a record object answers the value the shape records. -/
theorem readMember_of_shape {ref : RefId} {entries : List (String × Value)}
    (state : Target.State) (shape : Relation.HasOwnFields state.heap ref entries)
    (name : String) (value : Value)
    (found : (entries.find? fun entry => entry.1 == name) = some (name, value)) :
    Target.readMember state name (.object ref) = .ok value state := by
  simp only [Target.readMember, shape.read name, found]
  rfl

/-- A successful source run is matched by a successful target run, and by nothing else. -/
theorem refines_value_inv {program : Ir.Program} {start : Target.State} {value : Source.Value}
    {trace : Source.Trace} {result : Target.Result}
    (refines : Relation.Refines program start (.value value trace) result) :
    ∃ target state, result = .ok target state ∧ Target.State.Extension start state ∧
      state.ClosuresWellFormed ∧ Relation.Represents program state value target ∧
        Relation.RefinesTrace program state trace state.trace := by
  cases result with
  | ok target state =>
      simp only [Relation.Refines] at refines
      exact ⟨target, state, rfl, refines.1, refines.2.1, refines.2.2.1, refines.2.2.2⟩
  | thrown error state => simp only [Relation.Refines] at refines
  | fault fault state => simp only [Relation.Refines] at refines
  | exhausted state => simp only [Relation.Refines] at refines

/-- An exhausted source run is matched by an exhausted target run, and by nothing else. -/
theorem refines_exhausted_inv {program : Ir.Program} {start : Target.State} {trace : Source.Trace}
    {result : Target.Result}
    (refines : Relation.Refines program start (.exhausted trace) result) :
    ∃ state, result = .exhausted state ∧ Target.State.Extension start state ∧
      state.ClosuresWellFormed ∧ Relation.RefinesTrace program state trace state.trace := by
  cases result with
  | ok target state => simp only [Relation.Refines] at refines
  | thrown error state => simp only [Relation.Refines] at refines
  | fault fault state => simp only [Relation.Refines] at refines
  | exhausted state => exact ⟨state, rfl, refines.1, refines.2.1, refines.2.2⟩

/-- Builds the refinement of a successful run. -/
theorem refines_value {program : Ir.Program} {start : Target.State} {value : Source.Value}
    {trace : Source.Trace} {target : Value} {state : Target.State}
    (extension : Target.State.Extension start state) (closuresValid : state.ClosuresWellFormed)
    (represents : Relation.Represents program state value target)
    (traceRefines : Relation.RefinesTrace program state trace state.trace) :
    Relation.Refines program start (.value value trace) (.ok target state) := by
  simp only [Relation.Refines]
  exact ⟨extension, closuresValid, represents, traceRefines⟩

/-- Builds the refinement of an exhausted run. -/
theorem refines_exhausted {program : Ir.Program} {start : Target.State} {trace : Source.Trace}
    {state : Target.State}
    (extension : Target.State.Extension start state) (closuresValid : state.ClosuresWellFormed)
    (traceRefines : Relation.RefinesTrace program state trace state.trace) :
    Relation.Refines program start (.exhausted trace) (.exhausted state) := by
  simp only [Relation.Refines]
  exact ⟨extension, closuresValid, traceRefines⟩

/-- A source run that faults claims nothing of the target. -/
theorem refines_fault {program : Ir.Program} {start : Target.State} {fault : Source.Fault}
    {trace : Source.Trace} {result : Target.Result} :
    Relation.Refines program start (.fault fault trace) result := by
  simp only [Relation.Refines]

/-- The configuration a subexpression's run leaves behind is aligned again. -/
theorem Aligned.step {program : Ir.Program} {sourceScope : List Source.Value}
    {targetScope : List Value} {trace nextTrace : Source.Trace} {state nextState : Target.State}
    (aligned : Aligned program sourceScope targetScope trace state)
    (extension : Target.State.Extension state nextState)
    (closuresValid : nextState.ClosuresWellFormed)
    (traceRefines : Relation.RefinesTrace program nextState nextTrace nextState.trace) :
    Aligned program sourceScope targetScope nextTrace nextState :=
  ⟨extension.nextWellFormed, closuresValid,
    Relation.RepresentsList.stable extension sourceScope targetScope aligned.scope, traceRefines⟩

/-- Every represented value is a valid heap value, so it may be stored in a fresh object. -/
theorem valueValid_of_represents {program : Ir.Program} {state : Target.State} :
    ∀ (value : Source.Value) (target : Value),
      Relation.Represents program state value target → state.heap.valueValid target = true
  | .boolean _, _, related => by
      unfold Relation.Represents at related; subst related; rfl
  | .nat _, _, related => by
      unfold Relation.Represents at related; subst related; rfl
  | .int _, _, related => by
      unfold Relation.Represents at related; subst related; rfl
  | .string _, _, related => by
      unfold Relation.Represents at related; subst related; rfl
  | .char _, _, related => by
      unfold Relation.Represents at related; subst related; rfl
  | .record _ _, _, related => by
      unfold Relation.Represents at related
      obtain ⟨ref, entries, targetEq, _, shape⟩ := related
      subst targetEq
      exact Relation.valueValid_of_hasOwnFields shape
  | .array _ _, _, related => by
      unfold Relation.Represents at related
      obtain ⟨ref, images, targetEq, _, dense⟩ := related
      subst targetEq
      exact Relation.valueValid_of_denseElements dense
  | .variant _ _ _, target, related => by
      unfold Relation.Represents at related
      obtain ⟨constructors, _, constructor, _, body⟩ := related
      by_cases nullary : Ir.allNullary constructors = true
      · rw [if_pos nullary] at body
        obtain ⟨_, targetEq⟩ := body
        subst targetEq
        rfl
      · rw [if_neg nullary] at body
        obtain ⟨ref, entries, targetEq, _, shape⟩ := body
        subst targetEq
        exact Relation.valueValid_of_hasOwnFields shape
  | .closure _ _ _, _, related => by
      unfold Relation.Represents at related
      obtain ⟨ref, _, targetEq, _, _, _, _, shape⟩ := related
      subst targetEq
      exact Relation.valueValid_of_hasOwnFields shape

/-- A record's own-property read answers the field the source reads. -/
theorem fields_lookup {program : Ir.Program} {state : Target.State} :
    ∀ (fields : List (String × Source.Value)) (entries : List (String × Value)),
      Relation.RepresentsFields program state fields entries →
      ∀ (name : String) (value : Source.Value), Source.fieldValue? fields name = some value →
        ∃ target, (entries.find? fun entry => entry.1 == name) = some (name, target) ∧
          Relation.Represents program state value target
  | [], entries, related, name, value, found => by
      unfold Relation.RepresentsFields at related
      subst related
      exact absurd found (by simp [Source.fieldValue?])
  | (field, head) :: rest, entries, related, name, value, found => by
      unfold Relation.RepresentsFields at related
      obtain ⟨target, restEntries, entriesEq, headRelated, tailRelated⟩ := related
      subst entriesEq
      by_cases same : field = name
      · subst same
        simp only [Source.fieldValue?, List.find?_cons, beq_self_eq_true, Option.map_some] at found
        simp only [Option.some.injEq] at found
        subst found
        exact ⟨target, by simp, headRelated⟩
      · have skip : (field == name) = false := beq_eq_false_iff_ne.mpr same
        simp only [Source.fieldValue?, List.find?_cons, skip] at found
        obtain ⟨image, lookupEq, related⟩ :=
          fields_lookup rest restEntries tailRelated name value found
        refine ⟨image, ?_, related⟩
        simp only [List.find?_cons, skip]
        exact lookupEq

/-- Running a lowering leaves the state exactly as it found it, whenever it succeeds. This is what
lets the tag chain read its scrutinee once per arm without the repeated reads being observable. -/
def StateStable (target : Target.Program) (runtime : Runtime) (fuel : Nat)
    (emitted : Target.Expr) : Prop :=
  ∀ (targetScope : List Value) (state : Target.State) (produced : Value) (next : Target.State),
    Target.eval target runtime fuel targetScope state emitted = .ok produced next → next = state

/--
A scrutinee the tag chain may read once per arm, and may also drop.

The chain evaluates the scrutinee once per comparison and, when the match has one arm, not at all.
Both are unobservable exactly when reading the scrutinee produces no event, spends no fuel and
changes no state, which is what `emitter.ts` restricts the scrutinee to a binding or a field read to
secure.
-/
structure Readable (program : Ir.Program) (target : Target.Program) (runtime : Runtime) (fuel : Nat)
    (scrutinee : Ir.Expr) (emitted : Target.Expr) : Prop where
  refines : Everywhere program target runtime fuel scrutinee emitted
  sourcePure : ∀ (sourceScope : List Source.Value) (trace : Source.Trace),
    (∃ value, Source.eval program fuel sourceScope trace scrutinee = .value value trace) ∨
      (∃ fault, Source.eval program fuel sourceScope trace scrutinee = .fault fault trace)
  targetStable : StateStable target runtime fuel emitted

/-! ## The obligation each operation carries -/

/-- Each arm's lowering refines it, arm for arm and tag for tag. -/
def EverywhereCases (program : Ir.Program) (target : Target.Program) (runtime : Runtime)
    (fuel : Nat) : List (String × Ir.Expr) → List (String × Target.Expr) → Prop
  | [], emitted => emitted = []
  | (tag, arm) :: rest, emitted =>
      ∃ (emittedArm : Target.Expr) (restEmitted : List (String × Target.Expr)),
        emitted = (tag, emittedArm) :: restEmitted ∧
          Everywhere program target runtime fuel arm emittedArm ∧
          EverywhereCases program target runtime fuel rest restEmitted

/--
Each arm of a statement-form match refines it, arm for arm. The arm at each position decides the
constructor the declaration carries at that position and names exactly that constructor's payload
fields, which is the positional correspondence `emitMatchStatements` reads out of the declaration and
`Compile.decidesInOrder` refuses a document without.
-/
def EverywhereArms (program : Ir.Program) (target : Target.Program) (runtime : Runtime)
    (fuel : Nat) : List Ir.Constructor → List (String × Ir.Expr) →
      List (String × List String × Target.Body) → Prop
  | constructors, [], emitted => constructors = [] ∧ emitted = []
  | constructors, (tag, arm) :: rest, emitted =>
      ∃ (constructor : Ir.Constructor) (remaining : List Ir.Constructor)
        (emittedArm : Target.Body) (restEmitted : List (String × List String × Target.Body)),
        constructors = constructor :: remaining ∧ tag = constructor.name ∧
          emitted = (constructor.name, constructor.fields.map Ir.Field.name, emittedArm)
            :: restEmitted ∧
          EverywhereBody program target runtime fuel arm emittedArm ∧
          EverywhereArms program target runtime fuel remaining rest restEmitted

/--
What one admitted IR operation owes: given that each of its subexpressions' lowerings refines it from
every aligned configuration, its own lowering refines it. The lowering named in each clause is
exactly the one `src/lean-to-typescript/emitter.ts` builds for that operation.
-/
def Op.Preserves (runtime : Runtime) : Ir.Op → Prop
  | .varRef => ∀ (program : Ir.Program) (target : Target.Program) (fuel index : Nat),
      Everywhere program target runtime fuel (.varRef index) (.binding index)
  | .boolLit => ∀ (program : Ir.Program) (target : Target.Program) (fuel : Nat) (value : Bool),
      Everywhere program target runtime fuel (.boolLit value) (.boolLit value)
  | .natLit => ∀ (program : Ir.Program) (target : Target.Program) (fuel value : Nat),
      Everywhere program target runtime fuel (.natLit value) (.bigintLit value)
  | .stringLit => ∀ (program : Ir.Program) (target : Target.Program) (fuel : Nat) (value : String),
      Everywhere program target runtime fuel (.stringLit value) (.stringLit value)
  | .letBind => ∀ (program : Ir.Program) (target : Target.Program) (fuel : Nat) (name : String)
      (value body : Ir.Expr) (emittedValue : Target.Expr) (emittedBody : Target.Body),
      Everywhere program target runtime fuel value emittedValue →
      EverywhereBody program target runtime fuel body emittedBody →
      EverywhereBody program target runtime fuel (.letBind name value body)
        (.constBind name emittedValue emittedBody)
  | .fieldGet => ∀ (program : Ir.Program) (target : Target.Program) (fuel : Nat)
      (subject : Ir.Expr) (field : String) (emittedSubject : Target.Expr),
      Everywhere program target runtime fuel subject emittedSubject →
      Everywhere program target runtime fuel (.fieldGet subject field) (.member emittedSubject field)
  | .ifThenElse => (∀ (program : Ir.Program) (target : Target.Program) (fuel : Nat)
      (condition consequent alternate : Ir.Expr)
      (emittedCondition emittedConsequent emittedAlternate : Target.Expr),
      Everywhere program target runtime fuel condition emittedCondition →
      Everywhere program target runtime fuel consequent emittedConsequent →
      Everywhere program target runtime fuel alternate emittedAlternate →
      Everywhere program target runtime fuel (.ifThenElse condition consequent alternate)
        (.conditional emittedCondition emittedConsequent emittedAlternate)) ∧
    (∀ (program : Ir.Program) (target : Target.Program) (fuel : Nat)
      (condition consequent alternate : Ir.Expr) (emittedCondition : Target.Expr)
      (emittedConsequent emittedAlternate : Target.Body),
      Everywhere program target runtime fuel condition emittedCondition →
      EverywhereBody program target runtime fuel consequent emittedConsequent →
      EverywhereBody program target runtime fuel alternate emittedAlternate →
      EverywhereBody program target runtime fuel (.ifThenElse condition consequent alternate)
        (.ifThen emittedCondition emittedConsequent emittedAlternate))
  | .operation => ∀ (program : Ir.Program) (target : Target.Program) (fuel : Nat),
      (∀ (typeArguments : List Ir.Ty) (left right : Ir.Expr)
          (emittedLeft emittedRight : Target.Expr),
          Everywhere program target runtime fuel left emittedLeft →
          Everywhere program target runtime fuel right emittedRight →
          Everywhere program target runtime fuel (.operation .boolAnd typeArguments [left, right])
            (.logicalAnd emittedLeft emittedRight)) ∧
        (∀ (typeArguments : List Ir.Ty) (left right : Ir.Expr)
          (emittedLeft emittedRight : Target.Expr),
          Everywhere program target runtime fuel left emittedLeft →
          Everywhere program target runtime fuel right emittedRight →
          Everywhere program target runtime fuel (.operation .boolOr typeArguments [left, right])
            (.logicalOr emittedLeft emittedRight)) ∧
        (∀ (typeArguments : List Ir.Ty) (operand : Ir.Expr) (emittedOperand : Target.Expr),
          Everywhere program target runtime fuel operand emittedOperand →
          Everywhere program target runtime fuel (.operation .boolNot typeArguments [operand])
            (.logicalNot emittedOperand)) ∧
        (∀ (typeArguments : List Ir.Ty) (left right : Ir.Expr)
          (emittedLeft emittedRight : Target.Expr),
          Everywhere program target runtime fuel left emittedLeft →
          Everywhere program target runtime fuel right emittedRight →
          Everywhere program target runtime fuel
              (.operation .boolEquals typeArguments [left, right])
              (.strictEquals emittedLeft emittedRight) ∧
            Everywhere program target runtime fuel
              (.operation .boolEquals typeArguments [left, .boolLit true]) emittedLeft ∧
            Everywhere program target runtime fuel
              (.operation .boolEquals typeArguments [.boolLit true, right]) emittedRight) ∧
        (∀ (opcode : Ir.Opcode) (typeArguments : List Ir.Ty) (arguments : List Ir.Expr)
          (emittedArguments : List Target.Expr),
          (∀ form, opcode.operator? = some form → arguments.length ≠ form.operands) →
          opcode.Preserves runtime →
          ListsFit program →
          EverywhereList program target runtime fuel arguments emittedArguments →
          (∀ smaller, smaller + 1 = fuel → ∀ (inner : Ir.Expr) (emitted : Target.Body),
            Compile.body program inner = .ok emitted →
            EverywhereBody program target runtime smaller inner emitted) →
          Everywhere program target runtime fuel (.operation opcode typeArguments arguments)
            (.operation opcode emittedArguments))
  | .variant => ∀ (program : Ir.Program) (target : Target.Program) (fuel : Nat),
      (∀ (type : Ir.Ty) (name : String) (constructors : List Ir.Constructor)
          (constructor : Ir.Constructor) (arguments : List Ir.Expr)
          (emittedArguments : List Target.Expr),
          type.element? = none →
          program.constructorsOf type = some constructors →
          Ir.constructor? constructors name = some constructor →
          (∀ field ∈ constructor.fields, Ir.ValidKey field.name ∧ field.name ≠ "kind") →
          (constructor.fields.map Ir.Field.name).Nodup →
          constructor.fields.length = arguments.length →
          arguments.length = emittedArguments.length →
          EverywhereList program target runtime fuel arguments emittedArguments →
          (Ir.allNullary constructors = true →
              Everywhere program target runtime fuel (.variant type name arguments)
                (.stringLit name)) ∧
            (Ir.allNullary constructors = false →
              Everywhere program target runtime fuel (.variant type name arguments)
                (.objectLiteral (("kind", .stringLit name) ::
                  (constructor.fields.map Ir.Field.name).zip emittedArguments)))) ∧
        (∀ (element : Ir.Ty),
          Everywhere program target runtime fuel (.variant (.list element) "nil" [])
            .arrayEmpty) ∧
        (∀ (element : Ir.Ty) (head tail : Ir.Expr) (emittedHead emittedTail : Target.Expr),
          ListsFit program →
          Everywhere program target runtime fuel head emittedHead →
          Everywhere program target runtime fuel tail emittedTail →
          Everywhere program target runtime fuel (.variant (.list element) "cons" [head, tail])
            (.arrayCons emittedHead emittedTail))
  | .record => ∀ (program : Ir.Program) (target : Target.Program) (fuel : Nat) (type : Ir.Ty)
      (fields : List (String × Ir.Expr)) (emittedFields : List (String × Target.Expr)),
      (∀ field ∈ fields, Ir.ValidKey field.1) →
      (fields.map Prod.fst).Nodup →
      EverywhereFields program target runtime fuel fields emittedFields →
      Everywhere program target runtime fuel (.record type fields) (.objectLiteral emittedFields)
  | .matchOn => (∀ (program : Ir.Program) (target : Target.Program) (fuel : Nat) (type : Ir.Ty)
      (scrutinee : Ir.Expr) (cases : List (String × Ir.Expr)) (emittedScrutinee : Target.Expr)
      (emittedCases : List (String × Target.Expr)) (chain : Target.Expr)
      (constructors : List Ir.Constructor),
      program.constructorsOf type = some constructors →
      Ir.allNullary constructors = true →
      Readable program target runtime fuel scrutinee emittedScrutinee →
      EverywhereCases program target runtime fuel cases emittedCases →
      Compile.tagChain emittedScrutinee emittedCases = some chain →
      Everywhere program target runtime fuel (.matchOn type scrutinee cases) chain) ∧
    (∀ (program : Ir.Program) (target : Target.Program) (fuel : Nat) (type : Ir.Ty)
      (scrutinee : Ir.Expr) (cases : List (String × Ir.Expr)) (emittedScrutinee : Target.Expr)
      (emittedArms : List (String × List String × Target.Body))
      (discriminator : Target.Discriminator) (constructors : List Ir.Constructor),
      program.constructorsOf type = some constructors →
      type.element? = none →
      (Ir.allNullary constructors = true → discriminator = .tag) →
      (Ir.allNullary constructors = false → discriminator = .tagged) →
      (∀ constructor ∈ constructors, (∀ field ∈ constructor.fields, field.name ≠ "kind") ∧
        (constructor.fields.map Ir.Field.name).Nodup) →
      Everywhere program target runtime fuel scrutinee emittedScrutinee →
      EverywhereArms program target runtime fuel constructors cases emittedArms →
      EverywhereBody program target runtime fuel (.matchOn type scrutinee cases)
        (.branch emittedScrutinee discriminator emittedArms))
  | .lambda => ∀ (program : Ir.Program) (target : Target.Program) (fuel : Nat)
      (parameters : List Ir.Field) (body : Ir.Expr) (emittedBody : Target.Body),
      Compile.body program body = .ok emittedBody →
      EverywhereBody program target runtime fuel body emittedBody →
      Everywhere program target runtime fuel (.lambda parameters body)
        (.arrow ⟨parameters, body⟩ emittedBody)
  | .apply =>
      (∀ (program : Ir.Program) (target : Target.Program) (fuel index : Nat)
        (arguments : List Ir.Expr) (emittedArguments : List Target.Expr),
        EverywhereList program target runtime fuel arguments emittedArguments →
        (∀ smaller, smaller + 1 = fuel → ∀ body emittedBody,
          Compile.body program body = .ok emittedBody →
          EverywhereBody program target runtime smaller body emittedBody) →
        Everywhere program target runtime fuel (.apply (.varRef index) arguments)
          (.callValue (.binding index) emittedArguments)) ∧
      (∀ (program : Ir.Program) (target : Target.Program) (fuel : Nat)
        (subject : Ir.Expr) (field : String) (emittedSubject : Target.Expr)
        (arguments : List Ir.Expr) (emittedArguments : List Target.Expr),
        Everywhere program target runtime fuel subject emittedSubject →
        EverywhereList program target runtime fuel arguments emittedArguments →
        (∀ smaller, smaller + 1 = fuel → ∀ body emittedBody,
          Compile.body program body = .ok emittedBody →
          EverywhereBody program target runtime smaller body emittedBody) →
        Everywhere program target runtime fuel (.apply (.fieldGet subject field) arguments)
          (.callValue (.member emittedSubject field) emittedArguments))
  | .call => ∀ (program : Ir.Program) (target : Target.Program) (fuel : Nat) (function : String)
      (typeArguments : List Ir.Ty) (arguments : List Ir.Expr)
      (emittedArguments : List Target.Expr),
      Lowered program target →
      EverywhereList program target runtime fuel arguments emittedArguments →
      (∀ smaller, smaller + 1 = fuel → EveryFunction program target runtime smaller) →
      Everywhere program target runtime fuel (.call function typeArguments arguments)
        (.callFunction function emittedArguments)

/-! ## The literal and reference theorems -/

/-- A binding read resolves positionally on both sides, and reads nothing else. -/
theorem varRef {runtime : Runtime} : Op.Preserves runtime .varRef := by
  intro program target fuel index sourceScope targetScope trace state aligned
  simp only [Source.eval, Target.eval]
  cases sourceLookup : Source.lookup sourceScope index with
  | none => exact refines_fault
  | some value =>
      obtain ⟨image, targetLookup, related⟩ :=
        lookup_represents sourceScope targetScope index aligned.scope value sourceLookup
      rw [targetLookup]
      exact refines_value (Target.State.Extension.refl state aligned.heapValid)
        aligned.closuresValid related aligned.trace

/-- A `Bool` literal is a JavaScript boolean literal. -/
theorem boolLit {runtime : Runtime} : Op.Preserves runtime .boolLit := by
  intro program target fuel value sourceScope targetScope trace state aligned
  simp only [Source.eval, Target.eval]
  refine refines_value (Target.State.Extension.refl state aligned.heapValid) aligned.closuresValid
    ?_ aligned.trace
  unfold Relation.Represents
  rfl

/-- A `Nat` literal is a bigint literal, which is exact at every magnitude. -/
theorem natLit {runtime : Runtime} : Op.Preserves runtime .natLit := by
  intro program target fuel value sourceScope targetScope trace state aligned
  simp only [Source.eval, Target.eval]
  refine refines_value (Target.State.Extension.refl state aligned.heapValid) aligned.closuresValid
    ?_ aligned.trace
  unfold Relation.Represents
  rfl

/-- A `String` literal is a JavaScript string literal, in UTF-16 code units. -/
theorem stringLit {runtime : Runtime} : Op.Preserves runtime .stringLit := by
  intro program target fuel value sourceScope targetScope trace state aligned
  simp only [Source.eval, Target.eval]
  refine refines_value (Target.State.Extension.refl state aligned.heapValid) aligned.closuresValid
    ?_ aligned.trace
  unfold Relation.Represents
  rfl

/-- A refinement measured from a later state holds from an earlier state it extends. -/
theorem refines_widen {program : Ir.Program} {start middle : Target.State} {source : Source.Outcome}
    {result : Target.Result} (extension : Target.State.Extension start middle)
    (refines : Relation.Refines program middle source result) :
    Relation.Refines program start source result := by
  cases source with
  | fault fault trace => exact refines_fault
  | value value trace =>
      obtain ⟨image, state, resultEq, inner, closuresValid, related, traceRefines⟩ :=
        refines_value_inv refines
      subst resultEq
      exact refines_value (extension.trans inner) closuresValid related traceRefines
  | exhausted trace =>
      obtain ⟨state, resultEq, inner, closuresValid, traceRefines⟩ := refines_exhausted_inv refines
      subst resultEq
      exact refines_exhausted (extension.trans inner) closuresValid traceRefines

/--
A statement-form `if` selects by truthiness, exactly as the conditional expression does, and the
branch it selects runs the statements the emitter placed under it. The consequent returns, so the
alternate is the narrowed remainder and neither branch can fall into the other.
-/
theorem ifThenBody {runtime : Runtime} : ∀ (program : Ir.Program) (target : Target.Program)
    (fuel : Nat) (condition consequent alternate : Ir.Expr) (emittedCondition : Target.Expr)
    (emittedConsequent emittedAlternate : Target.Body),
    Everywhere program target runtime fuel condition emittedCondition →
    EverywhereBody program target runtime fuel consequent emittedConsequent →
    EverywhereBody program target runtime fuel alternate emittedAlternate →
    EverywhereBody program target runtime fuel (.ifThenElse condition consequent alternate)
      (.ifThen emittedCondition emittedConsequent emittedAlternate) := by
  intro program target fuel condition consequent alternate emittedCondition emittedConsequent
    emittedAlternate conditionStep consequentStep alternateStep
    sourceScope targetScope trace state aligned
  simp only [Source.eval, Target.evalBody]
  cases conditionRun : Source.eval program fuel sourceScope trace condition with
  | fault fault next => exact refines_fault
  | exhausted next =>
      obtain ⟨targetState, targetRun, extension, closuresValid, traceRefines⟩ :=
        refines_exhausted_inv
          (conditionRun ▸ conditionStep sourceScope targetScope trace state aligned)
      rw [targetRun]
      exact refines_exhausted extension closuresValid traceRefines
  | value produced next =>
      obtain ⟨image, targetState, targetRun, extension, closuresValid, related, traceRefines⟩ :=
        refines_value_inv
          (conditionRun ▸ conditionStep sourceScope targetScope trace state aligned)
      rw [targetRun]
      cases produced with
      | boolean flag =>
          unfold Relation.Represents at related
          subst related
          have nextAligned := aligned.step extension closuresValid traceRefines
          cases flag with
          | true =>
              simp only [Value.toBoolean, Primitive.toBoolean, if_true]
              exact refines_widen extension
                (consequentStep sourceScope targetScope next targetState nextAligned)
          | false =>
              simp only [Value.toBoolean, Primitive.toBoolean]
              exact refines_widen extension
                (alternateStep sourceScope targetScope next targetState nextAligned)
      | nat _ => exact refines_fault
      | int _ => exact refines_fault
      | char _ => exact refines_fault
      | string _ => exact refines_fault
      | record _ _ => exact refines_fault
      | array _ _ => exact refines_fault
      | variant _ _ _ => exact refines_fault
      | closure _ _ _ => exact refines_fault

/-- `? :` selects by truthiness, and a represented `Bool` is truthy exactly when it is `true`. -/
theorem ifThenElse {runtime : Runtime} : Op.Preserves runtime .ifThenElse := by
  refine ⟨?_, ifThenBody⟩
  intro program target fuel condition consequent alternate emittedCondition emittedConsequent
    emittedAlternate conditionStep consequentStep alternateStep
    sourceScope targetScope trace state aligned
  simp only [Source.eval, Target.eval]
  cases conditionRun : Source.eval program fuel sourceScope trace condition with
  | fault fault next => exact refines_fault
  | exhausted next =>
      obtain ⟨targetState, targetRun, extension, closuresValid, traceRefines⟩ :=
        refines_exhausted_inv
          (conditionRun ▸ conditionStep sourceScope targetScope trace state aligned)
      rw [targetRun]
      exact refines_exhausted extension closuresValid traceRefines
  | value produced next =>
      obtain ⟨image, targetState, targetRun, extension, closuresValid, related, traceRefines⟩ :=
        refines_value_inv
          (conditionRun ▸ conditionStep sourceScope targetScope trace state aligned)
      rw [targetRun]
      cases produced with
      | boolean flag =>
          unfold Relation.Represents at related
          subst related
          have nextAligned := aligned.step extension closuresValid traceRefines
          cases flag with
          | true =>
              simp only [Value.toBoolean, Primitive.toBoolean, if_true]
              exact refines_widen extension
                (consequentStep sourceScope targetScope next targetState nextAligned)
          | false =>
              simp only [Value.toBoolean, Primitive.toBoolean]
              exact refines_widen extension
                (alternateStep sourceScope targetScope next targetState nextAligned)
      | nat _ => exact refines_fault
      | int _ => exact refines_fault
      | char _ => exact refines_fault
      | string _ => exact refines_fault
      | record _ _ => exact refines_fault
      | array _ _ => exact refines_fault
      | variant _ _ _ => exact refines_fault
      | closure _ _ _ => exact refines_fault

/-- A declared field read is an own-property read of the object the record is represented by. -/
theorem fieldGet {runtime : Runtime} : Op.Preserves runtime .fieldGet := by
  intro program target fuel subject field emittedSubject inner
    sourceScope targetScope trace state aligned
  simp only [Source.eval, Target.eval]
  cases sourceRun : Source.eval program fuel sourceScope trace subject with
  | fault fault next => exact refines_fault
  | exhausted next =>
      obtain ⟨targetState, targetRun, extension, closuresValid, traceRefines⟩ :=
        refines_exhausted_inv (sourceRun ▸ inner sourceScope targetScope trace state aligned)
      rw [targetRun]
      exact refines_exhausted extension closuresValid traceRefines
  | value produced next =>
      obtain ⟨image, targetState, targetRun, extension, closuresValid, related, traceRefines⟩ :=
        refines_value_inv (sourceRun ▸ inner sourceScope targetScope trace state aligned)
      rw [targetRun]
      cases produced with
      | record type fields =>
          dsimp only
          unfold Relation.Represents at related
          obtain ⟨ref, entries, imageEq, fieldsRelated, shape⟩ := related
          subst imageEq
          cases lookup : Source.fieldValue? fields field with
          | none => exact refines_fault
          | some value =>
              obtain ⟨fieldImage, entryFound, fieldRelated⟩ :=
                fields_lookup fields entries fieldsRelated field value lookup
              rw [readMember_of_shape targetState shape field fieldImage entryFound]
              exact refines_value extension closuresValid fieldRelated traceRefines
      | boolean _ => exact refines_fault
      | nat _ => exact refines_fault
      | int _ => exact refines_fault
      | string _ => exact refines_fault
      | char _ => exact refines_fault
      | array _ _ => exact refines_fault
      | variant _ _ _ => exact refines_fault
      | closure _ _ _ => exact refines_fault

/-- A leading `let` becomes a `const` binding, and the body sees it at the same position. -/
theorem letBind {runtime : Runtime} : Op.Preserves runtime .letBind := by
  intro program target fuel name value body emittedValue emittedBody valueStep bodyStep
    sourceScope targetScope trace state aligned
  simp only [Source.eval, Target.evalBody]
  cases sourceRun : Source.eval program fuel sourceScope trace value with
  | fault fault next => exact refines_fault
  | exhausted next =>
      obtain ⟨targetState, targetRun, extension, closuresValid, traceRefines⟩ :=
        refines_exhausted_inv (sourceRun ▸ valueStep sourceScope targetScope trace state aligned)
      rw [targetRun]
      exact refines_exhausted extension closuresValid traceRefines
  | value produced next =>
      obtain ⟨image, targetState, targetRun, extension, closuresValid, related, traceRefines⟩ :=
        refines_value_inv (sourceRun ▸ valueStep sourceScope targetScope trace state aligned)
      rw [targetRun]
      have extended :
          Aligned program (produced :: sourceScope) (image :: targetScope) next targetState := by
        refine ⟨extension.nextWellFormed, closuresValid, ?_, traceRefines⟩
        unfold Relation.RepresentsList
        exact ⟨image, targetScope, rfl, related,
          Relation.RepresentsList.stable extension sourceScope targetScope aligned.scope⟩
      exact refines_widen extension
        (bodyStep (produced :: sourceScope) (image :: targetScope) next targetState extended)

/-! ## Support for the constructing operations -/

/-- A successful field-list run is matched by a successful property-list run, and by nothing else. -/
theorem refinesFields_inv {program : Ir.Program} {start : Target.State}
    {produced : List (String × Source.Value)} {trace : Source.Trace}
    {result : Target.NamedListResult}
    (refines : Relation.RefinesFields program start (.fields produced trace) result) :
    ∃ entries state, result = .ok entries state ∧ Target.State.Extension start state ∧
      state.ClosuresWellFormed ∧ Relation.RepresentsFields program state produced entries ∧
        Relation.RefinesTrace program state trace state.trace := by
  cases result with
  | ok entries state =>
      simp only [Relation.RefinesFields] at refines
      exact ⟨entries, state, rfl, refines.1, refines.2.1, refines.2.2.1, refines.2.2.2⟩
  | thrown error state => simp only [Relation.RefinesFields] at refines
  | fault fault state => simp only [Relation.RefinesFields] at refines
  | exhausted state => simp only [Relation.RefinesFields] at refines

/-- An exhausted field-list run is matched by an exhausted target run. -/
theorem refinesFields_exhausted_inv {program : Ir.Program} {start : Target.State}
    {trace : Source.Trace} {result : Target.NamedListResult}
    (refines : Relation.RefinesFields program start (.exhausted trace) result) :
    ∃ state, result = .exhausted state ∧ Target.State.Extension start state ∧
      state.ClosuresWellFormed ∧ Relation.RefinesTrace program state trace state.trace := by
  cases result with
  | ok entries state => simp only [Relation.RefinesFields] at refines
  | thrown error state => simp only [Relation.RefinesFields] at refines
  | fault fault state => simp only [Relation.RefinesFields] at refines
  | exhausted state => exact ⟨state, rfl, refines.1, refines.2.1, refines.2.2⟩

/-- A successful argument-list run is matched by a successful target list run. -/
theorem refinesList_inv {program : Ir.Program} {start : Target.State} {produced : List Source.Value}
    {trace : Source.Trace} {result : Target.ListResult}
    (refines : Relation.RefinesList program start (.values produced trace) result) :
    ∃ targets state, result = .ok targets state ∧ Target.State.Extension start state ∧
      state.ClosuresWellFormed ∧ Relation.RepresentsList program state produced targets ∧
        Relation.RefinesTrace program state trace state.trace := by
  cases result with
  | ok targets state =>
      simp only [Relation.RefinesList] at refines
      exact ⟨targets, state, rfl, refines.1, refines.2.1, refines.2.2.1, refines.2.2.2⟩
  | thrown error state => simp only [Relation.RefinesList] at refines
  | fault fault state => simp only [Relation.RefinesList] at refines
  | exhausted state => simp only [Relation.RefinesList] at refines

/-- An exhausted argument-list run is matched by an exhausted target run. -/
theorem refinesList_exhausted_inv {program : Ir.Program} {start : Target.State}
    {trace : Source.Trace} {result : Target.ListResult}
    (refines : Relation.RefinesList program start (.exhausted trace) result) :
    ∃ state, result = .exhausted state ∧ Target.State.Extension start state ∧
      state.ClosuresWellFormed ∧ Relation.RefinesTrace program state trace state.trace := by
  cases result with
  | ok targets state => simp only [Relation.RefinesList] at refines
  | thrown error state => simp only [Relation.RefinesList] at refines
  | fault fault state => simp only [Relation.RefinesList] at refines
  | exhausted state => exact ⟨state, rfl, refines.1, refines.2.1, refines.2.2⟩

/-- Builds a successful list refinement. -/
theorem refinesList_values {program : Ir.Program} {start : Target.State}
    {produced : List Source.Value} {trace : Source.Trace} {targets : List Value}
    {state : Target.State} (extension : Target.State.Extension start state)
    (closuresValid : state.ClosuresWellFormed)
    (related : Relation.RepresentsList program state produced targets)
    (traceRefines : Relation.RefinesTrace program state trace state.trace) :
    Relation.RefinesList program start (.values produced trace) (.ok targets state) := by
  simp only [Relation.RefinesList]
  exact ⟨extension, closuresValid, related, traceRefines⟩

/-- Builds an exhausted list refinement. -/
theorem refinesList_exhausted {program : Ir.Program} {start : Target.State} {trace : Source.Trace}
    {state : Target.State} (extension : Target.State.Extension start state)
    (closuresValid : state.ClosuresWellFormed)
    (traceRefines : Relation.RefinesTrace program state trace state.trace) :
    Relation.RefinesList program start (.exhausted trace) (.exhausted state) := by
  simp only [Relation.RefinesList]
  exact ⟨extension, closuresValid, traceRefines⟩

/-- A source list run that faults claims nothing of the target. -/
theorem refinesList_fault {program : Ir.Program} {start : Target.State} {fault : Source.Fault}
    {trace : Source.Trace} {result : Target.ListResult} :
    Relation.RefinesList program start (.fault fault trace) result := by
  simp only [Relation.RefinesList]

/-- Field evaluation keeps the declared names, in declaration order. -/
theorem evalFields_names {program : Ir.Program} {fuel : Nat} {sourceScope : List Source.Value} :
    ∀ (fields : List (String × Ir.Expr)) (trace : Source.Trace)
      (produced : List (String × Source.Value)) (next : Source.Trace),
      Source.evalFields program fuel sourceScope trace fields = .fields produced next →
      produced.map Prod.fst = fields.map Prod.fst
  | [], trace, produced, next, run => by
      simp only [Source.evalFields] at run
      injection run with producedEq _
      subst producedEq
      rfl
  | (name, expression) :: rest, trace, produced, next, run => by
      simp only [Source.evalFields] at run
      cases headRun : Source.eval program fuel sourceScope trace expression with
      | fault fault middle => rw [headRun] at run; simp at run
      | exhausted middle => rw [headRun] at run; simp at run
      | value value middle =>
          rw [headRun] at run
          dsimp only at run
          cases tailRun : Source.evalFields program fuel sourceScope middle rest with
          | fault fault last => rw [tailRun] at run; simp at run
          | exhausted last => rw [tailRun] at run; simp at run
          | fields values last =>
              rw [tailRun] at run
              injection run with producedEq _
              subst producedEq
              simp only [List.map_cons]
              rw [evalFields_names rest middle values last tailRun]

/-- Field representation keeps the names, so the emitted object's own keys are the declared ones. -/
theorem representsFields_names {program : Ir.Program} {state : Target.State} :
    ∀ (fields : List (String × Source.Value)) (entries : List (String × Value)),
      Relation.RepresentsFields program state fields entries →
      entries.map Prod.fst = fields.map Prod.fst
  | [], entries, related => by
      unfold Relation.RepresentsFields at related
      subst related
      rfl
  | (name, value) :: rest, entries, related => by
      unfold Relation.RepresentsFields at related
      obtain ⟨target, restEntries, entriesEq, _, tailRelated⟩ := related
      subst entriesEq
      simp only [List.map_cons]
      rw [representsFields_names rest restEntries tailRelated]

/-- Every value a represented field carries is a valid heap value. -/
theorem representsFields_valuesValid {program : Ir.Program} {state : Target.State} :
    ∀ (fields : List (String × Source.Value)) (entries : List (String × Value)),
      Relation.RepresentsFields program state fields entries →
      ∀ entry ∈ entries, state.heap.valueValid entry.2 = true
  | [], entries, related, entry, member => by
      unfold Relation.RepresentsFields at related
      subst related
      exact absurd member (by simp)
  | (name, value) :: rest, entries, related, entry, member => by
      unfold Relation.RepresentsFields at related
      obtain ⟨target, restEntries, entriesEq, headRelated, tailRelated⟩ := related
      subst entriesEq
      rcases List.mem_cons.mp member with rfl | tail
      · exact valueValid_of_represents value target headRelated
      · exact representsFields_valuesValid rest restEntries tailRelated entry tail

/-- A record value is the object literal the emitter builds for it: own keys exactly the declared
field keys, in declaration order, each a standard data property. -/
theorem record {runtime : Runtime} : Op.Preserves runtime .record := by
  intro program target fuel type fields emittedFields validKeys distinct fieldsStep
    sourceScope targetScope trace state aligned
  simp only [Source.eval, Target.eval]
  cases sourceRun : Source.evalFields program fuel sourceScope trace fields with
  | fault fault next => exact refines_fault
  | exhausted next =>
      obtain ⟨targetState, targetRun, extension, closuresValid, traceRefines⟩ :=
        refinesFields_exhausted_inv
          (sourceRun ▸ fieldsStep sourceScope targetScope trace state aligned)
      rw [targetRun]
      exact refines_exhausted extension closuresValid traceRefines
  | fields produced next =>
      obtain ⟨entries, targetState, targetRun, extension, closuresValid, fieldsRelated,
        traceRefines⟩ :=
        refinesFields_inv (sourceRun ▸ fieldsStep sourceScope targetScope trace state aligned)
      rw [targetRun]
      dsimp only
      have names : entries.map Prod.fst = fields.map Prod.fst := by
        rw [representsFields_names produced entries fieldsRelated,
          evalFields_names fields trace produced next sourceRun]
      obtain ⟨ref, final, allocated, traceEq, _, finalExtension, finalClosuresValid, _, shape⟩ :=
        Allocation.allocateLiteral_shape targetState entries extension.nextWellFormed closuresValid
          (by
            intro entry member
            have nameMember : entry.1 ∈ fields.map Prod.fst := by
              rw [← names]
              exact List.mem_map_of_mem member
            obtain ⟨field, fieldMember, fieldEq⟩ := List.mem_map.mp nameMember
            exact fieldEq ▸ validKeys field fieldMember)
          (by rw [names]; exact distinct)
          (representsFields_valuesValid produced entries fieldsRelated)
      rw [allocated]
      refine refines_value (extension.trans finalExtension) finalClosuresValid ?_ ?_
      · unfold Relation.Represents
        exact ⟨ref, entries, rfl,
          Relation.RepresentsFields.stable finalExtension produced entries fieldsRelated, shape⟩
      · rw [traceEq]
        exact Relation.RefinesTrace.stable finalExtension next targetState.trace traceRefines

/-- Representation of a list is length-preserving, so a call that satisfies the source arity
satisfies the emitted one. -/
theorem representsList_length {program : Ir.Program} {state : Target.State} :
    ∀ (values : List Source.Value) (targets : List Value),
      Relation.RepresentsList program state values targets → values.length = targets.length
  | [], targets, related => by
      unfold Relation.RepresentsList at related
      subst related
      rfl
  | value :: rest, targets, related => by
      unfold Relation.RepresentsList at related
      obtain ⟨image, restTargets, targetsEq, _, tailRelated⟩ := related
      subst targetsEq
      simp only [List.length_cons]
      rw [representsList_length rest restTargets tailRelated]

/-- Representation of a list decides emptiness the same way on both sides. -/
theorem representsList_isEmpty {program : Ir.Program} {state : Target.State} :
    ∀ (values : List Source.Value) (targets : List Value),
      Relation.RepresentsList program state values targets → values.isEmpty = targets.isEmpty
  | [], targets, related => by
      unfold Relation.RepresentsList at related
      subst related
      rfl
  | value :: rest, targets, related => by
      unfold Relation.RepresentsList at related
      obtain ⟨image, restTargets, targetsEq, _, _⟩ := related
      subst targetsEq
      rfl

/-- Every value a represented list carries is a valid heap value. -/
theorem representsList_valuesValid {program : Ir.Program} {state : Target.State} :
    ∀ (values : List Source.Value) (targets : List Value),
      Relation.RepresentsList program state values targets →
      ∀ image ∈ targets, state.heap.valueValid image = true
  | [], targets, related, image, member => by
      unfold Relation.RepresentsList at related
      subst related
      exact absurd member (by simp)
  | value :: rest, targets, related, image, member => by
      unfold Relation.RepresentsList at related
      obtain ⟨head, restTargets, targetsEq, headRelated, tailRelated⟩ := related
      subst targetsEq
      rcases List.mem_cons.mp member with rfl | tail
      · exact valueValid_of_represents value _ headRelated
      · exact representsList_valuesValid rest restTargets tailRelated image tail

/--
A call evaluates its arguments left to right, records one declared-function entry, spends one unit
of fuel, and enters the lowered body with the arguments bound in reverse.
-/
theorem call {runtime : Runtime} : Op.Preserves runtime .call := by
  intro program target fuel function typeArguments arguments emittedArguments lowered argumentsStep
    functions sourceScope targetScope trace state aligned
  simp only [Source.eval, Target.eval]
  cases sourceRun : Source.evalList program fuel sourceScope trace arguments with
  | fault fault next => exact refines_fault
  | exhausted next =>
      obtain ⟨targetState, targetRun, extension, closuresValid, traceRefines⟩ :=
        refinesList_exhausted_inv
          (sourceRun ▸ argumentsStep sourceScope targetScope trace state aligned)
      rw [targetRun]
      exact refines_exhausted extension closuresValid traceRefines
  | values produced next =>
      obtain ⟨targets, targetState, targetRun, extension, closuresValid, listRelated,
        traceRefines⟩ :=
        refinesList_inv (sourceRun ▸ argumentsStep sourceScope targetScope trace state aligned)
      rw [targetRun]
      dsimp only
      simp only [Source.enter, Target.enter]
      cases declared : program.function? function with
      | none => exact refines_fault
      | some declaration =>
          obtain ⟨parameters, result, recursion, body⟩ := declaration
          obtain ⟨emitted, emittedFound, arity⟩ :=
            lowered function parameters result recursion body declared
          rw [emittedFound]
          dsimp only
          by_cases matched : parameters.length = produced.length
          · rw [if_pos matched]
            have lengths : emitted.parameters = targets.length := by
              rw [arity, matched, representsList_length produced targets listRelated]
            rw [bindArguments_exact targets emitted.parameters lengths]
            cases fuel with
            | zero => exact refines_exhausted extension closuresValid traceRefines
            | succ remaining =>
                dsimp only
                have recorded := Target.State.record_extension targetState
                  (.function function targets) extension.nextWellFormed
                refine refines_widen extension ?_
                refine refines_widen recorded ?_
                refine functions remaining rfl function parameters result recursion body emitted
                  declared emittedFound produced.reverse targets.reverse
                  (next ++ [.function function produced])
                  (targetState.record (.function function targets)) ?_
                refine ⟨extension.nextWellFormed, closuresValid, ?_, ?_⟩
                · exact Relation.RepresentsList.stable recorded produced.reverse targets.reverse
                    (represents_reverse produced targets listRelated)
                · exact refinesTrace_append next targetState.trace
                    (.function function produced) (.function function targets)
                    (Relation.RefinesTrace.stable recorded next targetState.trace traceRefines)
                    ⟨rfl, Relation.RepresentsList.stable recorded produced targets listRelated⟩
          · rw [if_neg matched]
            exact refines_fault

/--
An inline lambda allocates one heap object carrying exactly its captured binders. The object owns
the exact inline code label and compiled body in its callable payload. Allocation is the whole
effect: no entry is recorded and no fuel is spent.
-/
theorem lambda {runtime : Runtime} : Op.Preserves runtime .lambda := by
  intro program target fuel parameters body emittedBody compiled _
    sourceScope targetScope trace state aligned
  simp only [Source.eval, Target.eval]
  obtain ⟨ref, final, allocated, traceEq, extension, finalClosuresValid, closureFound, shape⟩ :=
    Closure.allocate_shape state ⟨parameters, body⟩ emittedBody targetScope aligned.heapValid
      aligned.closuresValid (representsList_valuesValid sourceScope targetScope aligned.scope)
  rw [allocated]
  refine refines_value extension finalClosuresValid ?_ ?_
  · unfold Relation.Represents
    exact ⟨ref, ⟨⟨parameters, body⟩, emittedBody, targetScope⟩, rfl, closureFound, rfl, compiled,
      Relation.RepresentsList.stable extension sourceScope targetScope aligned.scope, shape⟩
  · rw [traceEq]
    exact Relation.RefinesTrace.stable extension trace state.trace aligned.trace

/-! ## Applying an inline arrow

The one correspondence the `apply` operation and the six higher-order opcodes share: a represented
arrow, invoked on representing arguments, enters the body its own callable payload holds.
-/

/--
Applying a represented arrow refines invoking the function object it is represented by. The
payload's body is authoritative, the captured own properties read back exactly, one application
event carrying the exact lambda code is recorded, and one unit of fuel is spent.
-/
theorem invoke_refines {program : Ir.Program} {target : Target.Program} {runtime : Runtime}
    {fuel : Nat}
    (bodyAtLower : ∀ smaller, smaller + 1 = fuel → ∀ (inner : Ir.Expr) (emitted : Target.Body),
      Compile.body program inner = .ok emitted →
      EverywhereBody program target runtime smaller inner emitted)
    {captured : List Source.Value} {parameters : List Ir.Field} {body : Ir.Expr} {callee : Value}
    {arguments : List Source.Value} {targets : List Value} {trace : Source.Trace}
    {state : Target.State}
    (heapValid : state.heap.WellFormed) (closuresValid : state.ClosuresWellFormed)
    (calleeRelated : Relation.Represents program state (.closure captured parameters body) callee)
    (related : Relation.RepresentsList program state arguments targets)
    (traceRefines : Relation.RefinesTrace program state trace state.trace) :
    Relation.Refines program state
      (Source.applyClosure program fuel trace captured parameters body arguments)
      (Target.invoke target runtime fuel state callee targets) := by
  unfold Relation.Represents at calleeRelated
  obtain ⟨ref, closure, calleeEq, closureFound, codeEq, compiledBody, capturedRelated, shape⟩ :=
    calleeRelated
  subst calleeEq
  simp only [Target.invoke]
  rw [closureFound]
  dsimp only
  rw [Closure.read_captured_all shape]
  dsimp only
  rw [if_pos rfl]
  unfold Source.applyClosure
  by_cases arity : parameters.length = arguments.length
  · rw [if_pos arity]
    have targetArity : closure.code.parameters.length = targets.length := by
      simp only [codeEq]
      rw [arity, representsList_length arguments targets related]
    rw [bindArguments_exact targets closure.code.parameters.length targetArity]
    cases fuel with
    | zero =>
        exact refines_exhausted (Target.State.Extension.refl state heapValid) closuresValid
          traceRefines
    | succ remaining =>
        dsimp only
        have recorded := Target.State.record_extension state
          (.application closure.code targets) heapValid
        refine refines_widen recorded ?_
        refine bodyAtLower remaining rfl body closure.body compiledBody
          (arguments.reverse ++ captured) (targets.reverse ++ closure.captured)
          (trace ++ [.application ⟨parameters, body⟩ arguments])
          (state.record (.application closure.code targets)) ?_
        refine ⟨heapValid, closuresValid, ?_, ?_⟩
        · exact represents_append arguments.reverse targets.reverse captured closure.captured
            (Relation.RepresentsList.stable recorded arguments.reverse targets.reverse
              (represents_reverse arguments targets related))
            (Relation.RepresentsList.stable recorded captured closure.captured capturedRelated)
        · exact refinesTrace_append trace state.trace
            (.application ⟨parameters, body⟩ arguments)
            (.application closure.code targets)
            (Relation.RefinesTrace.stable recorded trace state.trace traceRefines)
            ⟨codeEq.symm, Relation.RepresentsList.stable recorded arguments targets related⟩
  · rw [if_neg arity]
    exact refines_fault

/--
A dictionary method application evaluates its field projection before it evaluates its arguments.

This is distinct from a named call: the dictionary can be an inline record, a captured value or a
declared instance, and the field read is observable if evaluating its target allocates or faults.
The theorem therefore uses the existing field-refinement row first and only then enters the closure
it read. The source and target preserve that order exactly.
-/
theorem applyField {runtime : Runtime} : ∀ (program : Ir.Program) (target : Target.Program)
    (fuel : Nat) (subject : Ir.Expr) (field : String) (emittedSubject : Target.Expr)
    (arguments : List Ir.Expr) (emittedArguments : List Target.Expr),
    Everywhere program target runtime fuel subject emittedSubject →
    EverywhereList program target runtime fuel arguments emittedArguments →
    (∀ smaller, smaller + 1 = fuel → ∀ body emittedBody,
      Compile.body program body = .ok emittedBody →
      EverywhereBody program target runtime smaller body emittedBody) →
    Everywhere program target runtime fuel (.apply (.fieldGet subject field) arguments)
      (.callValue (.member emittedSubject field) emittedArguments) := by
  intro program target fuel subject field emittedSubject arguments emittedArguments subjectStep
    argumentsStep bodyAtLower sourceScope targetScope trace state aligned
  rw [Source.eval.eq_def program fuel sourceScope trace (.apply (.fieldGet subject field) arguments)]
  rw [Target.eval.eq_def target runtime fuel targetScope state
    (.callValue (.member emittedSubject field) emittedArguments)]
  simp only
  have calleeStep := fieldGet program target fuel subject field emittedSubject subjectStep
  cases calleeRun : Source.eval program fuel sourceScope trace (.fieldGet subject field) with
  | fault fault next => exact refines_fault
  | exhausted next =>
      obtain ⟨targetState, targetRun, extension, closuresValid, traceRefines⟩ :=
        refines_exhausted_inv
          (calleeRun ▸ calleeStep sourceScope targetScope trace state aligned)
      rw [targetRun]
      exact refines_exhausted extension closuresValid traceRefines
  | value callee next =>
      obtain ⟨calleeImage, targetState, targetRun, extension, closuresValid, calleeRelated,
        traceRefines⟩ :=
        refines_value_inv (calleeRun ▸ calleeStep sourceScope targetScope trace state aligned)
      rw [targetRun]
      dsimp only
      cases callee with
      | boolean _ | nat _ | int _ | string _ | char _ | record _ _ | array _ _ | variant _ _ _ =>
          exact refines_fault
      | closure captured parameters body =>
          have nextAligned := aligned.step extension closuresValid traceRefines
          change Relation.Refines program state
            (match Source.evalList program fuel sourceScope next arguments with
            | .values values last => Source.applyClosure program fuel last captured parameters body values
            | .fault fault last => .fault fault last
            | .exhausted last => .exhausted last)
            (match Target.evalList target runtime fuel targetScope targetState emittedArguments with
            | .ok values last => Target.invoke target runtime fuel last calleeImage values
            | .thrown error last => .thrown error last
            | .fault fault last => .fault fault last
            | .exhausted last => .exhausted last)
          cases argumentsRun : Source.evalList program fuel sourceScope next arguments with
          | fault fault last => exact refines_fault
          | exhausted last =>
              obtain ⟨lastState, lastRun, argumentExtension, lastValid, lastTrace⟩ :=
                refinesList_exhausted_inv
                  (argumentsRun ▸ argumentsStep sourceScope targetScope next targetState nextAligned)
              rw [lastRun]
              dsimp only
              exact refines_exhausted (extension.trans argumentExtension) lastValid lastTrace
          | values produced last =>
              obtain ⟨targets, lastState, lastRun, argumentExtension, lastValid, listRelated,
                lastTrace⟩ :=
                refinesList_inv
                  (argumentsRun ▸ argumentsStep sourceScope targetScope next targetState nextAligned)
              rw [lastRun]
              dsimp only
              refine refines_widen (extension.trans argumentExtension) ?_
              exact invoke_refines bodyAtLower argumentExtension.nextWellFormed lastValid
                (Relation.Represents.stable argumentExtension (.closure captured parameters body)
                  calleeImage calleeRelated)
                listRelated lastTrace



theorem apply {runtime : Runtime} : Op.Preserves runtime .apply := by
  refine ⟨?_, applyField⟩
  intro program target fuel index arguments emittedArguments argumentsStep bodyAtLower
    sourceScope targetScope trace state aligned
  simp only [Source.eval, Target.eval]
  cases sourceLookup : Source.lookup sourceScope index with
  | none => exact refines_fault
  | some callee =>
      obtain ⟨calleeImage, targetLookup, calleeRelated⟩ :=
        lookup_represents sourceScope targetScope index aligned.scope callee sourceLookup
      rw [targetLookup]
      cases callee with
      | boolean _ => exact refines_fault
      | nat _ => exact refines_fault
      | int _ => exact refines_fault
      | string _ => exact refines_fault
      | char _ => exact refines_fault
      | record _ _ => exact refines_fault
      | array _ _ => exact refines_fault
      | variant _ _ _ => exact refines_fault
      | closure captured parameters body =>
          dsimp only
          cases argumentsRun : Source.evalList program fuel sourceScope trace arguments with
          | fault fault next => exact refines_fault
          | exhausted next =>
              obtain ⟨targetState, targetRun, extension, closuresValid, traceRefines⟩ :=
                refinesList_exhausted_inv
                  (argumentsRun ▸ argumentsStep sourceScope targetScope trace state aligned)
              rw [targetRun]
              exact refines_exhausted extension closuresValid traceRefines
          | values produced next =>
              obtain ⟨targets, targetState, targetRun, extension, closuresValid, listRelated,
                traceRefines⟩ :=
                refinesList_inv
                  (argumentsRun ▸ argumentsStep sourceScope targetScope trace state aligned)
              rw [targetRun]
              dsimp only
              refine refines_widen extension ?_
              exact invoke_refines bodyAtLower extension.nextWellFormed closuresValid
                (Relation.Represents.stable extension (.closure captured parameters body)
                  calleeImage calleeRelated)
                listRelated traceRefines
/-! ### The six per-element loops

Each higher-order opcode enters its callback once per element, in element order. Every entry spends
one unit of fuel and records one application event on both sides, so the correspondence is the
closure-application correspondence, applied once per element, and never an appeal to a Lean function
standing in for the callback.
-/

/-- `value.map(callback)` enters the callback once per element, in order, keeping the images. -/
theorem mapElements_refines {program : Ir.Program} {target : Target.Program} {runtime : Runtime}
    {fuel : Nat}
    (bodyAtLower : ∀ smaller, smaller + 1 = fuel → ∀ (inner : Ir.Expr) (emitted : Target.Body),
      Compile.body program inner = .ok emitted →
      EverywhereBody program target runtime smaller inner emitted)
    {captured : List Source.Value} {parameters : List Ir.Field} {body : Ir.Expr} {callee : Value} :
    ∀ (elements : List Source.Value) (images : List Value) (trace : Source.Trace)
      (state : Target.State),
      state.heap.WellFormed → state.ClosuresWellFormed →
      Relation.Represents program state (.closure captured parameters body) callee →
      Relation.RepresentsList program state elements images →
      Relation.RefinesTrace program state trace state.trace →
      Relation.RefinesList program state
        (Source.mapElements program fuel trace captured parameters body elements)
        (Target.mapCalls target runtime fuel state callee images)
  | [], images, trace, state, heapValid, closuresValid, _, related, traceRefines => by
      unfold Relation.RepresentsList at related
      subst related
      simp only [Source.mapElements, Target.mapCalls]
      exact refinesList_values (Target.State.Extension.refl state heapValid) closuresValid
        represents_nil traceRefines
  | head :: rest, images, trace, state, heapValid, closuresValid, calleeRelated, related,
      traceRefines => by
      unfold Relation.RepresentsList at related
      obtain ⟨headImage, restImages, imagesEq, headRelated, tailRelated⟩ := related
      subst imagesEq
      simp only [Source.mapElements, Target.mapCalls]
      cases headRun : Source.applyClosure program fuel trace captured parameters body [head] with
      | fault fault next => exact refinesList_fault
      | exhausted next =>
          obtain ⟨targetState, targetRun, extension, nextValid, nextTrace⟩ :=
            refines_exhausted_inv (headRun ▸ invoke_refines bodyAtLower heapValid closuresValid
              calleeRelated (represents_singleton headRelated) traceRefines)
          rw [targetRun]
          exact refinesList_exhausted extension nextValid nextTrace
      | value produced next =>
          obtain ⟨image, targetState, targetRun, extension, nextValid, producedRelated,
            nextTrace⟩ :=
            refines_value_inv (headRun ▸ invoke_refines bodyAtLower heapValid closuresValid
              calleeRelated (represents_singleton headRelated) traceRefines)
          rw [targetRun]
          dsimp only
          have step := mapElements_refines bodyAtLower rest restImages next targetState
            extension.nextWellFormed nextValid
            (Relation.Represents.stable extension _ _ calleeRelated)
            (Relation.RepresentsList.stable extension rest restImages tailRelated) nextTrace
          cases restRun : Source.mapElements program fuel next captured parameters body rest with
          | fault fault last => exact refinesList_fault
          | exhausted last =>
              obtain ⟨lastState, lastRun, lastExtension, lastValid, lastTrace⟩ :=
                refinesList_exhausted_inv (restRun ▸ step)
              rw [lastRun]
              exact refinesList_exhausted (extension.trans lastExtension) lastValid lastTrace
          | values images last =>
              obtain ⟨lastImages, lastState, lastRun, lastExtension, lastValid, listRelated,
                lastTrace⟩ := refinesList_inv (restRun ▸ step)
              rw [lastRun]
              refine refinesList_values (extension.trans lastExtension) lastValid ?_ lastTrace
              unfold Relation.RepresentsList
              exact ⟨image, lastImages, rfl,
                Relation.Represents.stable lastExtension _ _ producedRelated, listRelated⟩

/-- `value.filter(callback)` enters the callback once per element, in order, keeping the elements it
accepts, and a represented `Bool` is truthy exactly when it is `true`. -/
theorem filterElements_refines {program : Ir.Program} {target : Target.Program} {runtime : Runtime}
    {fuel : Nat}
    (bodyAtLower : ∀ smaller, smaller + 1 = fuel → ∀ (inner : Ir.Expr) (emitted : Target.Body),
      Compile.body program inner = .ok emitted →
      EverywhereBody program target runtime smaller inner emitted)
    {captured : List Source.Value} {parameters : List Ir.Field} {body : Ir.Expr} {callee : Value} :
    ∀ (elements : List Source.Value) (images : List Value) (trace : Source.Trace)
      (state : Target.State),
      state.heap.WellFormed → state.ClosuresWellFormed →
      Relation.Represents program state (.closure captured parameters body) callee →
      Relation.RepresentsList program state elements images →
      Relation.RefinesTrace program state trace state.trace →
      Relation.RefinesList program state
        (Source.filterElements program fuel trace captured parameters body elements)
        (Target.filterCalls target runtime fuel state callee images)
  | [], images, trace, state, heapValid, closuresValid, _, related, traceRefines => by
      unfold Relation.RepresentsList at related
      subst related
      simp only [Source.filterElements, Target.filterCalls]
      exact refinesList_values (Target.State.Extension.refl state heapValid) closuresValid
        represents_nil traceRefines
  | head :: rest, images, trace, state, heapValid, closuresValid, calleeRelated, related,
      traceRefines => by
      unfold Relation.RepresentsList at related
      obtain ⟨headImage, restImages, imagesEq, headRelated, tailRelated⟩ := related
      subst imagesEq
      simp only [Source.filterElements, Target.filterCalls]
      cases headRun : Source.applyClosure program fuel trace captured parameters body [head] with
      | fault fault next => exact refinesList_fault
      | exhausted next =>
          obtain ⟨targetState, targetRun, extension, nextValid, nextTrace⟩ :=
            refines_exhausted_inv (headRun ▸ invoke_refines bodyAtLower heapValid closuresValid
              calleeRelated (represents_singleton headRelated) traceRefines)
          rw [targetRun]
          exact refinesList_exhausted extension nextValid nextTrace
      | value produced next =>
          obtain ⟨image, targetState, targetRun, extension, nextValid, producedRelated,
            nextTrace⟩ :=
            refines_value_inv (headRun ▸ invoke_refines bodyAtLower heapValid closuresValid
              calleeRelated (represents_singleton headRelated) traceRefines)
          rw [targetRun]
          cases produced with
          | boolean keep =>
              unfold Relation.Represents at producedRelated
              subst producedRelated
              dsimp only
              have step := filterElements_refines bodyAtLower rest restImages next targetState
                extension.nextWellFormed nextValid
                (Relation.Represents.stable extension _ _ calleeRelated)
                (Relation.RepresentsList.stable extension rest restImages tailRelated) nextTrace
              cases restRun :
                  Source.filterElements program fuel next captured parameters body rest with
              | fault fault last => exact refinesList_fault
              | exhausted last =>
                  obtain ⟨lastState, lastRun, lastExtension, lastValid, lastTrace⟩ :=
                    refinesList_exhausted_inv (restRun ▸ step)
                  rw [lastRun]
                  exact refinesList_exhausted (extension.trans lastExtension) lastValid lastTrace
              | values kept last =>
                  obtain ⟨lastImages, lastState, lastRun, lastExtension, lastValid, listRelated,
                    lastTrace⟩ := refinesList_inv (restRun ▸ step)
                  rw [lastRun]
                  refine refinesList_values (extension.trans lastExtension) lastValid ?_ lastTrace
                  cases keep with
                  | true =>
                      simp only [Value.toBoolean, Primitive.toBoolean, if_true]
                      unfold Relation.RepresentsList
                      exact ⟨headImage, lastImages, rfl,
                        Relation.Represents.stable (extension.trans lastExtension) _ _ headRelated,
                        listRelated⟩
                  | false =>
                      simp only [Value.toBoolean, Primitive.toBoolean, Bool.false_eq_true, if_false]
                      exact listRelated
          | nat _ => exact refinesList_fault
          | int _ => exact refinesList_fault
          | char _ => exact refinesList_fault
          | string _ => exact refinesList_fault
          | record _ _ => exact refinesList_fault
          | array _ _ => exact refinesList_fault
          | variant _ _ _ => exact refinesList_fault
          | closure _ _ _ => exact refinesList_fault

/-- `value.some(callback)` enters the callback once per element, in order, until one accepts. -/
theorem anyElements_refines {program : Ir.Program} {target : Target.Program} {runtime : Runtime}
    {fuel : Nat}
    (bodyAtLower : ∀ smaller, smaller + 1 = fuel → ∀ (inner : Ir.Expr) (emitted : Target.Body),
      Compile.body program inner = .ok emitted →
      EverywhereBody program target runtime smaller inner emitted)
    {captured : List Source.Value} {parameters : List Ir.Field} {body : Ir.Expr} {callee : Value} :
    ∀ (elements : List Source.Value) (images : List Value) (trace : Source.Trace)
      (state : Target.State),
      state.heap.WellFormed → state.ClosuresWellFormed →
      Relation.Represents program state (.closure captured parameters body) callee →
      Relation.RepresentsList program state elements images →
      Relation.RefinesTrace program state trace state.trace →
      Relation.Refines program state
        (Source.anyElements program fuel trace captured parameters body elements)
        (Target.anyCalls target runtime fuel state callee images)
  | [], images, trace, state, heapValid, closuresValid, _, related, traceRefines => by
      unfold Relation.RepresentsList at related
      subst related
      simp only [Source.anyElements, Target.anyCalls]
      refine refines_value (Target.State.Extension.refl state heapValid) closuresValid ?_
        traceRefines
      unfold Relation.Represents
      rfl
  | head :: rest, images, trace, state, heapValid, closuresValid, calleeRelated, related,
      traceRefines => by
      unfold Relation.RepresentsList at related
      obtain ⟨headImage, restImages, imagesEq, headRelated, tailRelated⟩ := related
      subst imagesEq
      simp only [Source.anyElements, Target.anyCalls]
      cases headRun : Source.applyClosure program fuel trace captured parameters body [head] with
      | fault fault next => exact refines_fault
      | exhausted next =>
          obtain ⟨targetState, targetRun, extension, nextValid, nextTrace⟩ :=
            refines_exhausted_inv (headRun ▸ invoke_refines bodyAtLower heapValid closuresValid
              calleeRelated (represents_singleton headRelated) traceRefines)
          rw [targetRun]
          exact refines_exhausted extension nextValid nextTrace
      | value produced next =>
          obtain ⟨image, targetState, targetRun, extension, nextValid, producedRelated,
            nextTrace⟩ :=
            refines_value_inv (headRun ▸ invoke_refines bodyAtLower heapValid closuresValid
              calleeRelated (represents_singleton headRelated) traceRefines)
          rw [targetRun]
          cases produced with
          | boolean decision =>
              unfold Relation.Represents at producedRelated
              subst producedRelated
              cases decision with
              | true =>
                  simp only [Value.toBoolean, Primitive.toBoolean, if_true]
                  refine refines_value extension nextValid ?_ nextTrace
                  unfold Relation.Represents
                  rfl
              | false =>
                  simp only [Value.toBoolean, Primitive.toBoolean, Bool.false_eq_true, if_false]
                  refine refines_widen extension ?_
                  exact anyElements_refines bodyAtLower rest restImages next targetState
                    extension.nextWellFormed nextValid
                    (Relation.Represents.stable extension _ _ calleeRelated)
                    (Relation.RepresentsList.stable extension rest restImages tailRelated) nextTrace
          | nat _ => exact refines_fault
          | int _ => exact refines_fault
          | char _ => exact refines_fault
          | string _ => exact refines_fault
          | record _ _ => exact refines_fault
          | array _ _ => exact refines_fault
          | variant _ _ _ => exact refines_fault
          | closure _ _ _ => exact refines_fault

/-- `value.every(callback)` enters the callback once per element, in order, until one refuses. -/
theorem allElements_refines {program : Ir.Program} {target : Target.Program} {runtime : Runtime}
    {fuel : Nat}
    (bodyAtLower : ∀ smaller, smaller + 1 = fuel → ∀ (inner : Ir.Expr) (emitted : Target.Body),
      Compile.body program inner = .ok emitted →
      EverywhereBody program target runtime smaller inner emitted)
    {captured : List Source.Value} {parameters : List Ir.Field} {body : Ir.Expr} {callee : Value} :
    ∀ (elements : List Source.Value) (images : List Value) (trace : Source.Trace)
      (state : Target.State),
      state.heap.WellFormed → state.ClosuresWellFormed →
      Relation.Represents program state (.closure captured parameters body) callee →
      Relation.RepresentsList program state elements images →
      Relation.RefinesTrace program state trace state.trace →
      Relation.Refines program state
        (Source.allElements program fuel trace captured parameters body elements)
        (Target.allCalls target runtime fuel state callee images)
  | [], images, trace, state, heapValid, closuresValid, _, related, traceRefines => by
      unfold Relation.RepresentsList at related
      subst related
      simp only [Source.allElements, Target.allCalls]
      refine refines_value (Target.State.Extension.refl state heapValid) closuresValid ?_
        traceRefines
      unfold Relation.Represents
      rfl
  | head :: rest, images, trace, state, heapValid, closuresValid, calleeRelated, related,
      traceRefines => by
      unfold Relation.RepresentsList at related
      obtain ⟨headImage, restImages, imagesEq, headRelated, tailRelated⟩ := related
      subst imagesEq
      simp only [Source.allElements, Target.allCalls]
      cases headRun : Source.applyClosure program fuel trace captured parameters body [head] with
      | fault fault next => exact refines_fault
      | exhausted next =>
          obtain ⟨targetState, targetRun, extension, nextValid, nextTrace⟩ :=
            refines_exhausted_inv (headRun ▸ invoke_refines bodyAtLower heapValid closuresValid
              calleeRelated (represents_singleton headRelated) traceRefines)
          rw [targetRun]
          exact refines_exhausted extension nextValid nextTrace
      | value produced next =>
          obtain ⟨image, targetState, targetRun, extension, nextValid, producedRelated,
            nextTrace⟩ :=
            refines_value_inv (headRun ▸ invoke_refines bodyAtLower heapValid closuresValid
              calleeRelated (represents_singleton headRelated) traceRefines)
          rw [targetRun]
          cases produced with
          | boolean decision =>
              unfold Relation.Represents at producedRelated
              subst producedRelated
              cases decision with
              | false =>
                  simp only [Value.toBoolean, Primitive.toBoolean, Bool.false_eq_true, if_false]
                  refine refines_value extension nextValid ?_ nextTrace
                  unfold Relation.Represents
                  rfl
              | true =>
                  simp only [Value.toBoolean, Primitive.toBoolean, if_true]
                  refine refines_widen extension ?_
                  exact allElements_refines bodyAtLower rest restImages next targetState
                    extension.nextWellFormed nextValid
                    (Relation.Represents.stable extension _ _ calleeRelated)
                    (Relation.RepresentsList.stable extension rest restImages tailRelated) nextTrace
          | nat _ => exact refines_fault
          | int _ => exact refines_fault
          | char _ => exact refines_fault
          | string _ => exact refines_fault
          | record _ _ => exact refines_fault
          | array _ _ => exact refines_fault
          | variant _ _ _ => exact refines_fault
          | closure _ _ _ => exact refines_fault

/-- `value.reduce(callback, initial)` folds from the left, accumulator first. -/
theorem foldLeftElements_refines {program : Ir.Program} {target : Target.Program}
    {runtime : Runtime} {fuel : Nat}
    (bodyAtLower : ∀ smaller, smaller + 1 = fuel → ∀ (inner : Ir.Expr) (emitted : Target.Body),
      Compile.body program inner = .ok emitted →
      EverywhereBody program target runtime smaller inner emitted)
    {captured : List Source.Value} {parameters : List Ir.Field} {body : Ir.Expr} {callee : Value} :
    ∀ (elements : List Source.Value) (images : List Value) (accumulator : Source.Value)
      (accumulatorImage : Value) (trace : Source.Trace) (state : Target.State),
      state.heap.WellFormed → state.ClosuresWellFormed →
      Relation.Represents program state (.closure captured parameters body) callee →
      Relation.Represents program state accumulator accumulatorImage →
      Relation.RepresentsList program state elements images →
      Relation.RefinesTrace program state trace state.trace →
      Relation.Refines program state
        (Source.foldLeftElements program fuel trace captured parameters body accumulator elements)
        (Target.foldLeftCalls target runtime fuel state callee accumulatorImage images)
  | [], images, accumulator, accumulatorImage, trace, state, heapValid, closuresValid, _,
      accumulatorRelated, related, traceRefines => by
      unfold Relation.RepresentsList at related
      subst related
      simp only [Source.foldLeftElements, Target.foldLeftCalls]
      exact refines_value (Target.State.Extension.refl state heapValid) closuresValid
        accumulatorRelated traceRefines
  | head :: rest, images, accumulator, accumulatorImage, trace, state, heapValid, closuresValid,
      calleeRelated, accumulatorRelated, related, traceRefines => by
      unfold Relation.RepresentsList at related
      obtain ⟨headImage, restImages, imagesEq, headRelated, tailRelated⟩ := related
      subst imagesEq
      simp only [Source.foldLeftElements, Target.foldLeftCalls]
      cases headRun :
          Source.applyClosure program fuel trace captured parameters body [accumulator, head] with
      | fault fault next => exact refines_fault
      | exhausted next =>
          obtain ⟨targetState, targetRun, extension, nextValid, nextTrace⟩ :=
            refines_exhausted_inv (headRun ▸ invoke_refines bodyAtLower heapValid closuresValid
              calleeRelated (represents_pair accumulatorRelated headRelated) traceRefines)
          rw [targetRun]
          exact refines_exhausted extension nextValid nextTrace
      | value produced next =>
          obtain ⟨image, targetState, targetRun, extension, nextValid, producedRelated,
            nextTrace⟩ :=
            refines_value_inv (headRun ▸ invoke_refines bodyAtLower heapValid closuresValid
              calleeRelated (represents_pair accumulatorRelated headRelated) traceRefines)
          rw [targetRun]
          refine refines_widen extension ?_
          exact foldLeftElements_refines bodyAtLower rest restImages produced image next
            targetState extension.nextWellFormed nextValid
            (Relation.Represents.stable extension _ _ calleeRelated) producedRelated
            (Relation.RepresentsList.stable extension rest restImages tailRelated) nextTrace

/-- `value.reduceRight(callback, initial)` folds from the right, element first. -/
theorem foldRightElements_refines {program : Ir.Program} {target : Target.Program}
    {runtime : Runtime} {fuel : Nat}
    (bodyAtLower : ∀ smaller, smaller + 1 = fuel → ∀ (inner : Ir.Expr) (emitted : Target.Body),
      Compile.body program inner = .ok emitted →
      EverywhereBody program target runtime smaller inner emitted)
    {captured : List Source.Value} {parameters : List Ir.Field} {body : Ir.Expr} {callee : Value} :
    ∀ (elements : List Source.Value) (images : List Value) (accumulator : Source.Value)
      (accumulatorImage : Value) (trace : Source.Trace) (state : Target.State),
      state.heap.WellFormed → state.ClosuresWellFormed →
      Relation.Represents program state (.closure captured parameters body) callee →
      Relation.Represents program state accumulator accumulatorImage →
      Relation.RepresentsList program state elements images →
      Relation.RefinesTrace program state trace state.trace →
      Relation.Refines program state
        (Source.foldRightElements program fuel trace captured parameters body accumulator elements)
        (Target.foldRightCalls target runtime fuel state callee accumulatorImage images)
  | [], images, accumulator, accumulatorImage, trace, state, heapValid, closuresValid, _,
      accumulatorRelated, related, traceRefines => by
      unfold Relation.RepresentsList at related
      subst related
      simp only [Source.foldRightElements, Target.foldRightCalls]
      exact refines_value (Target.State.Extension.refl state heapValid) closuresValid
        accumulatorRelated traceRefines
  | head :: rest, images, accumulator, accumulatorImage, trace, state, heapValid, closuresValid,
      calleeRelated, accumulatorRelated, related, traceRefines => by
      unfold Relation.RepresentsList at related
      obtain ⟨headImage, restImages, imagesEq, headRelated, tailRelated⟩ := related
      subst imagesEq
      simp only [Source.foldRightElements, Target.foldRightCalls]
      have step := foldRightElements_refines bodyAtLower rest restImages accumulator
        accumulatorImage trace state heapValid closuresValid calleeRelated accumulatorRelated
        tailRelated traceRefines
      cases restRun : Source.foldRightElements program fuel trace captured parameters body
          accumulator rest with
      | fault fault next => exact refines_fault
      | exhausted next =>
          obtain ⟨targetState, targetRun, extension, nextValid, nextTrace⟩ :=
            refines_exhausted_inv (restRun ▸ step)
          rw [targetRun]
          exact refines_exhausted extension nextValid nextTrace
      | value produced next =>
          obtain ⟨image, targetState, targetRun, extension, nextValid, producedRelated,
            nextTrace⟩ := refines_value_inv (restRun ▸ step)
          rw [targetRun]
          refine refines_widen extension ?_
          exact invoke_refines bodyAtLower extension.nextWellFormed nextValid
            (Relation.Represents.stable extension _ _ calleeRelated)
            (represents_pair
              (Relation.Represents.stable extension _ _ headRelated) producedRelated)
            nextTrace

/-! ### The first-order opcodes

`Source.applyStrict` matches the opcode first, so the operand list each opcode accepts is one split
away. The twenty first-order opcodes then denote the `Runtime` operation they name, at no fuel and no
trace cost, and the engine law is consumed from `Ir.Opcode.Preserves` rather than restated.
-/

/-- A first-order opcode answers in place: no fuel, no event, no heap change. -/
private theorem refines_inPlace {program : Ir.Program} {state : Target.State}
    {trace : Source.Trace} {value : Source.Value} {image : Value}
    (heapValid : state.heap.WellFormed) (closuresValid : state.ClosuresWellFormed)
    (related : Relation.Represents program state value image)
    (traceRefines : Relation.RefinesTrace program state trace state.trace) :
    Relation.Refines program state (.value value trace) (.ok image state) :=
  refines_value (Target.State.Extension.refl state heapValid) closuresValid related traceRefines

/-- A represented list is a dense array the target reads back exactly. -/
theorem readArray_of_represents {program : Ir.Program} {state : Target.State} {element : Ir.Ty}
    {elements : List Source.Value} {subject : Value}
    (related : Relation.Represents program state (.array element elements) subject) :
    ∃ images, Target.readArray state subject = .ok images ∧
      Relation.RepresentsList program state elements images := by
  unfold Relation.Represents at related
  obtain ⟨ref, images, subjectEq, listRelated, dense⟩ := related
  subst subjectEq
  exact ⟨images, dense, listRelated⟩

/-- Allocating the emitted array refines producing the source list it represents. -/
theorem refines_allocateArray {program : Ir.Program} {state : Target.State} {trace : Source.Trace}
    {element : Ir.Ty} {elements : List Source.Value} {images : List Value}
    (heapValid : state.heap.WellFormed) (closuresValid : state.ClosuresWellFormed)
    (related : Relation.RepresentsList program state elements images)
    (traceRefines : Relation.RefinesTrace program state trace state.trace)
    (bound : elements.length ≤ Heap.maxArrayLength) :
    Relation.Refines program state (.value (.array element elements) trace)
      (Target.allocateArray state images) := by
  obtain ⟨ref, final, allocated, traceEq, _, extension, finalValid, dense⟩ :=
    Allocation.allocateArray_shape state images heapValid closuresValid
      (representsList_valuesValid elements images related)
      (by rw [← representsList_length elements images related]; exact bound)
  rw [allocated]
  refine refines_value extension finalValid ?_ ?_
  · unfold Relation.Represents
    exact ⟨ref, images, rfl, Relation.RepresentsList.stable extension elements images related,
      dense⟩
  · rw [traceEq]
    exact Relation.RefinesTrace.stable extension trace state.trace traceRefines

/-- A first-order opcode that answers a value denotes that value, at no fuel and no trace cost. -/
theorem applyOperation_of_strict_ok {program : Ir.Program} {fuel : Nat} {trace : Source.Trace}
    {typeArguments : List Ir.Ty} {opcode : Ir.Opcode} {values : List Source.Value}
    {value : Source.Value} (firstOrder : opcode.callback = false)
    (strict : Source.applyStrict opcode values = .ok value) :
    Source.applyOperation program fuel trace opcode typeArguments values = .value value trace := by
  cases opcode <;> simp_all [Source.applyOperation, Ir.Opcode.callback]

/-- A first-order opcode that refuses its operands faults where it occurs. -/
theorem applyOperation_of_strict_error {program : Ir.Program} {fuel : Nat} {trace : Source.Trace}
    {typeArguments : List Ir.Ty} {opcode : Ir.Opcode} {values : List Source.Value}
    {fault : Source.Fault} (firstOrder : opcode.callback = false)
    (strict : Source.applyStrict opcode values = .error fault) :
    Source.applyOperation program fuel trace opcode typeArguments values = .fault fault trace := by
  cases opcode <;> simp_all [Source.applyOperation, Ir.Opcode.callback]

/-- `bool.not` accepts one boolean operand. -/
theorem strict_boolNot {values : List Source.Value} {value : Source.Value}
    (produced : Source.applyStrict .boolNot values = .ok value) :
    ∃ operand, values = [.boolean operand] := by
  unfold Source.applyStrict at produced
  split at produced <;> simp_all

/-- `bool.equals` accepts two boolean operands. -/
theorem strict_boolEquals {values : List Source.Value} {value : Source.Value}
    (produced : Source.applyStrict .boolEquals values = .ok value) :
    ∃ left right, values = [.boolean left, .boolean right] := by
  unfold Source.applyStrict at produced
  split at produced <;> simp_all

/-- `nat.successor` accepts one `Nat` operand. -/
theorem strict_natSuccessor {values : List Source.Value} {value : Source.Value}
    (produced : Source.applyStrict .natSuccessor values = .ok value) :
    ∃ operand, values = [.nat operand] := by
  unfold Source.applyStrict at produced
  split at produced <;> simp_all

/-- The binary `Nat` opcodes accept two `Nat` operands. -/
theorem strict_binaryNat {opcode : Ir.Opcode} {values : List Source.Value} {value : Source.Value}
    (binary : opcode = .natAdd ∨ opcode = .natSubtract ∨ opcode = .natMultiply ∨
      opcode = .natLess ∨ opcode = .natLessOrEqual ∨ opcode = .natEquals)
    (produced : Source.applyStrict opcode values = .ok value) :
    ∃ left right, values = [.nat left, .nat right] := by
  rcases binary with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (unfold Source.applyStrict at produced; split at produced <;> simp_all)

/-- The binary `String` opcodes accept two `String` operands. -/
theorem strict_binaryString {opcode : Ir.Opcode} {values : List Source.Value}
    {value : Source.Value}
    (binary : opcode = .stringAppend ∨ opcode = .stringEquals)
    (produced : Source.applyStrict opcode values = .ok value) :
    ∃ left right, values = [.string left, .string right] := by
  rcases binary with rfl | rfl <;>
    (unfold Source.applyStrict at produced; split at produced <;> simp_all)

/-- The unary list opcodes accept one array operand. -/
theorem strict_unaryArray {opcode : Ir.Opcode} {values : List Source.Value} {value : Source.Value}
    (unary : opcode = .listLength ∨ opcode = .listIsEmpty ∨ opcode = .listReverse ∨
      opcode = .listRest ∨ opcode = .listFirst ∨ opcode = .listHead)
    (produced : Source.applyStrict opcode values = .ok value) :
    ∃ element elements, values = [.array element elements] := by
  rcases unary with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (unfold Source.applyStrict at produced; split at produced <;> simp_all)

/-- `list.append` accepts two array operands. -/
theorem strict_listAppend {values : List Source.Value} {value : Source.Value}
    (produced : Source.applyStrict .listAppend values = .ok value) :
    ∃ firstElement first secondElement second,
      values = [.array firstElement first, .array secondElement second] := by
  unfold Source.applyStrict at produced
  split at produced <;> simp_all

/-- The binary `Int` opcodes accept two `Int` operands. -/
theorem strict_binaryInt {opcode : Ir.Opcode} {values : List Source.Value} {value : Source.Value}
    (binary : opcode = .intAdd ∨ opcode = .intSubtract ∨ opcode = .intMultiply ∨
      opcode = .intTruncatedDivide ∨ opcode = .intTruncatedModulo ∨ opcode = .intLess ∨
      opcode = .intLessOrEqual ∨ opcode = .intEquals)
    (produced : Source.applyStrict opcode values = .ok value) :
    ∃ left right, values = [.int left, .int right] := by
  rcases binary with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (unfold Source.applyStrict at produced; split at produced <;> simp_all)

/-- The unary `Int` opcodes accept one `Int` operand. -/
theorem strict_unaryInt {opcode : Ir.Opcode} {values : List Source.Value} {value : Source.Value}
    (unary : opcode = .intNegate ∨ opcode = .intToNat)
    (produced : Source.applyStrict opcode values = .ok value) :
    ∃ operand, values = [.int operand] := by
  rcases unary with rfl | rfl <;>
    (unfold Source.applyStrict at produced; split at produced <;> simp_all)

/-- The two opcodes that read a `Nat` accept one `Nat` operand. -/
theorem strict_unaryNat {opcode : Ir.Opcode} {values : List Source.Value} {value : Source.Value}
    (unary : opcode = .intOfNat ∨ opcode = .charOfNat)
    (produced : Source.applyStrict opcode values = .ok value) :
    ∃ operand, values = [.nat operand] := by
  rcases unary with rfl | rfl <;>
    (unfold Source.applyStrict at produced; split at produced <;> simp_all)

/-- `char.toNat` and `string.singleton` accept one `Char` operand. -/
theorem strict_unaryChar {opcode : Ir.Opcode} {values : List Source.Value} {value : Source.Value}
    (unary : opcode = .charToNat ∨ opcode = .stringSingleton)
    (produced : Source.applyStrict opcode values = .ok value) :
    ∃ character, values = [.char character] := by
  rcases unary with rfl | rfl <;>
    (unfold Source.applyStrict at produced; split at produced <;> simp_all)

/-- The binary `Char` opcodes accept two `Char` operands. -/
theorem strict_binaryChar {opcode : Ir.Opcode} {values : List Source.Value} {value : Source.Value}
    (binary : opcode = .charEquals ∨ opcode = .charLess)
    (produced : Source.applyStrict opcode values = .ok value) :
    ∃ left right, values = [.char left, .char right] := by
  rcases binary with rfl | rfl <;>
    (unfold Source.applyStrict at produced; split at produced <;> simp_all)

/-- The unary `String` opcodes accept one `String` operand. -/
theorem strict_unaryString {opcode : Ir.Opcode} {values : List Source.Value}
    {value : Source.Value}
    (unary : opcode = .stringLength ∨ opcode = .stringIsEmpty ∨ opcode = .stringToList)
    (produced : Source.applyStrict opcode values = .ok value) :
    ∃ operand, values = [.string operand] := by
  rcases unary with rfl | rfl | rfl <;>
    (unfold Source.applyStrict at produced; split at produced <;> simp_all)

/-- `string.push` accepts a `String` and a `Char`. -/
theorem strict_stringPush {values : List Source.Value} {value : Source.Value}
    (produced : Source.applyStrict .stringPush values = .ok value) :
    ∃ operand character, values = [.string operand, .char character] := by
  unfold Source.applyStrict at produced
  split at produced <;> simp_all

/-- The unary `Array` opcodes accept one array operand. -/
theorem strict_unaryArrayOf {opcode : Ir.Opcode} {values : List Source.Value}
    {value : Source.Value}
    (unary : opcode = .arraySize ∨ opcode = .arrayIsEmpty ∨ opcode = .arrayReverse ∨
      opcode = .arrayToList ∨ opcode = .arrayOfList)
    (produced : Source.applyStrict opcode values = .ok value) :
    ∃ element elements, values = [.array element elements] := by
  cases values with
  | nil => rcases unary with rfl | rfl | rfl | rfl | rfl <;> simp [Source.applyStrict] at produced
  | cons head rest =>
      cases rest with
      | cons _ _ =>
          rcases unary with rfl | rfl | rfl | rfl | rfl <;> simp [Source.applyStrict] at produced
      | nil =>
          cases head with
          | array element elements => exact ⟨element, elements, rfl⟩
          | boolean _ | nat _ | int _ | string _ | char _ | record _ _ | variant _ _ _
          | closure _ _ _ =>
              rcases unary with rfl | rfl | rfl | rfl | rfl <;>
                simp [Source.applyStrict] at produced

/-- `array.push` accepts an array and one further value. -/
theorem strict_arrayPush {values : List Source.Value} {value : Source.Value}
    (produced : Source.applyStrict .arrayPush values = .ok value) :
    ∃ element elements pushed, values = [.array element elements, pushed] := by
  unfold Source.applyStrict at produced
  split at produced <;> simp_all

/-- `array.append` accepts two array operands. -/
theorem strict_arrayAppend {values : List Source.Value} {value : Source.Value}
    (produced : Source.applyStrict .arrayAppend values = .ok value) :
    ∃ firstElement first secondElement second,
      values = [.array firstElement first, .array secondElement second] := by
  unfold Source.applyStrict at produced
  split at produced <;> simp_all

/-- `string.ofList` accepts one array operand, and refuses it unless every element is a
character. -/
theorem strict_stringOfList {values : List Source.Value} {value : Source.Value}
    (produced : Source.applyStrict .stringOfList values = .ok value) :
    ∃ element characters,
      values = [.array element (characters.map Source.Value.char)] ∧
        value = .string (String.ofList characters) := by
  cases values with
  | nil => simp [Source.applyStrict] at produced
  | cons head rest =>
      cases rest with
      | cons _ _ => simp [Source.applyStrict] at produced
      | nil =>
          cases head with
          | array element elements =>
              cases read : Source.charList? elements with
              | none => simp [Source.applyStrict, read] at produced
              | some characters =>
                  refine ⟨element, characters, ?_, ?_⟩
                  · rw [Source.charList?_eq_some read]
                  · simp only [Source.applyStrict, read, Except.ok.injEq] at produced
                    exact produced.symm
          | boolean _ | nat _ | int _ | string _ | char _ | record _ _ | variant _ _ _
          | closure _ _ _ => simp [Source.applyStrict] at produced

/-- A character list and its images are related pointwise, which is what makes `string.toList`
produce a represented array and `string.ofList` read one back. -/
theorem represents_charList {program : Ir.Program} {state : Target.State} :
    ∀ characters : List Char,
      Relation.RepresentsList program state (characters.map Source.Value.char)
        (characters.map Encode.char)
  | [] => by unfold Relation.RepresentsList; rfl
  | character :: rest => by
      simp only [List.map_cons]
      unfold Relation.RepresentsList
      refine ⟨Encode.char character, rest.map Encode.char, rfl, ?_, represents_charList rest⟩
      unfold Relation.Represents
      rfl

/-- A represented character list has exactly the character images. -/
theorem representsList_charList {program : Ir.Program} {state : Target.State} :
    ∀ (characters : List Char) (images : List Value),
      Relation.RepresentsList program state (characters.map Source.Value.char) images →
      images = characters.map Encode.char
  | [], images, related => by unfold Relation.RepresentsList at related; exact related
  | character :: rest, images, related => by
      unfold Relation.RepresentsList at related
      obtain ⟨image, restImages, imagesEq, headRelated, tailRelated⟩ := related
      unfold Relation.Represents at headRelated
      subst imagesEq
      subst headRelated
      rw [List.map_cons, representsList_charList rest restImages tailRelated]
      rfl

/-- `bool.and` and `bool.or` have no first-order clause: they are lazy in their right operand, which
`eval` decides before any operand is evaluated. -/
theorem strict_refuses_lazy {opcode : Ir.Opcode} {values : List Source.Value}
    {value : Source.Value} (lazy : opcode = .boolAnd ∨ opcode = .boolOr) :
    Source.applyStrict opcode values ≠ .ok value := by
  intro produced
  rcases lazy with rfl | rfl <;>
    (unfold Source.applyStrict at produced; split at produced <;> simp_all)

/--
The twenty first-order opcodes denote the `Runtime` operation they name, on representing operands, at
no fuel and no trace cost. One row per opcode: the engine law is `Ir.Opcode.Preserves`, consumed as a
hypothesis, and `Opcode.registry` discharges it from the opcode's own recorded assumption closure.
-/
theorem runOperation_firstOrder_refines {program : Ir.Program} {target : Target.Program}
    {runtime : Runtime} {fuel : Nat} {opcode : Ir.Opcode} {typeArguments : List Ir.Ty}
    {values : List Source.Value} {operands : List Value} {trace : Source.Trace}
    {state : Target.State}
    (firstOrder : opcode.callback = false)
    (law : opcode.Preserves runtime)
    (notOperator : ∀ form, opcode.operator? = some form → values.length ≠ form.operands)
    (heapValid : state.heap.WellFormed) (closuresValid : state.ClosuresWellFormed)
    (related : Relation.RepresentsList program state values operands)
    (traceRefines : Relation.RefinesTrace program state trace state.trace)
    (fits : ∀ (element : Ir.Ty) (elements : List Source.Value) (next : Source.Trace),
      Source.applyOperation program fuel trace opcode typeArguments values
        = .value (.array element elements) next → elements.length ≤ Heap.maxArrayLength) :
    Relation.Refines program state
      (Source.applyOperation program fuel trace opcode typeArguments values)
      (Target.runOperation target runtime fuel state opcode operands) := by
  cases opcode
  case listMap => exact absurd firstOrder (by simp [Ir.Opcode.callback])
  case listFilter => exact absurd firstOrder (by simp [Ir.Opcode.callback])
  case listFoldLeft => exact absurd firstOrder (by simp [Ir.Opcode.callback])
  case listFoldRight => exact absurd firstOrder (by simp [Ir.Opcode.callback])
  case listAny => exact absurd firstOrder (by simp [Ir.Opcode.callback])
  case listAll => exact absurd firstOrder (by simp [Ir.Opcode.callback])
  case boolAnd =>
    cases strict : Source.applyStrict Ir.Opcode.boolAnd values with
    | ok produced => exact absurd strict (strict_refuses_lazy (Or.inl rfl))
    | error fault =>
        rw [applyOperation_of_strict_error firstOrder strict]
        exact refines_fault
  case boolOr =>
    cases strict : Source.applyStrict Ir.Opcode.boolOr values with
    | ok produced => exact absurd strict (strict_refuses_lazy (Or.inr rfl))
    | error fault =>
        rw [applyOperation_of_strict_error firstOrder strict]
        exact refines_fault
  case boolNot =>
    cases strict : Source.applyStrict Ir.Opcode.boolNot values with
    | error fault =>
        rw [applyOperation_of_strict_error firstOrder strict]
        exact refines_fault
    | ok produced =>
        obtain ⟨operand, valuesEq⟩ := strict_boolNot strict
        exact absurd (by rw [valuesEq]; rfl) (notOperator .logicalNot rfl)
  case boolEquals =>
    cases strict : Source.applyStrict Ir.Opcode.boolEquals values with
    | error fault =>
        rw [applyOperation_of_strict_error firstOrder strict]
        exact refines_fault
    | ok produced =>
        obtain ⟨left, right, valuesEq⟩ := strict_boolEquals strict
        exact absurd (by rw [valuesEq]; rfl) (notOperator .strictEquals rfl)
  case natSuccessor =>
    cases strict : Source.applyStrict Ir.Opcode.natSuccessor values with
    | error fault =>
        rw [applyOperation_of_strict_error firstOrder strict]
        exact refines_fault
    | ok produced =>
        obtain ⟨operand, valuesEq⟩ := strict_natSuccessor strict
        subst valuesEq
        have producedEq : produced = .nat (operand + 1) := by
          simpa only [Source.applyStrict, Except.ok.injEq] using strict.symm
        subst producedEq
        obtain ⟨image, operandsEq, operandRelated⟩ := representsList_one related
        subst operandsEq
        unfold Relation.Represents at operandRelated
        subst operandRelated
        rw [applyOperation_of_strict_ok firstOrder strict]
        simp only [Ir.Opcode.Preserves] at law
        simp only [Target.runOperation]
        refine refines_inPlace heapValid closuresValid ?_ traceRefines
        unfold Relation.Represents
        exact (law operand).symm
  case natAdd =>
    cases strict : Source.applyStrict Ir.Opcode.natAdd values with
    | error fault =>
        rw [applyOperation_of_strict_error firstOrder strict]
        exact refines_fault
    | ok produced =>
        obtain ⟨left, right, valuesEq⟩ := strict_binaryNat (by simp) strict
        subst valuesEq
        have producedEq : produced = .nat (left + right) := by
          simpa only [Source.applyStrict, Except.ok.injEq] using strict.symm
        subst producedEq
        obtain ⟨leftImage, rightImage, operandsEq, leftRelated, rightRelated⟩ :=
          representsList_two related
        subst operandsEq
        unfold Relation.Represents at leftRelated rightRelated
        subst leftRelated
        subst rightRelated
        rw [applyOperation_of_strict_ok firstOrder strict]
        simp only [Ir.Opcode.Preserves] at law
        simp only [Target.runOperation]
        refine refines_inPlace heapValid closuresValid ?_ traceRefines
        unfold Relation.Represents
        exact (law left right).symm
  case natSubtract =>
    cases strict : Source.applyStrict Ir.Opcode.natSubtract values with
    | error fault =>
        rw [applyOperation_of_strict_error firstOrder strict]
        exact refines_fault
    | ok produced =>
        obtain ⟨left, right, valuesEq⟩ := strict_binaryNat (by simp) strict
        subst valuesEq
        have producedEq : produced = .nat (left - right) := by
          simpa only [Source.applyStrict, Except.ok.injEq] using strict.symm
        subst producedEq
        obtain ⟨leftImage, rightImage, operandsEq, leftRelated, rightRelated⟩ :=
          representsList_two related
        subst operandsEq
        unfold Relation.Represents at leftRelated rightRelated
        subst leftRelated
        subst rightRelated
        rw [applyOperation_of_strict_ok firstOrder strict]
        simp only [Ir.Opcode.Preserves] at law
        simp only [Target.runOperation]
        refine refines_inPlace heapValid closuresValid ?_ traceRefines
        unfold Relation.Represents
        exact (law left right).symm
  case natMultiply =>
    cases strict : Source.applyStrict Ir.Opcode.natMultiply values with
    | error fault =>
        rw [applyOperation_of_strict_error firstOrder strict]
        exact refines_fault
    | ok produced =>
        obtain ⟨left, right, valuesEq⟩ := strict_binaryNat (by simp) strict
        subst valuesEq
        have producedEq : produced = .nat (left * right) := by
          simpa only [Source.applyStrict, Except.ok.injEq] using strict.symm
        subst producedEq
        obtain ⟨leftImage, rightImage, operandsEq, leftRelated, rightRelated⟩ :=
          representsList_two related
        subst operandsEq
        unfold Relation.Represents at leftRelated rightRelated
        subst leftRelated
        subst rightRelated
        rw [applyOperation_of_strict_ok firstOrder strict]
        simp only [Ir.Opcode.Preserves] at law
        simp only [Target.runOperation]
        refine refines_inPlace heapValid closuresValid ?_ traceRefines
        unfold Relation.Represents
        exact (law left right).symm
  case natLess =>
    cases strict : Source.applyStrict Ir.Opcode.natLess values with
    | error fault =>
        rw [applyOperation_of_strict_error firstOrder strict]
        exact refines_fault
    | ok produced =>
        obtain ⟨left, right, valuesEq⟩ := strict_binaryNat (by simp) strict
        subst valuesEq
        have producedEq : produced = .boolean (decide (left < right)) := by
          simpa only [Source.applyStrict, Except.ok.injEq] using strict.symm
        subst producedEq
        obtain ⟨leftImage, rightImage, operandsEq, leftRelated, rightRelated⟩ :=
          representsList_two related
        subst operandsEq
        unfold Relation.Represents at leftRelated rightRelated
        subst leftRelated
        subst rightRelated
        rw [applyOperation_of_strict_ok firstOrder strict]
        simp only [Ir.Opcode.Preserves] at law
        simp only [Target.runOperation]
        refine refines_inPlace heapValid closuresValid ?_ traceRefines
        unfold Relation.Represents
        exact (law left right).symm
  case natLessOrEqual =>
    cases strict : Source.applyStrict Ir.Opcode.natLessOrEqual values with
    | error fault =>
        rw [applyOperation_of_strict_error firstOrder strict]
        exact refines_fault
    | ok produced =>
        obtain ⟨left, right, valuesEq⟩ := strict_binaryNat (by simp) strict
        subst valuesEq
        have producedEq : produced = .boolean (decide (left ≤ right)) := by
          simpa only [Source.applyStrict, Except.ok.injEq] using strict.symm
        subst producedEq
        obtain ⟨leftImage, rightImage, operandsEq, leftRelated, rightRelated⟩ :=
          representsList_two related
        subst operandsEq
        unfold Relation.Represents at leftRelated rightRelated
        subst leftRelated
        subst rightRelated
        rw [applyOperation_of_strict_ok firstOrder strict]
        simp only [Ir.Opcode.Preserves] at law
        simp only [Target.runOperation]
        refine refines_inPlace heapValid closuresValid ?_ traceRefines
        unfold Relation.Represents
        exact (law left right).symm
  case natEquals =>
    cases strict : Source.applyStrict Ir.Opcode.natEquals values with
    | error fault =>
        rw [applyOperation_of_strict_error firstOrder strict]
        exact refines_fault
    | ok produced =>
        obtain ⟨left, right, valuesEq⟩ := strict_binaryNat (by simp) strict
        subst valuesEq
        have producedEq : produced = .boolean (left == right) := by
          simpa only [Source.applyStrict, Except.ok.injEq] using strict.symm
        subst producedEq
        obtain ⟨leftImage, rightImage, operandsEq, leftRelated, rightRelated⟩ :=
          representsList_two related
        subst operandsEq
        unfold Relation.Represents at leftRelated rightRelated
        subst leftRelated
        subst rightRelated
        rw [applyOperation_of_strict_ok firstOrder strict]
        simp only [Ir.Opcode.Preserves] at law
        simp only [Target.runOperation]
        refine refines_inPlace heapValid closuresValid ?_ traceRefines
        unfold Relation.Represents
        exact (law left right).symm
  case stringAppend =>
    cases strict : Source.applyStrict Ir.Opcode.stringAppend values with
    | error fault =>
        rw [applyOperation_of_strict_error firstOrder strict]
        exact refines_fault
    | ok produced =>
        obtain ⟨left, right, valuesEq⟩ := strict_binaryString (by simp) strict
        subst valuesEq
        have producedEq : produced = .string (left ++ right) := by
          simpa only [Source.applyStrict, Except.ok.injEq] using strict.symm
        subst producedEq
        obtain ⟨leftImage, rightImage, operandsEq, leftRelated, rightRelated⟩ :=
          representsList_two related
        subst operandsEq
        unfold Relation.Represents at leftRelated rightRelated
        subst leftRelated
        subst rightRelated
        rw [applyOperation_of_strict_ok firstOrder strict]
        simp only [Ir.Opcode.Preserves] at law
        simp only [Target.runOperation]
        refine refines_inPlace heapValid closuresValid ?_ traceRefines
        unfold Relation.Represents
        exact (law left right).symm
  case stringEquals =>
    cases strict : Source.applyStrict Ir.Opcode.stringEquals values with
    | error fault =>
        rw [applyOperation_of_strict_error firstOrder strict]
        exact refines_fault
    | ok produced =>
        obtain ⟨left, right, valuesEq⟩ := strict_binaryString (by simp) strict
        subst valuesEq
        have producedEq : produced = .boolean (left == right) := by
          simpa only [Source.applyStrict, Except.ok.injEq] using strict.symm
        subst producedEq
        obtain ⟨leftImage, rightImage, operandsEq, leftRelated, rightRelated⟩ :=
          representsList_two related
        subst operandsEq
        unfold Relation.Represents at leftRelated rightRelated
        subst leftRelated
        subst rightRelated
        rw [applyOperation_of_strict_ok firstOrder strict]
        simp only [Ir.Opcode.Preserves] at law
        simp only [Target.runOperation]
        refine refines_inPlace heapValid closuresValid ?_ traceRefines
        unfold Relation.Represents
        exact (law left right).symm
  case listLength =>
    cases strict : Source.applyStrict Ir.Opcode.listLength values with
    | error fault =>
        rw [applyOperation_of_strict_error firstOrder strict]
        exact refines_fault
    | ok produced =>
        obtain ⟨element, elements, valuesEq⟩ := strict_unaryArray (by simp) strict
        subst valuesEq
        have producedEq : produced = .nat elements.length := by
          simpa only [Source.applyStrict, Except.ok.injEq] using strict.symm
        subst producedEq
        obtain ⟨subject, operandsEq, subjectRelated⟩ := representsList_one related
        subst operandsEq
        obtain ⟨images, read, listRelated⟩ := readArray_of_represents subjectRelated
        rw [applyOperation_of_strict_ok firstOrder strict]
        simp only [Ir.Opcode.Preserves] at law
        simp only [Target.runOperation, read]
        refine refines_inPlace heapValid closuresValid ?_ traceRefines
        unfold Relation.Represents
        have denoted := law (α := Value) id images
        simp only [List.map_id] at denoted
        rw [← denoted, representsList_length elements images listRelated]
        rfl
  case listIsEmpty =>
    cases strict : Source.applyStrict Ir.Opcode.listIsEmpty values with
    | error fault =>
        rw [applyOperation_of_strict_error firstOrder strict]
        exact refines_fault
    | ok produced =>
        obtain ⟨element, elements, valuesEq⟩ := strict_unaryArray (by simp) strict
        subst valuesEq
        have producedEq : produced = .boolean elements.isEmpty := by
          simpa only [Source.applyStrict, Except.ok.injEq] using strict.symm
        subst producedEq
        obtain ⟨subject, operandsEq, subjectRelated⟩ := representsList_one related
        subst operandsEq
        obtain ⟨images, read, listRelated⟩ := readArray_of_represents subjectRelated
        rw [applyOperation_of_strict_ok firstOrder strict]
        simp only [Ir.Opcode.Preserves] at law
        simp only [Target.runOperation, read]
        refine refines_inPlace heapValid closuresValid ?_ traceRefines
        unfold Relation.Represents
        have denoted := law (α := Value) id images
        simp only [List.map_id] at denoted
        rw [← denoted, representsList_isEmpty elements images listRelated]
        rfl
  case listFirst =>
    cases strict : Source.applyStrict Ir.Opcode.listFirst values with
    | error fault =>
        rw [applyOperation_of_strict_error firstOrder strict]
        exact refines_fault
    | ok produced =>
        obtain ⟨element, elements, valuesEq⟩ := strict_unaryArray (by simp) strict
        subst valuesEq
        obtain ⟨subject, operandsEq, subjectRelated⟩ := representsList_one related
        subst operandsEq
        obtain ⟨images, read, listRelated⟩ := readArray_of_represents subjectRelated
        cases elements with
        | nil => exact absurd strict (by simp [Source.applyStrict])
        | cons head rest =>
            have producedEq : produced = head := by
              simpa only [Source.applyStrict, Except.ok.injEq] using strict.symm
            subst producedEq
            unfold Relation.RepresentsList at listRelated
            obtain ⟨headImage, restImages, imagesEq, headRelated, tailRelated⟩ := listRelated
            subst imagesEq
            rw [applyOperation_of_strict_ok firstOrder strict]
            simp only [Ir.Opcode.Preserves] at law
            simp only [Target.runOperation, read]
            refine refines_inPlace heapValid closuresValid ?_ traceRefines
            have denoted := law (α := Value) id headImage restImages
            simp only [List.map_cons, List.map_id, id_eq] at denoted
            rw [← denoted]
            exact headRelated
  case listRest =>
    cases strict : Source.applyStrict Ir.Opcode.listRest values with
    | error fault =>
        rw [applyOperation_of_strict_error firstOrder strict]
        exact refines_fault
    | ok produced =>
        obtain ⟨element, elements, valuesEq⟩ := strict_unaryArray (by simp) strict
        subst valuesEq
        obtain ⟨subject, operandsEq, subjectRelated⟩ := representsList_one related
        subst operandsEq
        obtain ⟨images, read, listRelated⟩ := readArray_of_represents subjectRelated
        cases elements with
        | nil => exact absurd strict (by simp [Source.applyStrict])
        | cons head rest =>
            have producedEq : produced = .array element rest := by
              simpa only [Source.applyStrict, Except.ok.injEq] using strict.symm
            subst producedEq
            unfold Relation.RepresentsList at listRelated
            obtain ⟨headImage, restImages, imagesEq, headRelated, tailRelated⟩ := listRelated
            subst imagesEq
            have sourceRun := applyOperation_of_strict_ok (program := program) (fuel := fuel)
              (trace := trace) (typeArguments := typeArguments) firstOrder strict
            rw [sourceRun]
            simp only [Ir.Opcode.Preserves] at law
            simp only [Target.runOperation, read]
            have denoted := law (α := Value) id headImage restImages
            simp only [List.map_cons, List.map_id, id_eq] at denoted
            rw [← denoted]
            exact refines_allocateArray heapValid closuresValid tailRelated traceRefines
              (fits element rest trace sourceRun)
  case listReverse =>
    cases strict : Source.applyStrict Ir.Opcode.listReverse values with
    | error fault =>
        rw [applyOperation_of_strict_error firstOrder strict]
        exact refines_fault
    | ok produced =>
        obtain ⟨element, elements, valuesEq⟩ := strict_unaryArray (by simp) strict
        subst valuesEq
        have producedEq : produced = .array element elements.reverse := by
          simpa only [Source.applyStrict, Except.ok.injEq] using strict.symm
        subst producedEq
        obtain ⟨subject, operandsEq, subjectRelated⟩ := representsList_one related
        subst operandsEq
        obtain ⟨images, read, listRelated⟩ := readArray_of_represents subjectRelated
        have sourceRun := applyOperation_of_strict_ok (program := program) (fuel := fuel)
          (trace := trace) (typeArguments := typeArguments) firstOrder strict
        rw [sourceRun]
        simp only [Ir.Opcode.Preserves] at law
        simp only [Target.runOperation, read]
        have denoted := law (α := Value) id images
        simp only [List.map_id] at denoted
        rw [← denoted]
        exact refines_allocateArray heapValid closuresValid
          (represents_reverse elements images listRelated) traceRefines
          (fits element elements.reverse trace sourceRun)
  case listAppend =>
    cases strict : Source.applyStrict Ir.Opcode.listAppend values with
    | error fault =>
        rw [applyOperation_of_strict_error firstOrder strict]
        exact refines_fault
    | ok produced =>
        obtain ⟨firstElement, first, secondElement, second, valuesEq⟩ := strict_listAppend strict
        subst valuesEq
        have producedEq : produced = .array firstElement (first ++ second) := by
          simpa only [Source.applyStrict, Except.ok.injEq] using strict.symm
        subst producedEq
        obtain ⟨firstSubject, secondSubject, operandsEq, firstRelated, secondRelated⟩ :=
          representsList_two related
        subst operandsEq
        obtain ⟨firstImages, firstRead, firstList⟩ := readArray_of_represents firstRelated
        obtain ⟨secondImages, secondRead, secondList⟩ := readArray_of_represents secondRelated
        have sourceRun := applyOperation_of_strict_ok (program := program) (fuel := fuel)
          (trace := trace) (typeArguments := typeArguments) firstOrder strict
        rw [sourceRun]
        simp only [Ir.Opcode.Preserves] at law
        simp only [Target.runOperation, firstRead, secondRead]
        have denoted := law (α := Value) id firstImages secondImages
        simp only [List.map_id] at denoted
        rw [← denoted]
        exact refines_allocateArray heapValid closuresValid
          (represents_append first firstImages second secondImages firstList secondList)
          traceRefines (fits firstElement (first ++ second) trace sourceRun)
  case intAdd =>
    cases strict : Source.applyStrict Ir.Opcode.intAdd values with
    | error fault =>
        rw [applyOperation_of_strict_error firstOrder strict]
        exact refines_fault
    | ok produced =>
        obtain ⟨left, right, valuesEq⟩ := strict_binaryInt (by simp) strict
        subst valuesEq
        have producedEq : produced = .int (left + right) := by
          simpa only [Source.applyStrict, Except.ok.injEq] using strict.symm
        subst producedEq
        obtain ⟨leftImage, rightImage, operandsEq, leftRelated, rightRelated⟩ :=
          representsList_two related
        subst operandsEq
        unfold Relation.Represents at leftRelated rightRelated
        subst leftRelated
        subst rightRelated
        rw [applyOperation_of_strict_ok firstOrder strict]
        simp only [Ir.Opcode.Preserves] at law
        simp only [Target.runOperation]
        refine refines_inPlace heapValid closuresValid ?_ traceRefines
        unfold Relation.Represents
        exact (law left right).symm
  case intSubtract =>
    cases strict : Source.applyStrict Ir.Opcode.intSubtract values with
    | error fault =>
        rw [applyOperation_of_strict_error firstOrder strict]
        exact refines_fault
    | ok produced =>
        obtain ⟨left, right, valuesEq⟩ := strict_binaryInt (by simp) strict
        subst valuesEq
        have producedEq : produced = .int (left - right) := by
          simpa only [Source.applyStrict, Except.ok.injEq] using strict.symm
        subst producedEq
        obtain ⟨leftImage, rightImage, operandsEq, leftRelated, rightRelated⟩ :=
          representsList_two related
        subst operandsEq
        unfold Relation.Represents at leftRelated rightRelated
        subst leftRelated
        subst rightRelated
        rw [applyOperation_of_strict_ok firstOrder strict]
        simp only [Ir.Opcode.Preserves] at law
        simp only [Target.runOperation]
        refine refines_inPlace heapValid closuresValid ?_ traceRefines
        unfold Relation.Represents
        exact (law left right).symm
  case intMultiply =>
    cases strict : Source.applyStrict Ir.Opcode.intMultiply values with
    | error fault =>
        rw [applyOperation_of_strict_error firstOrder strict]
        exact refines_fault
    | ok produced =>
        obtain ⟨left, right, valuesEq⟩ := strict_binaryInt (by simp) strict
        subst valuesEq
        have producedEq : produced = .int (left * right) := by
          simpa only [Source.applyStrict, Except.ok.injEq] using strict.symm
        subst producedEq
        obtain ⟨leftImage, rightImage, operandsEq, leftRelated, rightRelated⟩ :=
          representsList_two related
        subst operandsEq
        unfold Relation.Represents at leftRelated rightRelated
        subst leftRelated
        subst rightRelated
        rw [applyOperation_of_strict_ok firstOrder strict]
        simp only [Ir.Opcode.Preserves] at law
        simp only [Target.runOperation]
        refine refines_inPlace heapValid closuresValid ?_ traceRefines
        unfold Relation.Represents
        exact (law left right).symm
  case intTruncatedDivide =>
    cases strict : Source.applyStrict Ir.Opcode.intTruncatedDivide values with
    | error fault =>
        rw [applyOperation_of_strict_error firstOrder strict]
        exact refines_fault
    | ok produced =>
        obtain ⟨left, right, valuesEq⟩ := strict_binaryInt (by simp) strict
        subst valuesEq
        have producedEq : produced = .int (left.tdiv right) := by
          simpa only [Source.applyStrict, Except.ok.injEq] using strict.symm
        subst producedEq
        obtain ⟨leftImage, rightImage, operandsEq, leftRelated, rightRelated⟩ :=
          representsList_two related
        subst operandsEq
        unfold Relation.Represents at leftRelated rightRelated
        subst leftRelated
        subst rightRelated
        rw [applyOperation_of_strict_ok firstOrder strict]
        simp only [Ir.Opcode.Preserves] at law
        simp only [Target.runOperation]
        refine refines_inPlace heapValid closuresValid ?_ traceRefines
        unfold Relation.Represents
        exact (law left right).symm
  case intTruncatedModulo =>
    cases strict : Source.applyStrict Ir.Opcode.intTruncatedModulo values with
    | error fault =>
        rw [applyOperation_of_strict_error firstOrder strict]
        exact refines_fault
    | ok produced =>
        obtain ⟨left, right, valuesEq⟩ := strict_binaryInt (by simp) strict
        subst valuesEq
        have producedEq : produced = .int (left.tmod right) := by
          simpa only [Source.applyStrict, Except.ok.injEq] using strict.symm
        subst producedEq
        obtain ⟨leftImage, rightImage, operandsEq, leftRelated, rightRelated⟩ :=
          representsList_two related
        subst operandsEq
        unfold Relation.Represents at leftRelated rightRelated
        subst leftRelated
        subst rightRelated
        rw [applyOperation_of_strict_ok firstOrder strict]
        simp only [Ir.Opcode.Preserves] at law
        simp only [Target.runOperation]
        refine refines_inPlace heapValid closuresValid ?_ traceRefines
        unfold Relation.Represents
        exact (law left right).symm
  case intLess =>
    cases strict : Source.applyStrict Ir.Opcode.intLess values with
    | error fault =>
        rw [applyOperation_of_strict_error firstOrder strict]
        exact refines_fault
    | ok produced =>
        obtain ⟨left, right, valuesEq⟩ := strict_binaryInt (by simp) strict
        subst valuesEq
        have producedEq : produced = .boolean (decide (left < right)) := by
          simpa only [Source.applyStrict, Except.ok.injEq] using strict.symm
        subst producedEq
        obtain ⟨leftImage, rightImage, operandsEq, leftRelated, rightRelated⟩ :=
          representsList_two related
        subst operandsEq
        unfold Relation.Represents at leftRelated rightRelated
        subst leftRelated
        subst rightRelated
        rw [applyOperation_of_strict_ok firstOrder strict]
        simp only [Ir.Opcode.Preserves] at law
        simp only [Target.runOperation]
        refine refines_inPlace heapValid closuresValid ?_ traceRefines
        unfold Relation.Represents
        exact (law left right).symm
  case intLessOrEqual =>
    cases strict : Source.applyStrict Ir.Opcode.intLessOrEqual values with
    | error fault =>
        rw [applyOperation_of_strict_error firstOrder strict]
        exact refines_fault
    | ok produced =>
        obtain ⟨left, right, valuesEq⟩ := strict_binaryInt (by simp) strict
        subst valuesEq
        have producedEq : produced = .boolean (decide (left ≤ right)) := by
          simpa only [Source.applyStrict, Except.ok.injEq] using strict.symm
        subst producedEq
        obtain ⟨leftImage, rightImage, operandsEq, leftRelated, rightRelated⟩ :=
          representsList_two related
        subst operandsEq
        unfold Relation.Represents at leftRelated rightRelated
        subst leftRelated
        subst rightRelated
        rw [applyOperation_of_strict_ok firstOrder strict]
        simp only [Ir.Opcode.Preserves] at law
        simp only [Target.runOperation]
        refine refines_inPlace heapValid closuresValid ?_ traceRefines
        unfold Relation.Represents
        exact (law left right).symm
  case intEquals =>
    cases strict : Source.applyStrict Ir.Opcode.intEquals values with
    | error fault =>
        rw [applyOperation_of_strict_error firstOrder strict]
        exact refines_fault
    | ok produced =>
        obtain ⟨left, right, valuesEq⟩ := strict_binaryInt (by simp) strict
        subst valuesEq
        have producedEq : produced = .boolean (left == right) := by
          simpa only [Source.applyStrict, Except.ok.injEq] using strict.symm
        subst producedEq
        obtain ⟨leftImage, rightImage, operandsEq, leftRelated, rightRelated⟩ :=
          representsList_two related
        subst operandsEq
        unfold Relation.Represents at leftRelated rightRelated
        subst leftRelated
        subst rightRelated
        rw [applyOperation_of_strict_ok firstOrder strict]
        simp only [Ir.Opcode.Preserves] at law
        simp only [Target.runOperation]
        refine refines_inPlace heapValid closuresValid ?_ traceRefines
        unfold Relation.Represents
        exact (law left right).symm
  case intNegate =>
    cases strict : Source.applyStrict Ir.Opcode.intNegate values with
    | error fault =>
        rw [applyOperation_of_strict_error firstOrder strict]
        exact refines_fault
    | ok produced =>
        obtain ⟨operand, valuesEq⟩ := strict_unaryInt (by simp) strict
        subst valuesEq
        have producedEq : produced = .int (-operand) := by
          simpa only [Source.applyStrict, Except.ok.injEq] using strict.symm
        subst producedEq
        obtain ⟨image, operandsEq, operandRelated⟩ := representsList_one related
        subst operandsEq
        unfold Relation.Represents at operandRelated
        subst operandRelated
        rw [applyOperation_of_strict_ok firstOrder strict]
        simp only [Ir.Opcode.Preserves] at law
        simp only [Target.runOperation]
        refine refines_inPlace heapValid closuresValid ?_ traceRefines
        unfold Relation.Represents
        exact (law operand).symm
  case intToNat =>
    cases strict : Source.applyStrict Ir.Opcode.intToNat values with
    | error fault =>
        rw [applyOperation_of_strict_error firstOrder strict]
        exact refines_fault
    | ok produced =>
        obtain ⟨operand, valuesEq⟩ := strict_unaryInt (by simp) strict
        subst valuesEq
        have producedEq : produced = .nat operand.toNat := by
          simpa only [Source.applyStrict, Except.ok.injEq] using strict.symm
        subst producedEq
        obtain ⟨image, operandsEq, operandRelated⟩ := representsList_one related
        subst operandsEq
        unfold Relation.Represents at operandRelated
        subst operandRelated
        rw [applyOperation_of_strict_ok firstOrder strict]
        simp only [Ir.Opcode.Preserves] at law
        simp only [Target.runOperation]
        refine refines_inPlace heapValid closuresValid ?_ traceRefines
        unfold Relation.Represents
        exact (law operand).symm
  case intOfNat =>
    cases strict : Source.applyStrict Ir.Opcode.intOfNat values with
    | error fault =>
        rw [applyOperation_of_strict_error firstOrder strict]
        exact refines_fault
    | ok produced =>
        obtain ⟨operand, valuesEq⟩ := strict_unaryNat (by simp) strict
        subst valuesEq
        have producedEq : produced = .int (Int.ofNat operand) := by
          simpa only [Source.applyStrict, Except.ok.injEq] using strict.symm
        subst producedEq
        obtain ⟨image, operandsEq, operandRelated⟩ := representsList_one related
        subst operandsEq
        unfold Relation.Represents at operandRelated
        subst operandRelated
        rw [applyOperation_of_strict_ok firstOrder strict]
        simp only [Ir.Opcode.Preserves] at law
        simp only [Target.runOperation]
        refine refines_inPlace heapValid closuresValid ?_ traceRefines
        unfold Relation.Represents
        exact (law operand).symm
  case charOfNat =>
    cases strict : Source.applyStrict Ir.Opcode.charOfNat values with
    | error fault =>
        rw [applyOperation_of_strict_error firstOrder strict]
        exact refines_fault
    | ok produced =>
        obtain ⟨operand, valuesEq⟩ := strict_unaryNat (by simp) strict
        subst valuesEq
        have producedEq : produced = .char (Char.ofNat operand) := by
          simpa only [Source.applyStrict, Except.ok.injEq] using strict.symm
        subst producedEq
        obtain ⟨image, operandsEq, operandRelated⟩ := representsList_one related
        subst operandsEq
        unfold Relation.Represents at operandRelated
        subst operandRelated
        rw [applyOperation_of_strict_ok firstOrder strict]
        simp only [Ir.Opcode.Preserves] at law
        simp only [Target.runOperation]
        refine refines_inPlace heapValid closuresValid ?_ traceRefines
        unfold Relation.Represents
        exact (law operand).symm
  case charToNat =>
    cases strict : Source.applyStrict Ir.Opcode.charToNat values with
    | error fault =>
        rw [applyOperation_of_strict_error firstOrder strict]
        exact refines_fault
    | ok produced =>
        obtain ⟨character, valuesEq⟩ := strict_unaryChar (by simp) strict
        subst valuesEq
        have producedEq : produced = .nat character.toNat := by
          simpa only [Source.applyStrict, Except.ok.injEq] using strict.symm
        subst producedEq
        obtain ⟨image, operandsEq, operandRelated⟩ := representsList_one related
        subst operandsEq
        unfold Relation.Represents at operandRelated
        subst operandRelated
        rw [applyOperation_of_strict_ok firstOrder strict]
        simp only [Ir.Opcode.Preserves] at law
        simp only [Target.runOperation]
        refine refines_inPlace heapValid closuresValid ?_ traceRefines
        unfold Relation.Represents
        exact (law character).symm
  case stringSingleton =>
    cases strict : Source.applyStrict Ir.Opcode.stringSingleton values with
    | error fault =>
        rw [applyOperation_of_strict_error firstOrder strict]
        exact refines_fault
    | ok produced =>
        obtain ⟨character, valuesEq⟩ := strict_unaryChar (by simp) strict
        subst valuesEq
        have producedEq : produced = .string (String.singleton character) := by
          simpa only [Source.applyStrict, Except.ok.injEq] using strict.symm
        subst producedEq
        obtain ⟨image, operandsEq, operandRelated⟩ := representsList_one related
        subst operandsEq
        unfold Relation.Represents at operandRelated
        subst operandRelated
        rw [applyOperation_of_strict_ok firstOrder strict]
        simp only [Ir.Opcode.Preserves] at law
        simp only [Target.runOperation]
        refine refines_inPlace heapValid closuresValid ?_ traceRefines
        unfold Relation.Represents
        exact (law character).symm
  case charEquals =>
    cases strict : Source.applyStrict Ir.Opcode.charEquals values with
    | error fault =>
        rw [applyOperation_of_strict_error firstOrder strict]
        exact refines_fault
    | ok produced =>
        obtain ⟨left, right, valuesEq⟩ := strict_binaryChar (by simp) strict
        subst valuesEq
        have producedEq : produced = .boolean (left == right) := by
          simpa only [Source.applyStrict, Except.ok.injEq] using strict.symm
        subst producedEq
        obtain ⟨leftImage, rightImage, operandsEq, leftRelated, rightRelated⟩ :=
          representsList_two related
        subst operandsEq
        unfold Relation.Represents at leftRelated rightRelated
        subst leftRelated
        subst rightRelated
        rw [applyOperation_of_strict_ok firstOrder strict]
        simp only [Ir.Opcode.Preserves] at law
        simp only [Target.runOperation]
        refine refines_inPlace heapValid closuresValid ?_ traceRefines
        unfold Relation.Represents
        exact (law left right).symm
  case charLess =>
    cases strict : Source.applyStrict Ir.Opcode.charLess values with
    | error fault =>
        rw [applyOperation_of_strict_error firstOrder strict]
        exact refines_fault
    | ok produced =>
        obtain ⟨left, right, valuesEq⟩ := strict_binaryChar (by simp) strict
        subst valuesEq
        have producedEq : produced = .boolean (decide (left < right)) := by
          simpa only [Source.applyStrict, Except.ok.injEq] using strict.symm
        subst producedEq
        obtain ⟨leftImage, rightImage, operandsEq, leftRelated, rightRelated⟩ :=
          representsList_two related
        subst operandsEq
        unfold Relation.Represents at leftRelated rightRelated
        subst leftRelated
        subst rightRelated
        rw [applyOperation_of_strict_ok firstOrder strict]
        simp only [Ir.Opcode.Preserves] at law
        simp only [Target.runOperation]
        refine refines_inPlace heapValid closuresValid ?_ traceRefines
        unfold Relation.Represents
        exact (law left right).symm
  case stringLength =>
    cases strict : Source.applyStrict Ir.Opcode.stringLength values with
    | error fault =>
        rw [applyOperation_of_strict_error firstOrder strict]
        exact refines_fault
    | ok produced =>
        obtain ⟨operand, valuesEq⟩ := strict_unaryString (by simp) strict
        subst valuesEq
        have producedEq : produced = .nat operand.length := by
          simpa only [Source.applyStrict, Except.ok.injEq] using strict.symm
        subst producedEq
        obtain ⟨image, operandsEq, operandRelated⟩ := representsList_one related
        subst operandsEq
        unfold Relation.Represents at operandRelated
        subst operandRelated
        rw [applyOperation_of_strict_ok firstOrder strict]
        simp only [Ir.Opcode.Preserves] at law
        simp only [Target.runOperation]
        refine refines_inPlace heapValid closuresValid ?_ traceRefines
        unfold Relation.Represents
        exact (law operand).symm
  case stringIsEmpty =>
    cases strict : Source.applyStrict Ir.Opcode.stringIsEmpty values with
    | error fault =>
        rw [applyOperation_of_strict_error firstOrder strict]
        exact refines_fault
    | ok produced =>
        obtain ⟨operand, valuesEq⟩ := strict_unaryString (by simp) strict
        subst valuesEq
        have producedEq : produced = .boolean operand.isEmpty := by
          simpa only [Source.applyStrict, Except.ok.injEq] using strict.symm
        subst producedEq
        obtain ⟨image, operandsEq, operandRelated⟩ := representsList_one related
        subst operandsEq
        unfold Relation.Represents at operandRelated
        subst operandRelated
        rw [applyOperation_of_strict_ok firstOrder strict]
        simp only [Ir.Opcode.Preserves] at law
        simp only [Target.runOperation]
        refine refines_inPlace heapValid closuresValid ?_ traceRefines
        unfold Relation.Represents
        exact (law operand).symm
  case stringPush =>
    cases strict : Source.applyStrict Ir.Opcode.stringPush values with
    | error fault =>
        rw [applyOperation_of_strict_error firstOrder strict]
        exact refines_fault
    | ok produced =>
        obtain ⟨operand, character, valuesEq⟩ := strict_stringPush strict
        subst valuesEq
        have producedEq : produced = .string (operand.push character) := by
          simpa only [Source.applyStrict, Except.ok.injEq] using strict.symm
        subst producedEq
        obtain ⟨operandImage, characterImage, operandsEq, operandRelated, characterRelated⟩ :=
          representsList_two related
        subst operandsEq
        unfold Relation.Represents at operandRelated characterRelated
        subst operandRelated
        subst characterRelated
        rw [applyOperation_of_strict_ok firstOrder strict]
        simp only [Ir.Opcode.Preserves] at law
        simp only [Target.runOperation]
        refine refines_inPlace heapValid closuresValid ?_ traceRefines
        unfold Relation.Represents
        exact (law operand character).symm
  case stringToList =>
    cases strict : Source.applyStrict Ir.Opcode.stringToList values with
    | error fault =>
        rw [applyOperation_of_strict_error firstOrder strict]
        exact refines_fault
    | ok produced =>
        obtain ⟨operand, valuesEq⟩ := strict_unaryString (by simp) strict
        subst valuesEq
        have producedEq : produced = .array .char (operand.toList.map Source.Value.char) := by
          simpa only [Source.applyStrict, Except.ok.injEq] using strict.symm
        subst producedEq
        obtain ⟨image, operandsEq, operandRelated⟩ := representsList_one related
        subst operandsEq
        unfold Relation.Represents at operandRelated
        subst operandRelated
        have sourceRun := applyOperation_of_strict_ok (program := program) (fuel := fuel)
          (trace := trace) (typeArguments := typeArguments) firstOrder strict
        rw [sourceRun]
        simp only [Ir.Opcode.Preserves] at law
        simp only [Target.runOperation]
        have denoted := law operand
        simp only [Encode.string, Encode.jsString] at denoted
        rw [← denoted]
        exact refines_allocateArray heapValid closuresValid (represents_charList operand.toList)
          traceRefines (fits .char (operand.toList.map Source.Value.char) trace sourceRun)
  case stringOfList =>
    cases strict : Source.applyStrict Ir.Opcode.stringOfList values with
    | error fault =>
        rw [applyOperation_of_strict_error firstOrder strict]
        exact refines_fault
    | ok produced =>
        obtain ⟨element, characters, valuesEq, producedEq⟩ := strict_stringOfList strict
        subst valuesEq
        subst producedEq
        obtain ⟨subject, operandsEq, subjectRelated⟩ := representsList_one related
        subst operandsEq
        obtain ⟨images, read, listRelated⟩ := readArray_of_represents subjectRelated
        have imagesEq := representsList_charList characters images listRelated
        subst imagesEq
        rw [applyOperation_of_strict_ok firstOrder strict]
        simp only [Ir.Opcode.Preserves] at law
        simp only [Target.runOperation, read]
        refine refines_inPlace heapValid closuresValid ?_ traceRefines
        unfold Relation.Represents
        exact (law characters).symm
  case arraySize =>
    cases strict : Source.applyStrict Ir.Opcode.arraySize values with
    | error fault =>
        rw [applyOperation_of_strict_error firstOrder strict]
        exact refines_fault
    | ok produced =>
        obtain ⟨element, elements, valuesEq⟩ := strict_unaryArrayOf (by simp) strict
        subst valuesEq
        have producedEq : produced = .nat elements.length := by
          simpa only [Source.applyStrict, Except.ok.injEq] using strict.symm
        subst producedEq
        obtain ⟨subject, operandsEq, subjectRelated⟩ := representsList_one related
        subst operandsEq
        obtain ⟨images, read, listRelated⟩ := readArray_of_represents subjectRelated
        rw [applyOperation_of_strict_ok firstOrder strict]
        simp only [Ir.Opcode.Preserves] at law
        simp only [Target.runOperation, read]
        refine refines_inPlace heapValid closuresValid ?_ traceRefines
        unfold Relation.Represents
        have denoted := law (α := Value) id images
        simp only [List.map_id] at denoted
        rw [← denoted, representsList_length elements images listRelated]
        rfl
  case arrayIsEmpty =>
    cases strict : Source.applyStrict Ir.Opcode.arrayIsEmpty values with
    | error fault =>
        rw [applyOperation_of_strict_error firstOrder strict]
        exact refines_fault
    | ok produced =>
        obtain ⟨element, elements, valuesEq⟩ := strict_unaryArrayOf (by simp) strict
        subst valuesEq
        have producedEq : produced = .boolean elements.isEmpty := by
          simpa only [Source.applyStrict, Except.ok.injEq] using strict.symm
        subst producedEq
        obtain ⟨subject, operandsEq, subjectRelated⟩ := representsList_one related
        subst operandsEq
        obtain ⟨images, read, listRelated⟩ := readArray_of_represents subjectRelated
        rw [applyOperation_of_strict_ok firstOrder strict]
        simp only [Ir.Opcode.Preserves] at law
        simp only [Target.runOperation, read]
        refine refines_inPlace heapValid closuresValid ?_ traceRefines
        unfold Relation.Represents
        have denoted := law (α := Value) id images
        simp only [List.map_id] at denoted
        rw [← denoted, representsList_isEmpty elements images listRelated]
        rfl
  case arrayReverse =>
    cases strict : Source.applyStrict Ir.Opcode.arrayReverse values with
    | error fault =>
        rw [applyOperation_of_strict_error firstOrder strict]
        exact refines_fault
    | ok produced =>
        obtain ⟨element, elements, valuesEq⟩ := strict_unaryArrayOf (by simp) strict
        subst valuesEq
        have producedEq : produced = .array element elements.reverse := by
          simpa only [Source.applyStrict, Except.ok.injEq] using strict.symm
        subst producedEq
        obtain ⟨subject, operandsEq, subjectRelated⟩ := representsList_one related
        subst operandsEq
        obtain ⟨images, read, listRelated⟩ := readArray_of_represents subjectRelated
        have sourceRun := applyOperation_of_strict_ok (program := program) (fuel := fuel)
          (trace := trace) (typeArguments := typeArguments) firstOrder strict
        rw [sourceRun]
        simp only [Ir.Opcode.Preserves] at law
        simp only [Target.runOperation, read]
        have denoted := law (α := Value) id images
        simp only [List.map_id] at denoted
        rw [← denoted]
        exact refines_allocateArray heapValid closuresValid
          (represents_reverse elements images listRelated) traceRefines
          (fits element elements.reverse trace sourceRun)
  case arrayPush =>
    cases strict : Source.applyStrict Ir.Opcode.arrayPush values with
    | error fault =>
        rw [applyOperation_of_strict_error firstOrder strict]
        exact refines_fault
    | ok produced =>
        obtain ⟨element, elements, pushed, valuesEq⟩ := strict_arrayPush strict
        subst valuesEq
        have producedEq : produced = .array element (elements ++ [pushed]) := by
          simpa only [Source.applyStrict, Except.ok.injEq] using strict.symm
        subst producedEq
        obtain ⟨subject, pushedImage, operandsEq, subjectRelated, pushedRelated⟩ :=
          representsList_two related
        subst operandsEq
        obtain ⟨images, read, listRelated⟩ := readArray_of_represents subjectRelated
        have sourceRun := applyOperation_of_strict_ok (program := program) (fuel := fuel)
          (trace := trace) (typeArguments := typeArguments) firstOrder strict
        rw [sourceRun]
        simp only [Ir.Opcode.Preserves] at law
        simp only [Target.runOperation, read]
        have denoted := law (α := Value) id images pushedImage
        simp only [List.map_id, List.map_append, List.map_cons, List.map_nil, id_eq] at denoted
        rw [← denoted]
        exact refines_allocateArray heapValid closuresValid
          (represents_append elements images [pushed] [pushedImage] listRelated
            (represents_singleton pushedRelated))
          traceRefines (fits element (elements ++ [pushed]) trace sourceRun)
  case arrayAppend =>
    cases strict : Source.applyStrict Ir.Opcode.arrayAppend values with
    | error fault =>
        rw [applyOperation_of_strict_error firstOrder strict]
        exact refines_fault
    | ok produced =>
        obtain ⟨firstElement, first, secondElement, second, valuesEq⟩ := strict_arrayAppend strict
        subst valuesEq
        have producedEq : produced = .array firstElement (first ++ second) := by
          simpa only [Source.applyStrict, Except.ok.injEq] using strict.symm
        subst producedEq
        obtain ⟨firstSubject, secondSubject, operandsEq, firstRelated, secondRelated⟩ :=
          representsList_two related
        subst operandsEq
        obtain ⟨firstImages, firstRead, firstList⟩ := readArray_of_represents firstRelated
        obtain ⟨secondImages, secondRead, secondList⟩ := readArray_of_represents secondRelated
        have sourceRun := applyOperation_of_strict_ok (program := program) (fuel := fuel)
          (trace := trace) (typeArguments := typeArguments) firstOrder strict
        rw [sourceRun]
        simp only [Ir.Opcode.Preserves] at law
        simp only [Target.runOperation, firstRead, secondRead]
        have denoted := law (α := Value) id firstImages secondImages
        simp only [List.map_id] at denoted
        rw [← denoted]
        exact refines_allocateArray heapValid closuresValid
          (represents_append first firstImages second secondImages firstList secondList)
          traceRefines (fits firstElement (first ++ second) trace sourceRun)
  case arrayToList =>
    cases strict : Source.applyStrict Ir.Opcode.arrayToList values with
    | error fault =>
        rw [applyOperation_of_strict_error firstOrder strict]
        exact refines_fault
    | ok produced =>
        obtain ⟨element, elements, valuesEq⟩ := strict_unaryArrayOf (by simp) strict
        subst valuesEq
        have producedEq : produced = .array element elements := by
          simpa only [Source.applyStrict, Except.ok.injEq] using strict.symm
        subst producedEq
        obtain ⟨subject, operandsEq, subjectRelated⟩ := representsList_one related
        subst operandsEq
        rw [applyOperation_of_strict_ok firstOrder strict]
        simp only [Ir.Opcode.Preserves] at law
        simp only [Target.runOperation]
        rw [← law subject]
        exact refines_inPlace heapValid closuresValid subjectRelated traceRefines
  case arrayOfList =>
    cases strict : Source.applyStrict Ir.Opcode.arrayOfList values with
    | error fault =>
        rw [applyOperation_of_strict_error firstOrder strict]
        exact refines_fault
    | ok produced =>
        obtain ⟨element, elements, valuesEq⟩ := strict_unaryArrayOf (by simp) strict
        subst valuesEq
        have producedEq : produced = .array element elements := by
          simpa only [Source.applyStrict, Except.ok.injEq] using strict.symm
        subst producedEq
        obtain ⟨subject, operandsEq, subjectRelated⟩ := representsList_one related
        subst operandsEq
        rw [applyOperation_of_strict_ok firstOrder strict]
        simp only [Ir.Opcode.Preserves] at law
        simp only [Target.runOperation]
        rw [← law subject]
        exact refines_inPlace heapValid closuresValid subjectRelated traceRefines
  case listHead =>
    cases strict : Source.applyStrict Ir.Opcode.listHead values with
    | error fault =>
        rw [applyOperation_of_strict_error firstOrder strict]
        exact refines_fault
    | ok produced =>
        obtain ⟨element, elements, valuesEq⟩ := strict_unaryArray (by simp) strict
        subst valuesEq
        obtain ⟨subject, operandsEq, subjectRelated⟩ := representsList_one related
        subst operandsEq
        obtain ⟨images, read, listRelated⟩ := readArray_of_represents subjectRelated
        have declared : program.constructorsOf (.option element)
            = some [⟨"none", []⟩, ⟨"some", [⟨"value", element⟩]⟩] := rfl
        have carries : Ir.allNullary [⟨"none", []⟩, ⟨"some", [⟨"value", element⟩]⟩] = false := by
          simp [Ir.allNullary]
        simp only [Ir.Opcode.Preserves] at law
        cases elements with
        | nil =>
            have producedEq : produced = .variant (.option element) "none" [] := by
              simpa only [Source.applyStrict, Except.ok.injEq] using strict.symm
            subst producedEq
            unfold Relation.RepresentsList at listRelated
            subst listRelated
            have denoted : runtime.listHead ([] : List Value) = OptionImage.absent := by
              simpa [Encode.option] using (law (α := Value) id ([] : List Value)).symm
            rw [applyOperation_of_strict_ok firstOrder strict]
            simp only [Target.runOperation, read, denoted, Target.optionValue]
            obtain ⟨ref, final, allocated, traceEq, _, extension, finalValid, _, shape⟩ :=
              Allocation.allocateLiteral_shape state
                [("kind", Value.primitive (.string (JSString.ofLeanString "none")))]
                heapValid closuresValid
                (by
                  intro entry member
                  simp only [List.mem_singleton] at member
                  subst member
                  show Ir.ValidKey "kind"
                  decide)
                (by simp)
                (by
                  intro entry member
                  simp only [List.mem_singleton] at member
                  subst member
                  rfl)
            rw [allocated]
            refine refines_value extension finalValid ?_ ?_
            · unfold Relation.Represents
              refine ⟨_, declared, ⟨"none", []⟩, rfl, ?_⟩
              rw [if_neg (by simp [carries])]
              refine ⟨ref, [], rfl, ?_, shape⟩
              unfold Relation.RepresentsArguments
              exact ⟨rfl, rfl⟩
            · rw [traceEq]
              exact Relation.RefinesTrace.stable extension trace state.trace traceRefines
        | cons head rest =>
            have producedEq : produced = .variant (.option element) "some" [head] := by
              simpa only [Source.applyStrict, Except.ok.injEq] using strict.symm
            subst producedEq
            unfold Relation.RepresentsList at listRelated
            obtain ⟨headImage, restImages, imagesEq, headRelated, tailRelated⟩ := listRelated
            subst imagesEq
            have denoted : runtime.listHead (headImage :: restImages)
                = OptionImage.present headImage := by
              simpa [Encode.option] using (law (α := Value) id (headImage :: restImages)).symm
            rw [applyOperation_of_strict_ok firstOrder strict]
            simp only [Target.runOperation, read, denoted, Target.optionValue]
            obtain ⟨ref, final, allocated, traceEq, _, extension, finalValid, _, shape⟩ :=
              Allocation.allocateLiteral_shape state
                [("kind", Value.primitive (.string (JSString.ofLeanString "some"))),
                  ("value", headImage)]
                heapValid closuresValid
                (by
                  intro entry member
                  rcases List.mem_cons.mp member with rfl | tail
                  · show Ir.ValidKey "kind"
                    decide
                  · simp only [List.mem_singleton] at tail
                    subst tail
                    show Ir.ValidKey "value"
                    decide)
                (by simp)
                (by
                  intro entry member
                  rcases List.mem_cons.mp member with rfl | tail
                  · rfl
                  · simp only [List.mem_singleton] at tail
                    subst tail
                    exact valueValid_of_represents head headImage headRelated)
            rw [allocated]
            refine refines_value extension finalValid ?_ ?_
            · unfold Relation.Represents
              refine ⟨_, declared, ⟨"some", [⟨"value", element⟩]⟩, rfl, ?_⟩
              rw [if_neg (by simp [carries])]
              refine ⟨ref, [("value", headImage)], rfl, ?_, shape⟩
              unfold Relation.RepresentsArguments
              refine ⟨⟨"value", element⟩, [], headImage, [], rfl, rfl,
                Relation.Represents.stable extension head headImage headRelated, ?_⟩
              unfold Relation.RepresentsArguments
              exact ⟨rfl, rfl⟩
            · rw [traceEq]
              exact Relation.RefinesTrace.stable extension trace state.trace traceRefines

/-! ### The six higher-order opcodes

Each one accepts exactly one operand list: a callback and an array, in the order Coverage v5's
emitter writes them. Every other operand list is refused, and a refused source run claims nothing of
the target, so each inversion answers either the finished refinement or the operand shape the loop
runs on.
-/

/-- `list.map` takes the callback first and the subject second. -/
theorem listMap_operands {program : Ir.Program} {target : Target.Program} {runtime : Runtime}
    {fuel : Nat} {typeArguments : List Ir.Ty} {values : List Source.Value} {operands : List Value}
    {trace : Source.Trace} {state : Target.State} :
    Relation.Refines program state
        (Source.applyOperation program fuel trace .listMap typeArguments values)
        (Target.runOperation target runtime fuel state .listMap operands) ∨
      ∃ captured parameters body element elements,
        values = [.closure captured parameters body, .array element elements] := by
  match values with
  | [] => exact Or.inl (by simp only [Source.applyOperation, Source.applyStrict]; exact refines_fault)
  | [_] => exact Or.inl (by simp only [Source.applyOperation, Source.applyStrict]; exact refines_fault)
  | _ :: _ :: _ :: _ =>
      exact Or.inl (by simp only [Source.applyOperation, Source.applyStrict]; exact refines_fault)
  | [.closure captured parameters body, .array element elements] =>
      exact Or.inr ⟨captured, parameters, body, element, elements, rfl⟩
  | [.closure _ _ _, .boolean _] | [.closure _ _ _, .nat _] | [.closure _ _ _, .int _]
  | [.closure _ _ _, .string _] | [.closure _ _ _, .char _] | [.closure _ _ _, .record _ _]
  | [.closure _ _ _, .variant _ _ _] | [.closure _ _ _, .closure _ _ _]
  | [.boolean _, _] | [.nat _, _] | [.int _, _] | [.string _, _] | [.char _, _]
  | [.record _ _, _] | [.array _ _, _] | [.variant _ _ _, _] =>
      exact Or.inl (by simp only [Source.applyOperation]; exact refines_fault)

/-- `list.filter` takes the callback first and the subject second. -/
theorem listFilter_operands {program : Ir.Program} {target : Target.Program} {runtime : Runtime}
    {fuel : Nat} {typeArguments : List Ir.Ty} {values : List Source.Value} {operands : List Value}
    {trace : Source.Trace} {state : Target.State} :
    Relation.Refines program state
        (Source.applyOperation program fuel trace .listFilter typeArguments values)
        (Target.runOperation target runtime fuel state .listFilter operands) ∨
      ∃ captured parameters body element elements,
        values = [.closure captured parameters body, .array element elements] := by
  match values with
  | [] => exact Or.inl (by simp only [Source.applyOperation, Source.applyStrict]; exact refines_fault)
  | [_] => exact Or.inl (by simp only [Source.applyOperation, Source.applyStrict]; exact refines_fault)
  | _ :: _ :: _ :: _ =>
      exact Or.inl (by simp only [Source.applyOperation, Source.applyStrict]; exact refines_fault)
  | [.closure captured parameters body, .array element elements] =>
      exact Or.inr ⟨captured, parameters, body, element, elements, rfl⟩
  | [.closure _ _ _, .boolean _] | [.closure _ _ _, .nat _] | [.closure _ _ _, .int _]
  | [.closure _ _ _, .string _] | [.closure _ _ _, .char _] | [.closure _ _ _, .record _ _]
  | [.closure _ _ _, .variant _ _ _] | [.closure _ _ _, .closure _ _ _]
  | [.boolean _, _] | [.nat _, _] | [.int _, _] | [.string _, _] | [.char _, _]
  | [.record _ _, _] | [.array _ _, _] | [.variant _ _ _, _] =>
      exact Or.inl (by simp only [Source.applyOperation]; exact refines_fault)

/-- `list.any` takes the subject first and the callback second. -/
theorem listAny_operands {program : Ir.Program} {target : Target.Program} {runtime : Runtime}
    {fuel : Nat} {typeArguments : List Ir.Ty} {values : List Source.Value} {operands : List Value}
    {trace : Source.Trace} {state : Target.State} :
    Relation.Refines program state
        (Source.applyOperation program fuel trace .listAny typeArguments values)
        (Target.runOperation target runtime fuel state .listAny operands) ∨
      ∃ element elements captured parameters body,
        values = [.array element elements, .closure captured parameters body] := by
  match values with
  | [] => exact Or.inl (by simp only [Source.applyOperation, Source.applyStrict]; exact refines_fault)
  | [_] => exact Or.inl (by simp only [Source.applyOperation, Source.applyStrict]; exact refines_fault)
  | _ :: _ :: _ :: _ =>
      exact Or.inl (by simp only [Source.applyOperation, Source.applyStrict]; exact refines_fault)
  | [.array element elements, .closure captured parameters body] =>
      exact Or.inr ⟨element, elements, captured, parameters, body, rfl⟩
  | [.array _ _, .boolean _] | [.array _ _, .nat _] | [.array _ _, .int _]
  | [.array _ _, .string _] | [.array _ _, .char _] | [.array _ _, .record _ _]
  | [.array _ _, .variant _ _ _] | [.array _ _, .array _ _]
  | [.boolean _, _] | [.nat _, _] | [.int _, _] | [.string _, _] | [.char _, _]
  | [.record _ _, _] | [.closure _ _ _, _]
  | [.variant _ _ _, _] =>
      exact Or.inl (by simp only [Source.applyOperation]; exact refines_fault)

/-- `list.all` takes the subject first and the callback second. -/
theorem listAll_operands {program : Ir.Program} {target : Target.Program} {runtime : Runtime}
    {fuel : Nat} {typeArguments : List Ir.Ty} {values : List Source.Value} {operands : List Value}
    {trace : Source.Trace} {state : Target.State} :
    Relation.Refines program state
        (Source.applyOperation program fuel trace .listAll typeArguments values)
        (Target.runOperation target runtime fuel state .listAll operands) ∨
      ∃ element elements captured parameters body,
        values = [.array element elements, .closure captured parameters body] := by
  match values with
  | [] => exact Or.inl (by simp only [Source.applyOperation, Source.applyStrict]; exact refines_fault)
  | [_] => exact Or.inl (by simp only [Source.applyOperation, Source.applyStrict]; exact refines_fault)
  | _ :: _ :: _ :: _ =>
      exact Or.inl (by simp only [Source.applyOperation, Source.applyStrict]; exact refines_fault)
  | [.array element elements, .closure captured parameters body] =>
      exact Or.inr ⟨element, elements, captured, parameters, body, rfl⟩
  | [.array _ _, .boolean _] | [.array _ _, .nat _] | [.array _ _, .int _]
  | [.array _ _, .string _] | [.array _ _, .char _] | [.array _ _, .record _ _]
  | [.array _ _, .variant _ _ _] | [.array _ _, .array _ _]
  | [.boolean _, _] | [.nat _, _] | [.int _, _] | [.string _, _] | [.char _, _]
  | [.record _ _, _] | [.closure _ _ _, _]
  | [.variant _ _ _, _] =>
      exact Or.inl (by simp only [Source.applyOperation]; exact refines_fault)

/-- `list.foldLeft` takes the step, the initial accumulator, then the subject. -/
theorem listFoldLeft_operands {program : Ir.Program} {target : Target.Program} {runtime : Runtime}
    {fuel : Nat} {typeArguments : List Ir.Ty} {values : List Source.Value} {operands : List Value}
    {trace : Source.Trace} {state : Target.State} :
    Relation.Refines program state
        (Source.applyOperation program fuel trace .listFoldLeft typeArguments values)
        (Target.runOperation target runtime fuel state .listFoldLeft operands) ∨
      ∃ captured parameters body initial element elements,
        values = [.closure captured parameters body, initial, .array element elements] := by
  match values with
  | [] => exact Or.inl (by simp only [Source.applyOperation, Source.applyStrict]; exact refines_fault)
  | [_] => exact Or.inl (by simp only [Source.applyOperation, Source.applyStrict]; exact refines_fault)
  | [_, _] => exact Or.inl (by simp only [Source.applyOperation, Source.applyStrict]; exact refines_fault)
  | _ :: _ :: _ :: _ :: _ =>
      exact Or.inl (by simp only [Source.applyOperation, Source.applyStrict]; exact refines_fault)
  | [.closure captured parameters body, initial, .array element elements] =>
      exact Or.inr ⟨captured, parameters, body, initial, element, elements, rfl⟩
  | [.closure _ _ _, _, .boolean _] | [.closure _ _ _, _, .nat _] | [.closure _ _ _, _, .int _]
  | [.closure _ _ _, _, .string _] | [.closure _ _ _, _, .char _]
  | [.closure _ _ _, _, .record _ _] | [.closure _ _ _, _, .variant _ _ _]
  | [.closure _ _ _, _, .closure _ _ _]
  | [.boolean _, _, _] | [.nat _, _, _] | [.int _, _, _] | [.string _, _, _] | [.char _, _, _]
  | [.record _ _, _, _] | [.array _ _, _, _] | [.variant _ _ _, _, _] =>
      exact Or.inl (by simp only [Source.applyOperation]; exact refines_fault)

/-- `list.foldRight` takes the step, the initial accumulator, then the subject. -/
theorem listFoldRight_operands {program : Ir.Program} {target : Target.Program} {runtime : Runtime}
    {fuel : Nat} {typeArguments : List Ir.Ty} {values : List Source.Value} {operands : List Value}
    {trace : Source.Trace} {state : Target.State} :
    Relation.Refines program state
        (Source.applyOperation program fuel trace .listFoldRight typeArguments values)
        (Target.runOperation target runtime fuel state .listFoldRight operands) ∨
      ∃ captured parameters body initial element elements,
        values = [.closure captured parameters body, initial, .array element elements] := by
  match values with
  | [] => exact Or.inl (by simp only [Source.applyOperation, Source.applyStrict]; exact refines_fault)
  | [_] => exact Or.inl (by simp only [Source.applyOperation, Source.applyStrict]; exact refines_fault)
  | [_, _] => exact Or.inl (by simp only [Source.applyOperation, Source.applyStrict]; exact refines_fault)
  | _ :: _ :: _ :: _ :: _ =>
      exact Or.inl (by simp only [Source.applyOperation, Source.applyStrict]; exact refines_fault)
  | [.closure captured parameters body, initial, .array element elements] =>
      exact Or.inr ⟨captured, parameters, body, initial, element, elements, rfl⟩
  | [.closure _ _ _, _, .boolean _] | [.closure _ _ _, _, .nat _] | [.closure _ _ _, _, .int _]
  | [.closure _ _ _, _, .string _] | [.closure _ _ _, _, .char _]
  | [.closure _ _ _, _, .record _ _] | [.closure _ _ _, _, .variant _ _ _]
  | [.closure _ _ _, _, .closure _ _ _]
  | [.boolean _, _, _] | [.nat _, _, _] | [.int _, _, _] | [.string _, _, _] | [.char _, _, _]
  | [.record _ _, _, _] | [.array _ _, _, _] | [.variant _ _ _, _, _] =>
      exact Or.inl (by simp only [Source.applyOperation]; exact refines_fault)

/--
The six higher-order opcodes run their callback once per element on both sides, in element order,
spending one unit of fuel and recording one application event per entry. No engine law is consumed:
the callback is a real function object, and the correspondence between the two runs is
`invoke_refines`, applied once per element.
-/
theorem runOperation_callback_refines {program : Ir.Program} {target : Target.Program}
    {runtime : Runtime} {fuel : Nat} {opcode : Ir.Opcode} {typeArguments : List Ir.Ty}
    {values : List Source.Value} {operands : List Value} {trace : Source.Trace}
    {state : Target.State}
    (callback : opcode.callback = true)
    (bodyAtLower : ∀ smaller, smaller + 1 = fuel → ∀ (inner : Ir.Expr) (emitted : Target.Body),
      Compile.body program inner = .ok emitted →
      EverywhereBody program target runtime smaller inner emitted)
    (heapValid : state.heap.WellFormed) (closuresValid : state.ClosuresWellFormed)
    (related : Relation.RepresentsList program state values operands)
    (traceRefines : Relation.RefinesTrace program state trace state.trace)
    (fits : ∀ (element : Ir.Ty) (elements : List Source.Value) (next : Source.Trace),
      Source.applyOperation program fuel trace opcode typeArguments values
        = .value (.array element elements) next → elements.length ≤ Heap.maxArrayLength) :
    Relation.Refines program state
      (Source.applyOperation program fuel trace opcode typeArguments values)
      (Target.runOperation target runtime fuel state opcode operands) := by
  cases opcode
  case listMap =>
    rcases listMap_operands (program := program) (target := target) (runtime := runtime)
        (fuel := fuel) (typeArguments := typeArguments) (values := values) (operands := operands)
        (trace := trace) (state := state) with
      done | ⟨captured, parameters, body, element, elements, valuesEq⟩
    · exact done
    subst valuesEq
    obtain ⟨callbackImage, subjectImage, operandsEq, callbackRelated, subjectRelated⟩ :=
      representsList_two related
    subst operandsEq
    obtain ⟨images, read, listRelated⟩ := readArray_of_represents subjectRelated
    have loop := mapElements_refines bodyAtLower elements images trace state heapValid
      closuresValid callbackRelated listRelated traceRefines
    cases sourceRun : Source.mapElements program fuel trace captured parameters body elements with
    | fault fault last =>
        rw [show Source.applyOperation program fuel trace Ir.Opcode.listMap typeArguments
              [.closure captured parameters body, .array element elements] = .fault fault last from
          by simp only [Source.applyOperation, sourceRun]]
        exact refines_fault
    | exhausted last =>
        obtain ⟨lastState, lastRun, extension, lastValid, lastTrace⟩ :=
          refinesList_exhausted_inv (sourceRun ▸ loop)
        rw [show Source.applyOperation program fuel trace Ir.Opcode.listMap typeArguments
              [.closure captured parameters body, .array element elements] = .exhausted last from
          by simp only [Source.applyOperation, sourceRun]]
        simp only [Target.runOperation, read, lastRun]
        exact refines_exhausted extension lastValid lastTrace
    | values produced last =>
        obtain ⟨lastImages, lastState, lastRun, extension, lastValid, imagesRelated, lastTrace⟩ :=
          refinesList_inv (sourceRun ▸ loop)
        have sourceOutcome : Source.applyOperation program fuel trace Ir.Opcode.listMap
            typeArguments [.closure captured parameters body, .array element elements]
            = .value (.array (Source.imageType typeArguments) produced) last := by
          simp only [Source.applyOperation, sourceRun]
        have bound := fits (Source.imageType typeArguments) produced last sourceOutcome
        rw [sourceOutcome]
        simp only [Target.runOperation, read, lastRun]
        refine refines_widen extension ?_
        exact refines_allocateArray extension.nextWellFormed lastValid imagesRelated lastTrace bound
  case listFilter =>
    rcases listFilter_operands (program := program) (target := target) (runtime := runtime)
        (fuel := fuel) (typeArguments := typeArguments) (values := values) (operands := operands)
        (trace := trace) (state := state) with
      done | ⟨captured, parameters, body, element, elements, valuesEq⟩
    · exact done
    subst valuesEq
    obtain ⟨callbackImage, subjectImage, operandsEq, callbackRelated, subjectRelated⟩ :=
      representsList_two related
    subst operandsEq
    obtain ⟨images, read, listRelated⟩ := readArray_of_represents subjectRelated
    have loop := filterElements_refines bodyAtLower elements images trace state heapValid
      closuresValid callbackRelated listRelated traceRefines
    cases sourceRun :
        Source.filterElements program fuel trace captured parameters body elements with
    | fault fault last =>
        rw [show Source.applyOperation program fuel trace Ir.Opcode.listFilter typeArguments
              [.closure captured parameters body, .array element elements] = .fault fault last from
          by simp only [Source.applyOperation, sourceRun]]
        exact refines_fault
    | exhausted last =>
        obtain ⟨lastState, lastRun, extension, lastValid, lastTrace⟩ :=
          refinesList_exhausted_inv (sourceRun ▸ loop)
        rw [show Source.applyOperation program fuel trace Ir.Opcode.listFilter typeArguments
              [.closure captured parameters body, .array element elements] = .exhausted last from
          by simp only [Source.applyOperation, sourceRun]]
        simp only [Target.runOperation, read, lastRun]
        exact refines_exhausted extension lastValid lastTrace
    | values produced last =>
        obtain ⟨lastImages, lastState, lastRun, extension, lastValid, imagesRelated, lastTrace⟩ :=
          refinesList_inv (sourceRun ▸ loop)
        have sourceOutcome : Source.applyOperation program fuel trace Ir.Opcode.listFilter
            typeArguments [.closure captured parameters body, .array element elements]
            = .value (.array (Source.elementType typeArguments) produced) last := by
          simp only [Source.applyOperation, sourceRun]
        have bound := fits (Source.elementType typeArguments) produced last sourceOutcome
        rw [sourceOutcome]
        simp only [Target.runOperation, read, lastRun]
        refine refines_widen extension ?_
        exact refines_allocateArray extension.nextWellFormed lastValid imagesRelated lastTrace bound
  case listAny =>
    rcases listAny_operands (program := program) (target := target) (runtime := runtime)
        (fuel := fuel) (typeArguments := typeArguments) (values := values) (operands := operands)
        (trace := trace) (state := state) with
      done | ⟨element, elements, captured, parameters, body, valuesEq⟩
    · exact done
    subst valuesEq
    obtain ⟨subjectImage, callbackImage, operandsEq, subjectRelated, callbackRelated⟩ :=
      representsList_two related
    subst operandsEq
    obtain ⟨images, read, listRelated⟩ := readArray_of_represents subjectRelated
    rw [show Source.applyOperation program fuel trace Ir.Opcode.listAny typeArguments
          [.array element elements, .closure captured parameters body]
          = Source.anyElements program fuel trace captured parameters body elements from
      by simp only [Source.applyOperation]]
    simp only [Target.runOperation, read]
    exact anyElements_refines bodyAtLower elements images trace state heapValid closuresValid
      callbackRelated listRelated traceRefines
  case listAll =>
    rcases listAll_operands (program := program) (target := target) (runtime := runtime)
        (fuel := fuel) (typeArguments := typeArguments) (values := values) (operands := operands)
        (trace := trace) (state := state) with
      done | ⟨element, elements, captured, parameters, body, valuesEq⟩
    · exact done
    subst valuesEq
    obtain ⟨subjectImage, callbackImage, operandsEq, subjectRelated, callbackRelated⟩ :=
      representsList_two related
    subst operandsEq
    obtain ⟨images, read, listRelated⟩ := readArray_of_represents subjectRelated
    rw [show Source.applyOperation program fuel trace Ir.Opcode.listAll typeArguments
          [.array element elements, .closure captured parameters body]
          = Source.allElements program fuel trace captured parameters body elements from
      by simp only [Source.applyOperation]]
    simp only [Target.runOperation, read]
    exact allElements_refines bodyAtLower elements images trace state heapValid closuresValid
      callbackRelated listRelated traceRefines
  case listFoldLeft =>
    rcases listFoldLeft_operands (program := program) (target := target) (runtime := runtime)
        (fuel := fuel) (typeArguments := typeArguments) (values := values) (operands := operands)
        (trace := trace) (state := state) with
      done | ⟨captured, parameters, body, initial, element, elements, valuesEq⟩
    · exact done
    subst valuesEq
    obtain ⟨callbackImage, initialImage, subjectImage, operandsEq, callbackRelated,
      initialRelated, subjectRelated⟩ := representsList_three related
    subst operandsEq
    obtain ⟨images, read, listRelated⟩ := readArray_of_represents subjectRelated
    rw [show Source.applyOperation program fuel trace Ir.Opcode.listFoldLeft typeArguments
          [.closure captured parameters body, initial, .array element elements]
          = Source.foldLeftElements program fuel trace captured parameters body initial elements
        from by simp only [Source.applyOperation]]
    simp only [Target.runOperation, read]
    exact foldLeftElements_refines bodyAtLower elements images initial initialImage trace state
      heapValid closuresValid callbackRelated initialRelated listRelated traceRefines
  case listFoldRight =>
    rcases listFoldRight_operands (program := program) (target := target) (runtime := runtime)
        (fuel := fuel) (typeArguments := typeArguments) (values := values) (operands := operands)
        (trace := trace) (state := state) with
      done | ⟨captured, parameters, body, initial, element, elements, valuesEq⟩
    · exact done
    subst valuesEq
    obtain ⟨callbackImage, initialImage, subjectImage, operandsEq, callbackRelated,
      initialRelated, subjectRelated⟩ := representsList_three related
    subst operandsEq
    obtain ⟨images, read, listRelated⟩ := readArray_of_represents subjectRelated
    rw [show Source.applyOperation program fuel trace Ir.Opcode.listFoldRight typeArguments
          [.closure captured parameters body, initial, .array element elements]
          = Source.foldRightElements program fuel trace captured parameters body initial elements
        from by simp only [Source.applyOperation]]
    simp only [Target.runOperation, read]
    exact foldRightElements_refines bodyAtLower elements images initial initialImage trace state
      heapValid closuresValid callbackRelated initialRelated listRelated traceRefines
  all_goals exact absurd callback (by simp [Ir.Opcode.callback])

/-- Argument evaluation keeps the argument count. -/
theorem evalList_length {program : Ir.Program} {fuel : Nat} {sourceScope : List Source.Value} :
    ∀ (expressions : List Ir.Expr) (trace : Source.Trace) (produced : List Source.Value)
      (next : Source.Trace),
      Source.evalList program fuel sourceScope trace expressions = .values produced next →
      produced.length = expressions.length
  | [], trace, produced, next, run => by
      simp only [Source.evalList] at run
      injection run with producedEq _
      subst producedEq
      rfl
  | expression :: rest, trace, produced, next, run => by
      simp only [Source.evalList] at run
      cases headRun : Source.eval program fuel sourceScope trace expression with
      | fault fault middle => rw [headRun] at run; simp at run
      | exhausted middle => rw [headRun] at run; simp at run
      | value value middle =>
          rw [headRun] at run
          dsimp only at run
          cases tailRun : Source.evalList program fuel sourceScope middle rest with
          | fault fault last => rw [tailRun] at run; simp at run
          | exhausted last => rw [tailRun] at run; simp at run
          | values values last =>
              rw [tailRun] at run
              injection run with producedEq _
              subst producedEq
              simp only [List.length_cons]
              rw [evalList_length rest middle values last tailRun]

/--
An operation the emitter does not spell as a lazy operator evaluates its operands left to right and
then applies the opcode. `&&` and `||` are the only lazy forms, and only at the two operands their
emitted form takes.
-/
theorem eval_operation_strict {program : Ir.Program} {fuel : Nat} {scope : List Source.Value}
    {trace : Source.Trace} {opcode : Ir.Opcode} {typeArguments : List Ir.Ty}
    {arguments : List Ir.Expr}
    (notLazy : opcode.operator? = some .logicalAnd ∨ opcode.operator? = some .logicalOr →
      arguments.length ≠ 2) :
    Source.eval program fuel scope trace (.operation opcode typeArguments arguments)
      = match Source.evalList program fuel scope trace arguments with
        | .values values next => Source.applyOperation program fuel next opcode typeArguments values
        | .fault fault next => .fault fault next
        | .exhausted next => .exhausted next := by
  cases spelled : opcode.operator? with
  | none => (rw [Source.eval.eq_def]; simp only [spelled]; try rfl)
  | some form =>
      cases form with
      | logicalNot => (rw [Source.eval.eq_def]; simp only [spelled]; try rfl)
      | strictEquals => (rw [Source.eval.eq_def]; simp only [spelled]; try rfl)
      | logicalAnd =>
          have arity := notLazy (Or.inl spelled)
          cases arguments with
          | nil => (rw [Source.eval.eq_def]; simp only [spelled]; try rfl)
          | cons first rest =>
              cases rest with
              | nil => (rw [Source.eval.eq_def]; simp only [spelled]; try rfl)
              | cons second tail =>
                  cases tail with
                  | nil => exact absurd rfl arity
                  | cons third more => (rw [Source.eval.eq_def]; simp only [spelled]; try rfl)
      | logicalOr =>
          have arity := notLazy (Or.inr spelled)
          cases arguments with
          | nil => (rw [Source.eval.eq_def]; simp only [spelled]; try rfl)
          | cons first rest =>
              cases rest with
              | nil => (rw [Source.eval.eq_def]; simp only [spelled]; try rfl)
              | cons second tail =>
                  cases tail with
                  | nil => exact absurd rfl arity
                  | cons third more => (rw [Source.eval.eq_def]; simp only [spelled]; try rfl)

/-- A one-argument list evaluates exactly its one argument. -/
theorem evalList_one {program : Ir.Program} {fuel : Nat} {scope : List Source.Value}
    {trace : Source.Trace} (expression : Ir.Expr) :
    Source.evalList program fuel scope trace [expression]
      = match Source.eval program fuel scope trace expression with
        | .value value next => .values [value] next
        | .fault fault next => .fault fault next
        | .exhausted next => .exhausted next := by
  cases run : Source.eval program fuel scope trace expression with
  | value value next => simp only [Source.evalList, run]
  | fault fault next => simp only [Source.evalList, run]
  | exhausted next => simp only [Source.evalList, run]

/-- A two-argument list evaluates its arguments left to right. -/
theorem evalList_two {program : Ir.Program} {fuel : Nat} {scope : List Source.Value}
    {trace : Source.Trace} (first second : Ir.Expr) :
    Source.evalList program fuel scope trace [first, second]
      = match Source.eval program fuel scope trace first with
        | .value firstValue next =>
            (match Source.eval program fuel scope next second with
              | .value secondValue last => .values [firstValue, secondValue] last
              | .fault fault last => .fault fault last
              | .exhausted last => .exhausted last)
        | .fault fault next => .fault fault next
        | .exhausted next => .exhausted next := by
  cases run : Source.eval program fuel scope trace first with
  | fault fault next => simp only [Source.evalList, run]
  | exhausted next => simp only [Source.evalList, run]
  | value firstValue next =>
      cases secondRun : Source.eval program fuel scope next second with
      | fault fault last => simp only [Source.evalList, run, secondRun]
      | exhausted last => simp only [Source.evalList, run, secondRun]
      | value secondValue last => simp only [Source.evalList, run, secondRun]

/-- `!operand` accepts a boolean operand and refuses every other one. -/
theorem applyOperation_boolNot {program : Ir.Program} {fuel : Nat} {trace : Source.Trace}
    {typeArguments : List Ir.Ty} (value : Source.Value) :
    (∃ flag, value = .boolean flag ∧
        Source.applyOperation program fuel trace .boolNot typeArguments [value]
          = .value (.boolean (!flag)) trace) ∨
      (∃ fault, Source.applyOperation program fuel trace .boolNot typeArguments [value]
        = .fault fault trace) := by
  cases value with
  | boolean flag =>
      exact Or.inl ⟨flag, rfl,
        applyOperation_of_strict_ok (by decide) (by simp only [Source.applyStrict])⟩
  | nat _ | int _ | string _ | char _ | record _ _ | array _ _ | variant _ _ _
      | closure _ _ _ =>
      all_goals exact Or.inr ⟨_, applyOperation_of_strict_error (by decide)
        (by simp only [Source.applyStrict]; rfl)⟩

/-- `left === right` accepts two boolean operands and refuses every other pair. -/
theorem applyOperation_boolEquals {program : Ir.Program} {fuel : Nat} {trace : Source.Trace}
    {typeArguments : List Ir.Ty} (left right : Source.Value) :
    (∃ leftFlag rightFlag, left = .boolean leftFlag ∧ right = .boolean rightFlag ∧
        Source.applyOperation program fuel trace .boolEquals typeArguments [left, right]
          = .value (.boolean (leftFlag == rightFlag)) trace) ∨
      (∃ fault, Source.applyOperation program fuel trace .boolEquals typeArguments [left, right]
        = .fault fault trace) := by
  cases left with
  | boolean leftFlag =>
      cases right with
      | boolean rightFlag =>
          exact Or.inl ⟨leftFlag, rightFlag, rfl, rfl,
            applyOperation_of_strict_ok (by decide) (by simp only [Source.applyStrict])⟩
      | nat _ | int _ | string _ | char _ | record _ _ | array _ _ | variant _ _ _
      | closure _ _ _ =>
          all_goals exact Or.inr ⟨_, applyOperation_of_strict_error (by decide)
            (by simp only [Source.applyStrict]; rfl)⟩
  | nat _ | int _ | string _ | char _ | record _ _ | array _ _ | variant _ _ _
      | closure _ _ _ =>
      all_goals exact Or.inr ⟨_, applyOperation_of_strict_error (by decide)
        (by simp only [Source.applyStrict]; rfl)⟩

/--
One runtime opcode applied to its operands.

The four boolean opcodes reach the target as operators: `&&` and `||` are lazy in their right
operand, so the source is lazy in exactly the same place; `!` and `===` are strict. Every other
opcode reaches the target as an operation call, whose meaning is the opcode's own law for the twenty
first-order opcodes and a per-element callback entry for the six higher-order ones.
-/
theorem operation {runtime : Runtime} : Op.Preserves runtime .operation := by
  intro program target fuel
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro typeArguments left right emittedLeft emittedRight leftStep rightStep
      sourceScope targetScope trace state aligned
    rw [Source.eval.eq_def]
    simp only [Ir.Opcode.operator?, Target.eval]
    cases leftRun : Source.eval program fuel sourceScope trace left with
    | fault fault next => exact refines_fault
    | exhausted next =>
        obtain ⟨targetState, targetRun, extension, closuresValid, traceRefines⟩ :=
          refines_exhausted_inv (leftRun ▸ leftStep sourceScope targetScope trace state aligned)
        rw [targetRun]
        exact refines_exhausted extension closuresValid traceRefines
    | value produced next =>
        obtain ⟨image, targetState, targetRun, extension, closuresValid, related, traceRefines⟩ :=
          refines_value_inv (leftRun ▸ leftStep sourceScope targetScope trace state aligned)
        rw [targetRun]
        cases produced with
        | boolean flag =>
            unfold Relation.Represents at related
            subst related
            cases flag with
            | false =>
                simp only [Value.toBoolean, Primitive.toBoolean, Bool.false_eq_true, if_false]
                refine refines_value extension closuresValid ?_ traceRefines
                unfold Relation.Represents
                rfl
            | true =>
                simp only [Value.toBoolean, Primitive.toBoolean, if_true]
                have nextAligned := aligned.step extension closuresValid traceRefines
                cases rightRun : Source.eval program fuel sourceScope next right with
                | fault fault last => exact refines_fault
                | exhausted last =>
                    obtain ⟨lastState, lastRun, lastExtension, lastValid, lastTrace⟩ :=
                      refines_exhausted_inv
                        (rightRun ▸ rightStep sourceScope targetScope next targetState nextAligned)
                    rw [lastRun]
                    exact refines_exhausted (extension.trans lastExtension) lastValid lastTrace
                | value second last =>
                    obtain ⟨secondImage, lastState, lastRun, lastExtension, lastValid,
                      secondRelated, lastTrace⟩ :=
                      refines_value_inv
                        (rightRun ▸ rightStep sourceScope targetScope next targetState nextAligned)
                    rw [lastRun]
                    cases second with
                    | boolean secondFlag =>
                        exact refines_value (extension.trans lastExtension) lastValid secondRelated
                          lastTrace
                    | nat _ | int _ | string _ | char _ | record _ _ | array _ _
                    | variant _ _ _ | closure _ _ _ => all_goals exact refines_fault
        | nat _ | int _ | string _ | char _ | record _ _ | array _ _ | variant _ _ _
      | closure _ _ _ =>
            all_goals exact refines_fault
  · intro typeArguments left right emittedLeft emittedRight leftStep rightStep
      sourceScope targetScope trace state aligned
    rw [Source.eval.eq_def]
    simp only [Ir.Opcode.operator?, Target.eval]
    cases leftRun : Source.eval program fuel sourceScope trace left with
    | fault fault next => exact refines_fault
    | exhausted next =>
        obtain ⟨targetState, targetRun, extension, closuresValid, traceRefines⟩ :=
          refines_exhausted_inv (leftRun ▸ leftStep sourceScope targetScope trace state aligned)
        rw [targetRun]
        exact refines_exhausted extension closuresValid traceRefines
    | value produced next =>
        obtain ⟨image, targetState, targetRun, extension, closuresValid, related, traceRefines⟩ :=
          refines_value_inv (leftRun ▸ leftStep sourceScope targetScope trace state aligned)
        rw [targetRun]
        cases produced with
        | boolean flag =>
            unfold Relation.Represents at related
            subst related
            cases flag with
            | true =>
                simp only [Value.toBoolean, Primitive.toBoolean, if_true]
                refine refines_value extension closuresValid ?_ traceRefines
                unfold Relation.Represents
                rfl
            | false =>
                simp only [Value.toBoolean, Primitive.toBoolean, Bool.false_eq_true, if_false]
                have nextAligned := aligned.step extension closuresValid traceRefines
                cases rightRun : Source.eval program fuel sourceScope next right with
                | fault fault last => exact refines_fault
                | exhausted last =>
                    obtain ⟨lastState, lastRun, lastExtension, lastValid, lastTrace⟩ :=
                      refines_exhausted_inv
                        (rightRun ▸ rightStep sourceScope targetScope next targetState nextAligned)
                    rw [lastRun]
                    exact refines_exhausted (extension.trans lastExtension) lastValid lastTrace
                | value second last =>
                    obtain ⟨secondImage, lastState, lastRun, lastExtension, lastValid,
                      secondRelated, lastTrace⟩ :=
                      refines_value_inv
                        (rightRun ▸ rightStep sourceScope targetScope next targetState nextAligned)
                    rw [lastRun]
                    cases second with
                    | boolean secondFlag =>
                        exact refines_value (extension.trans lastExtension) lastValid secondRelated
                          lastTrace
                    | nat _ | int _ | string _ | char _ | record _ _ | array _ _
                    | variant _ _ _ | closure _ _ _ => all_goals exact refines_fault
        | nat _ | int _ | string _ | char _ | record _ _ | array _ _ | variant _ _ _
      | closure _ _ _ =>
            all_goals exact refines_fault
  · intro typeArguments operand emittedOperand operandStep
      sourceScope targetScope trace state aligned
    rw [eval_operation_strict (opcode := .boolNot) (typeArguments := typeArguments)
      (arguments := [operand]) (by
        intro lazy
        rcases lazy with spelled | spelled <;> simp [Ir.Opcode.operator?] at spelled),
      evalList_one]
    simp only [Target.eval]
    cases operandRun : Source.eval program fuel sourceScope trace operand with
    | fault fault next => exact refines_fault
    | exhausted next =>
        obtain ⟨targetState, targetRun, extension, closuresValid, traceRefines⟩ :=
          refines_exhausted_inv
            (operandRun ▸ operandStep sourceScope targetScope trace state aligned)
        rw [targetRun]
        exact refines_exhausted extension closuresValid traceRefines
    | value produced next =>
        obtain ⟨image, targetState, targetRun, extension, closuresValid, related, traceRefines⟩ :=
          refines_value_inv (operandRun ▸ operandStep sourceScope targetScope trace state aligned)
        rw [targetRun]
        dsimp only
        rcases applyOperation_boolNot (program := program) (fuel := fuel) (trace := next)
            (typeArguments := typeArguments) produced with
          ⟨flag, producedEq, sourceOutcome⟩ | ⟨fault, sourceOutcome⟩
        · rw [sourceOutcome]
          subst producedEq
          unfold Relation.Represents at related
          subst related
          refine refines_value extension closuresValid ?_ traceRefines
          unfold Relation.Represents
          rfl
        · rw [sourceOutcome]
          exact refines_fault
  · intro typeArguments left right emittedLeft emittedRight leftStep rightStep
    refine ⟨?_, ?_, ?_⟩
    · intro sourceScope targetScope trace state aligned
      rw [eval_operation_strict (opcode := .boolEquals) (typeArguments := typeArguments)
        (arguments := [left, right]) (by
          intro lazy
          rcases lazy with spelled | spelled <;> simp [Ir.Opcode.operator?] at spelled),
        evalList_two]
      simp only [Target.eval]
      cases leftRun : Source.eval program fuel sourceScope trace left with
      | fault fault next => exact refines_fault
      | exhausted next =>
          obtain ⟨targetState, targetRun, extension, closuresValid, traceRefines⟩ :=
            refines_exhausted_inv (leftRun ▸ leftStep sourceScope targetScope trace state aligned)
          rw [targetRun]
          exact refines_exhausted extension closuresValid traceRefines
      | value first next =>
          obtain ⟨firstImage, targetState, targetRun, extension, closuresValid, firstRelated,
            traceRefines⟩ :=
            refines_value_inv (leftRun ▸ leftStep sourceScope targetScope trace state aligned)
          rw [targetRun]
          dsimp only
          have nextAligned := aligned.step extension closuresValid traceRefines
          cases rightRun : Source.eval program fuel sourceScope next right with
          | fault fault last => exact refines_fault
          | exhausted last =>
              obtain ⟨lastState, lastRun, lastExtension, lastValid, lastTrace⟩ :=
                refines_exhausted_inv
                  (rightRun ▸ rightStep sourceScope targetScope next targetState nextAligned)
              rw [lastRun]
              exact refines_exhausted (extension.trans lastExtension) lastValid lastTrace
          | value second last =>
              obtain ⟨secondImage, lastState, lastRun, lastExtension, lastValid, secondRelated,
                lastTrace⟩ :=
                refines_value_inv
                  (rightRun ▸ rightStep sourceScope targetScope next targetState nextAligned)
              rw [lastRun]
              dsimp only
              rcases applyOperation_boolEquals (program := program) (fuel := fuel) (trace := last)
                  (typeArguments := typeArguments) first second with
                ⟨firstFlag, secondFlag, firstEq, secondEq, sourceOutcome⟩ | ⟨fault, sourceOutcome⟩
              · rw [sourceOutcome]
                subst firstEq
                subst secondEq
                unfold Relation.Represents at firstRelated secondRelated
                subst firstRelated
                subst secondRelated
                refine refines_value (extension.trans lastExtension) lastValid ?_ lastTrace
                unfold Relation.Represents
                rw [TSLean.Refinement.Bool.strictEqual_commutes firstFlag secondFlag]
              · rw [sourceOutcome]
                exact refines_fault
    · intro sourceScope targetScope trace state aligned
      rw [eval_operation_strict (opcode := .boolEquals) (typeArguments := typeArguments)
        (arguments := [left, .boolLit true]) (by
          intro lazy
          rcases lazy with spelled | spelled <;> simp [Ir.Opcode.operator?] at spelled),
        evalList_two]
      cases leftRun : Source.eval program fuel sourceScope trace left with
      | fault fault next => exact refines_fault
      | exhausted next =>
          obtain ⟨targetState, targetRun, extension, closuresValid, traceRefines⟩ :=
            refines_exhausted_inv (leftRun ▸ leftStep sourceScope targetScope trace state aligned)
          rw [targetRun]
          exact refines_exhausted extension closuresValid traceRefines
      | value first next =>
          obtain ⟨firstImage, targetState, targetRun, extension, closuresValid, firstRelated,
            traceRefines⟩ :=
            refines_value_inv (leftRun ▸ leftStep sourceScope targetScope trace state aligned)
          rw [targetRun]
          simp only [Source.eval]
          rcases applyOperation_boolEquals (program := program) (fuel := fuel) (trace := next)
              (typeArguments := typeArguments) first (.boolean true) with
            ⟨firstFlag, secondFlag, firstEq, secondEq, sourceOutcome⟩ | ⟨fault, sourceOutcome⟩
          · rw [sourceOutcome]
            subst firstEq
            injection secondEq with secondFlagEq
            subst secondFlagEq
            unfold Relation.Represents at firstRelated
            subst firstRelated
            refine refines_value extension closuresValid ?_ traceRefines
            unfold Relation.Represents
            cases firstFlag <;> rfl
          · rw [sourceOutcome]
            exact refines_fault
    · intro sourceScope targetScope trace state aligned
      rw [eval_operation_strict (opcode := .boolEquals) (typeArguments := typeArguments)
        (arguments := [.boolLit true, right]) (by
          intro lazy
          rcases lazy with spelled | spelled <;> simp [Ir.Opcode.operator?] at spelled),
        evalList_two]
      simp only [Source.eval]
      cases rightRun : Source.eval program fuel sourceScope trace right with
      | fault fault next => exact refines_fault
      | exhausted next =>
          obtain ⟨targetState, targetRun, extension, closuresValid, traceRefines⟩ :=
            refines_exhausted_inv
              (rightRun ▸ rightStep sourceScope targetScope trace state aligned)
          rw [targetRun]
          exact refines_exhausted extension closuresValid traceRefines
      | value second next =>
          obtain ⟨secondImage, targetState, targetRun, extension, closuresValid, secondRelated,
            traceRefines⟩ :=
            refines_value_inv (rightRun ▸ rightStep sourceScope targetScope trace state aligned)
          rw [targetRun]
          dsimp only
          rcases applyOperation_boolEquals (program := program) (fuel := fuel) (trace := next)
              (typeArguments := typeArguments) (.boolean true) second with
            ⟨firstFlag, secondFlag, firstEq, secondEq, sourceOutcome⟩ | ⟨fault, sourceOutcome⟩
          · rw [sourceOutcome]
            subst secondEq
            injection firstEq with firstFlagEq
            subst firstFlagEq
            unfold Relation.Represents at secondRelated
            subst secondRelated
            refine refines_value extension closuresValid ?_ traceRefines
            unfold Relation.Represents
            cases secondFlag <;> rfl
          · rw [sourceOutcome]
            exact refines_fault
  · intro opcode typeArguments arguments emittedArguments notOperator law listsFit argumentsStep
      bodyAtLower sourceScope targetScope trace state aligned
    rw [eval_operation_strict (by
      intro lazy
      rcases lazy with spelled | spelled
      · exact notOperator .logicalAnd spelled
      · exact notOperator .logicalOr spelled)]
    simp only [Target.eval]
    cases sourceRun : Source.evalList program fuel sourceScope trace arguments with
    | fault fault next => exact refines_fault
    | exhausted next =>
        obtain ⟨targetState, targetRun, extension, closuresValid, traceRefines⟩ :=
          refinesList_exhausted_inv
            (sourceRun ▸ argumentsStep sourceScope targetScope trace state aligned)
        rw [targetRun]
        exact refines_exhausted extension closuresValid traceRefines
    | values produced next =>
        obtain ⟨targets, targetState, targetRun, extension, closuresValid, listRelated,
          traceRefines⟩ :=
          refinesList_inv (sourceRun ▸ argumentsStep sourceScope targetScope trace state aligned)
        rw [targetRun]
        dsimp only
        have counted := evalList_length arguments trace produced next sourceRun
        have fits : ∀ (element : Ir.Ty) (elements : List Source.Value) (last : Source.Trace),
            Source.applyOperation program fuel next opcode typeArguments produced
              = .value (.array element elements) last →
            elements.length ≤ Heap.maxArrayLength := by
          intro element elements last outcome
          refine listsFit fuel sourceScope trace (.operation opcode typeArguments arguments)
            element elements last ?_
          rw [eval_operation_strict (by
            intro lazy
            rcases lazy with spelled | spelled
            · exact notOperator .logicalAnd spelled
            · exact notOperator .logicalOr spelled), sourceRun]
          exact outcome
        refine refines_widen extension ?_
        by_cases callback : opcode.callback = true
        · exact runOperation_callback_refines callback bodyAtLower extension.nextWellFormed
            closuresValid listRelated traceRefines fits
        · refine runOperation_firstOrder_refines (by simpa using callback) law ?_
            extension.nextWellFormed closuresValid listRelated traceRefines fits
          intro form spelled
          rw [counted]
          exact notOperator form spelled

/-! ## Support for the constructor operations -/

/-- A named property list whose values are an argument list evaluates to those arguments' values,
paired with the names in order. -/
theorem evalProperties_zip_ok {target : Target.Program} {runtime : Runtime} {fuel : Nat}
    {targetScope : List Value} :
    ∀ (names : List String) (expressions : List Target.Expr) (state : Target.State)
      (targets : List Value) (next : Target.State),
      names.length = expressions.length →
      Target.evalList target runtime fuel targetScope state expressions = .ok targets next →
      Target.evalProperties target runtime fuel targetScope state (names.zip expressions)
        = .ok (names.zip targets) next
  | [], [], state, targets, next, _, run => by
      simp only [Target.evalList] at run
      injection run with targetsEq nextEq
      subst targetsEq
      subst nextEq
      simp only [List.zip_nil_left, Target.evalProperties]
  | [], _ :: _, _, _, _, lengths, _ => by simp at lengths
  | _ :: _, [], _, _, _, lengths, _ => by simp at lengths
  | name :: restNames, expression :: restExpressions, state, targets, next, lengths, run => by
      simp only [Target.evalList] at run
      cases headRun : Target.eval target runtime fuel targetScope state expression with
      | thrown error middle => rw [headRun] at run; simp at run
      | fault fault middle => rw [headRun] at run; simp at run
      | exhausted middle => rw [headRun] at run; simp at run
      | ok value middle =>
          rw [headRun] at run
          dsimp only at run
          cases tailRun :
              Target.evalList target runtime fuel targetScope middle restExpressions with
          | thrown error last => rw [tailRun] at run; simp at run
          | fault fault last => rw [tailRun] at run; simp at run
          | exhausted last => rw [tailRun] at run; simp at run
          | ok values last =>
              rw [tailRun] at run
              injection run with targetsEq nextEq
              subst targetsEq
              subst nextEq
              simp only [List.zip_cons_cons, Target.evalProperties, headRun]
              rw [evalProperties_zip_ok restNames restExpressions middle values last
                (by simpa using lengths) tailRun]

/-- A named property list whose values run out of fuel runs out of fuel in the same state. -/
theorem evalProperties_zip_exhausted {target : Target.Program} {runtime : Runtime} {fuel : Nat}
    {targetScope : List Value} :
    ∀ (names : List String) (expressions : List Target.Expr) (state : Target.State)
      (next : Target.State),
      names.length = expressions.length →
      Target.evalList target runtime fuel targetScope state expressions = .exhausted next →
      Target.evalProperties target runtime fuel targetScope state (names.zip expressions)
        = .exhausted next
  | [], [], state, next, _, run => by
      simp only [Target.evalList] at run
      exact absurd run (by simp)
  | [], _ :: _, _, _, lengths, _ => by simp at lengths
  | _ :: _, [], _, _, lengths, _ => by simp at lengths
  | name :: restNames, expression :: restExpressions, state, next, lengths, run => by
      simp only [Target.evalList] at run
      cases headRun : Target.eval target runtime fuel targetScope state expression with
      | thrown error middle => rw [headRun] at run; simp at run
      | fault fault middle => rw [headRun] at run; simp at run
      | exhausted middle =>
          rw [headRun] at run
          injection run with nextEq
          subst nextEq
          simp only [List.zip_cons_cons, Target.evalProperties, headRun]
      | ok value middle =>
          rw [headRun] at run
          dsimp only at run
          cases tailRun :
              Target.evalList target runtime fuel targetScope middle restExpressions with
          | thrown error last => rw [tailRun] at run; simp at run
          | fault fault last => rw [tailRun] at run; simp at run
          | ok values last => rw [tailRun] at run; simp at run
          | exhausted last =>
              rw [tailRun] at run
              injection run with nextEq
              subst nextEq
              simp only [List.zip_cons_cons, Target.evalProperties, headRun]
              rw [evalProperties_zip_exhausted restNames restExpressions middle last
                (by simpa using lengths) tailRun]

/-- A constructor's declared fields paired with represented argument values. -/
theorem representsArguments_zip {program : Ir.Program} {state : Target.State} :
    ∀ (fields : List Ir.Field) (values : List Source.Value) (targets : List Value),
      fields.length = values.length →
      Relation.RepresentsList program state values targets →
      Relation.RepresentsArguments program state fields values
        ((fields.map Ir.Field.name).zip targets)
  | fields, [], targets, lengths, related => by
      unfold Relation.RepresentsList at related
      subst related
      unfold Relation.RepresentsArguments
      cases fields with
      | nil => exact ⟨rfl, rfl⟩
      | cons field rest => simp at lengths
  | fields, value :: rest, targets, lengths, related => by
      unfold Relation.RepresentsList at related
      obtain ⟨image, restTargets, targetsEq, headRelated, tailRelated⟩ := related
      subst targetsEq
      cases fields with
      | nil => simp at lengths
      | cons field remaining =>
          unfold Relation.RepresentsArguments
          refine ⟨field, remaining, image, (remaining.map Ir.Field.name).zip restTargets, rfl, ?_,
            headRelated, ?_⟩
          · simp only [List.map_cons, List.zip_cons_cons]
          · exact representsArguments_zip remaining rest restTargets (by simpa using lengths)
              tailRelated

/-- An enum with no payload anywhere declares only nullary constructors. -/
theorem nullary_fields {constructors : List Ir.Constructor} {name : String}
    {constructor : Ir.Constructor} (nullary : Ir.allNullary constructors = true)
    (selected : Ir.constructor? constructors name = some constructor) : constructor.fields = [] := by
  unfold Ir.allNullary at nullary
  have member : constructor ∈ constructors := List.mem_of_find?_eq_some selected
  have empty := (List.all_eq_true.mp nullary) constructor member
  exact List.isEmpty_iff.mp empty

/-- A type that holds no element type builds a tagged value from its evaluated arguments. -/
theorem eval_variant_tagged {program : Ir.Program} {fuel : Nat} {scope : List Source.Value}
    {trace : Source.Trace} {type : Ir.Ty} {name : String} {arguments : List Ir.Expr}
    (notList : type.element? = none) :
    Source.eval program fuel scope trace (.variant type name arguments)
      = match Source.evalList program fuel scope trace arguments with
        | .values values next => .value (.variant type name values) next
        | .fault fault next => .fault fault next
        | .exhausted next => .exhausted next := by
  rw [Source.eval.eq_def]
  simp only [notList]
  rfl

/-- The empty list is the empty array. -/
theorem eval_variant_nil {program : Ir.Program} {fuel : Nat} {scope : List Source.Value}
    {trace : Source.Trace} {element : Ir.Ty} :
    Source.eval program fuel scope trace (.variant (.list element) "nil" [])
      = .value (.array element []) trace := by
  rw [Source.eval.eq_def]
  simp only [Ir.Ty.element?, Source.evalList]

/--
A constructor value.

A type that carries an element type is a `List`, and reaches the target as a dense array: `nil` is
`[]` and `cons` is `[head, ...tail]`. Every other type reaches the target as the emitter's structural
representation: an enum with no payload anywhere becomes its own tag string, and every other type
becomes an object carrying `kind` and then the constructor's declared fields.
-/
theorem variant {runtime : Runtime} : Op.Preserves runtime .variant := by
  intro program target fuel
  refine ⟨?_, ?_, ?_⟩
  · intro type name constructors constructor arguments emittedArguments notList declared selected
      keys distinct arity emittedArity argumentsStep
    refine ⟨?_, ?_⟩
    · intro nullary sourceScope targetScope trace state aligned
      have noFields := nullary_fields nullary selected
      have noArguments : arguments = [] := by
        rw [noFields] at arity
        exact List.eq_nil_of_length_eq_zero arity.symm
      subst noArguments
      rw [eval_variant_tagged notList]
      simp only [Source.evalList, Target.eval]
      refine refines_value (Target.State.Extension.refl state aligned.heapValid)
        aligned.closuresValid ?_ aligned.trace
      unfold Relation.Represents
      refine ⟨constructors, declared, constructor, selected, ?_⟩
      rw [if_pos nullary]
      exact ⟨rfl, rfl⟩
    · intro carries sourceScope targetScope trace state aligned
      rw [eval_variant_tagged notList]
      simp only [Target.eval, Target.evalProperties]
      cases sourceRun : Source.evalList program fuel sourceScope trace arguments with
      | fault fault next => exact refines_fault
      | exhausted next =>
          obtain ⟨targetState, targetRun, extension, closuresValid, traceRefines⟩ :=
            refinesList_exhausted_inv
              (sourceRun ▸ argumentsStep sourceScope targetScope trace state aligned)
          rw [evalProperties_zip_exhausted (constructor.fields.map Ir.Field.name) emittedArguments
            state targetState (by simp [arity, emittedArity]) targetRun]
          exact refines_exhausted extension closuresValid traceRefines
      | values produced next =>
          obtain ⟨targets, targetState, targetRun, extension, closuresValid, listRelated,
            traceRefines⟩ :=
            refinesList_inv (sourceRun ▸ argumentsStep sourceScope targetScope trace state aligned)
          rw [evalProperties_zip_ok (constructor.fields.map Ir.Field.name) emittedArguments state
            targets targetState (by simp [arity, emittedArity]) targetRun]
          dsimp only
          have names : ((constructor.fields.map Ir.Field.name).zip targets).map Prod.fst
              = constructor.fields.map Ir.Field.name := by
            refine List.map_fst_zip ?_
            simp only [List.length_map]
            rw [arity, ← evalList_length arguments trace produced next sourceRun,
              representsList_length produced targets listRelated]
            exact Nat.le_refl _
          obtain ⟨ref, final, allocated, traceEq, _, finalExtension, finalValid, _, shape⟩ :=
            Allocation.allocateLiteral_shape targetState
              (("kind", Value.primitive (.string (JSString.ofLeanString name)))
                :: (constructor.fields.map Ir.Field.name).zip targets)
              extension.nextWellFormed closuresValid
              (by
                intro entry member
                rcases List.mem_cons.mp member with rfl | tail
                · show Ir.ValidKey "kind"
                  decide
                · have nameMember : entry.1 ∈ constructor.fields.map Ir.Field.name := by
                    rw [← names]
                    exact List.mem_map_of_mem tail
                  obtain ⟨field, fieldMember, fieldEq⟩ := List.mem_map.mp nameMember
                  exact fieldEq ▸ (keys field fieldMember).1)
              (by
                simp only [List.map_cons, names]
                refine List.nodup_cons.mpr ⟨?_, distinct⟩
                intro member
                obtain ⟨field, fieldMember, fieldEq⟩ := List.mem_map.mp member
                exact (keys field fieldMember).2 fieldEq)
              (by
                intro entry member
                rcases List.mem_cons.mp member with rfl | tail
                · rfl
                · have valueMember : entry.2 ∈ targets := (List.of_mem_zip tail).2
                  exact representsList_valuesValid produced targets listRelated entry.2 valueMember)
          rw [allocated]
          refine refines_value (extension.trans finalExtension) finalValid ?_ ?_
          · unfold Relation.Represents
            refine ⟨constructors, declared, constructor, selected, ?_⟩
            rw [if_neg (by simp [carries])]
            exact ⟨ref, (constructor.fields.map Ir.Field.name).zip targets, rfl,
              Relation.RepresentsArguments.stable finalExtension constructor.fields produced _
                (representsArguments_zip constructor.fields produced targets
                  (by rw [arity, ← evalList_length arguments trace produced next sourceRun])
                  listRelated),
              shape⟩
          · rw [traceEq]
            exact Relation.RefinesTrace.stable finalExtension next targetState.trace traceRefines
  · intro element sourceScope targetScope trace state aligned
    rw [eval_variant_nil]
    simp only [Target.eval]
    obtain ⟨ref, final, allocated, traceEq, _, extension, finalValid, dense⟩ :=
      Allocation.allocateArray_shape state [] aligned.heapValid aligned.closuresValid
        (by intro value member; exact absurd member (by simp)) (by simp)
    rw [allocated]
    refine refines_value extension finalValid ?_ ?_
    · unfold Relation.Represents
      exact ⟨ref, [], rfl, represents_nil, dense⟩
    · rw [traceEq]
      exact Relation.RefinesTrace.stable extension trace state.trace aligned.trace
  · intro element head tail emittedHead emittedTail listsFit headStep tailStep
      sourceScope targetScope trace state aligned
    rw [Source.eval.eq_def]
    simp only [Ir.Ty.element?, Target.eval]
    rw [evalList_two]
    cases headRun : Source.eval program fuel sourceScope trace head with
    | fault fault next => exact refines_fault
    | exhausted next =>
        obtain ⟨targetState, targetRun, extension, closuresValid, traceRefines⟩ :=
          refines_exhausted_inv (headRun ▸ headStep sourceScope targetScope trace state aligned)
        rw [targetRun]
        exact refines_exhausted extension closuresValid traceRefines
    | value headValue next =>
        obtain ⟨headImage, targetState, targetRun, extension, closuresValid, headRelated,
          traceRefines⟩ :=
          refines_value_inv (headRun ▸ headStep sourceScope targetScope trace state aligned)
        rw [targetRun]
        dsimp only
        have nextAligned := aligned.step extension closuresValid traceRefines
        cases tailRun : Source.eval program fuel sourceScope next tail with
        | fault fault last => exact refines_fault
        | exhausted last =>
            obtain ⟨lastState, lastRun, lastExtension, lastValid, lastTrace⟩ :=
              refines_exhausted_inv
                (tailRun ▸ tailStep sourceScope targetScope next targetState nextAligned)
            rw [lastRun]
            exact refines_exhausted (extension.trans lastExtension) lastValid lastTrace
        | value tailValue last =>
            obtain ⟨tailImage, lastState, lastRun, lastExtension, lastValid, tailRelated,
              lastTrace⟩ :=
              refines_value_inv
                (tailRun ▸ tailStep sourceScope targetScope next targetState nextAligned)
            rw [lastRun]
            dsimp only
            cases tailValue with
            | array tailElement rest =>
                obtain ⟨images, read, listRelated⟩ := readArray_of_represents tailRelated
                rw [read]
                have sourceOutcome : Source.eval program fuel sourceScope trace
                    (.variant (.list element) "cons" [head, tail])
                    = .value (.array element (headValue :: rest)) last := by
                  rw [Source.eval.eq_def]
                  simp only [Ir.Ty.element?, evalList_two, headRun, tailRun]
                have bound := listsFit fuel sourceScope trace
                  (.variant (.list element) "cons" [head, tail]) element (headValue :: rest) last
                  sourceOutcome
                refine refines_widen (extension.trans lastExtension) ?_
                exact refines_allocateArray (extension.trans lastExtension).nextWellFormed
                  lastValid
                  (by
                    unfold Relation.RepresentsList
                    exact ⟨headImage, images, rfl,
                      Relation.Represents.stable lastExtension headValue headImage headRelated,
                      listRelated⟩)
                  lastTrace bound
            | boolean _ | nat _ | int _ | string _ | char _ | record _ _ | variant _ _ _
            | closure _ _ _ =>
                all_goals exact refines_fault

/-! ## The tag chain -/

/-- A represented tag is the constructor's own name as a JavaScript string. -/
theorem tag_of_represents {program : Ir.Program} {state : Target.State} {type : Ir.Ty}
    {name : String} {arguments : List Source.Value} {image : Value}
    {constructors : List Ir.Constructor}
    (declared : program.constructorsOf type = some constructors)
    (nullary : Ir.allNullary constructors = true)
    (related : Relation.Represents program state (.variant type name arguments) image) :
    image = .primitive (.string (JSString.ofLeanString name)) := by
  unfold Relation.Represents at related
  obtain ⟨found, foundEq, constructor, selected, body⟩ := related
  rw [declared] at foundEq
  injection foundEq with constructorsEq
  subst constructorsEq
  rw [if_pos nullary] at body
  exact body.2

/-- An enum with no payload anywhere is not a `List`: `cons` carries a head and a tail. -/
theorem element?_none_of_nullary {program : Ir.Program} {type : Ir.Ty}
    {constructors : List Ir.Constructor}
    (declared : program.constructorsOf type = some constructors)
    (nullary : Ir.allNullary constructors = true) : type.element? = none := by
  cases type with
  | list element =>
      rw [show program.constructorsOf (.list element)
        = some [⟨"nil", []⟩, ⟨"cons", [⟨"head", element⟩, ⟨"tail", .list element⟩]⟩] from rfl]
        at declared
      injection declared with constructorsEq
      subst constructorsEq
      exact absurd nullary (by simp [Ir.allNullary])
  | boolean | nat | string | parameter _ | named _ _ | option _ | except _ _ | function _ _
  | int | char | bytes | json | array _ | pair _ _ | hashMap _ _ | treeMap _ _ =>
      all_goals rfl

/-- The tag chain decides the arm whose tag the scrutinee carries, reading the scrutinee once per
comparison without that repetition being observable. -/
theorem tagChain_refines {program : Ir.Program} {target : Target.Program} {runtime : Runtime}
    {fuel : Nat} {emittedScrutinee : Target.Expr}
    (stable : StateStable target runtime fuel emittedScrutinee) :
    ∀ (cases : List (String × Ir.Expr)) (emittedCases : List (String × Target.Expr))
      (chain : Target.Expr) (tagName : String) (sourceScope : List Source.Value)
      (targetScope : List Value) (trace : Source.Trace) (state : Target.State),
      EverywhereCases program target runtime fuel cases emittedCases →
      Compile.tagChain emittedScrutinee emittedCases = some chain →
      Aligned program sourceScope targetScope trace state →
      Target.eval target runtime fuel targetScope state emittedScrutinee
        = .ok (.primitive (.string (JSString.ofLeanString tagName))) state →
      Relation.Refines program state
        (Source.evalCases program fuel sourceScope trace tagName [] cases)
        (Target.eval target runtime fuel targetScope state chain)
  | [], emittedCases, chain, tagName, sourceScope, targetScope, trace, state, armsStep, built,
      aligned, scrutineeRun => by
      unfold EverywhereCases at armsStep
      subst armsStep
      simp only [Compile.tagChain] at built
      exact absurd built (by simp)
  | [(tag, arm)], emittedCases, chain, tagName, sourceScope, targetScope, trace, state, armsStep,
      built, aligned, scrutineeRun => by
      unfold EverywhereCases at armsStep
      obtain ⟨emittedArm, restEmitted, emittedEq, armStep, restStep⟩ := armsStep
      unfold EverywhereCases at restStep
      subst restStep
      subst emittedEq
      simp only [Compile.tagChain, Option.some.injEq] at built
      subst built
      simp only [Source.evalCases]
      by_cases matched : tag = tagName
      · rw [if_pos matched]
        exact armStep sourceScope targetScope trace state aligned
      · rw [if_neg matched]
        exact refines_fault
  | (tag, arm) :: (secondTag, secondArm) :: rest, emittedCases, chain, tagName, sourceScope,
      targetScope, trace, state, armsStep, built, aligned, scrutineeRun => by
      unfold EverywhereCases at armsStep
      obtain ⟨emittedArm, restEmitted, emittedEq, armStep, restStep⟩ := armsStep
      subst emittedEq
      have restShape := restStep
      unfold EverywhereCases at restShape
      obtain ⟨emittedSecond, tailEmitted, restEq, _, _⟩ := restShape
      subst restEq
      simp only [Compile.tagChain] at built
      cases alternateBuilt :
          Compile.tagChain emittedScrutinee ((secondTag, emittedSecond) :: tailEmitted) with
      | none => rw [alternateBuilt] at built; simp at built
      | some alternate =>
          rw [alternateBuilt] at built
          simp only [Option.map_some, Option.some.injEq] at built
          subst built
          simp only [Target.eval, scrutineeRun]
          rw [TSLean.Refinement.String.strictEqual_commutes tagName tag]
          by_cases matched : tag = tagName
          · subst matched
            simpa only [Source.evalCases, if_pos, beq_self_eq_true, Value.toBoolean,
              Primitive.toBoolean, List.reverse_nil, List.nil_append] using
              armStep sourceScope targetScope trace state aligned
          · have different : (tagName == tag) = false :=
              beq_eq_false_iff_ne.mpr fun same => matched same.symm
            simpa only [Source.evalCases, if_neg matched, different, Value.toBoolean,
              Primitive.toBoolean, Bool.false_eq_true, if_false] using
              tagChain_refines stable ((secondTag, secondArm) :: rest)
                ((secondTag, emittedSecond) :: tailEmitted) alternate tagName sourceScope targetScope
                trace state restStep alternateBuilt aligned scrutineeRun

/-! ## The statement-form dispatch -/

/-- A represented payload's own keys are the constructor's declared field names, in declaration
order: the representation records one entry per field, under that field's own name. -/
theorem representsArguments_keys {program : Ir.Program} {state : Target.State} :
    ∀ (fields : List Ir.Field) (arguments : List Source.Value)
      (entries : List (String × Value)),
      Relation.RepresentsArguments program state fields arguments entries →
      entries.map Prod.fst = fields.map Ir.Field.name
  | fields, [], entries, related => by
      unfold Relation.RepresentsArguments at related
      obtain ⟨fieldsEq, entriesEq⟩ := related
      subst fieldsEq
      subst entriesEq
      rfl
  | fields, value :: rest, entries, related => by
      unfold Relation.RepresentsArguments at related
      obtain ⟨field, remaining, image, restEntries, fieldsEq, entriesEq, _, tailRelated⟩ := related
      subst fieldsEq
      subst entriesEq
      simp only [List.map_cons]
      rw [representsArguments_keys remaining rest restEntries tailRelated]

/-- A represented payload's images are exactly the entry values, in declaration order. -/
theorem representsArguments_values {program : Ir.Program} {state : Target.State} :
    ∀ (fields : List Ir.Field) (arguments : List Source.Value)
      (entries : List (String × Value)),
      Relation.RepresentsArguments program state fields arguments entries →
      Relation.RepresentsList program state arguments (entries.map Prod.snd)
  | _, [], entries, related => by
      unfold Relation.RepresentsArguments at related
      obtain ⟨_, entriesEq⟩ := related
      subst entriesEq
      exact represents_nil
  | _, value :: rest, entries, related => by
      unfold Relation.RepresentsArguments at related
      obtain ⟨field, remaining, image, restEntries, _, entriesEq, headRelated, tailRelated⟩ :=
        related
      subst entriesEq
      unfold Relation.RepresentsList
      exact ⟨image, restEntries.map Prod.snd, by simp, headRelated,
        representsArguments_values remaining rest restEntries tailRelated⟩

/--
Reading a run of own properties off an object answers exactly the values the shape records for them,
in order, and changes no state.

`consumed` is the entry run the reads have already passed: the emitted tag, and then each field in
turn. Stating it that way is what makes the lemma true of the whole own-property sequence rather than
of a suffix — a field name that collided with the tag, or with an earlier field, would resolve to the
earlier own property, and `Compile.checkPayloads` refuses a declaration for exactly that.
-/
theorem readPayload_of_entries {state : Target.State} {ref : RefId} :
    ∀ (consumed entries : List (String × Value)),
      Relation.HasOwnFields state.heap ref (consumed ++ entries) →
      (∀ entry ∈ entries, ∀ earlier ∈ consumed, earlier.1 ≠ entry.1) →
      (entries.map Prod.fst).Nodup →
      Target.readPayload state (.object ref) (entries.map Prod.fst)
        = .ok (entries.map Prod.snd) state
  | _, [], _, _, _ => by simp [Target.readPayload]
  | consumed, (name, value) :: rest, shape, fresh, distinct => by
      simp only [List.map_cons] at distinct
      obtain ⟨notLater, distinctRest⟩ := List.nodup_cons.mp distinct
      have missing : (consumed.find? fun entry => entry.1 == name) = none := by
        refine List.find?_eq_none.mpr ?_
        intro entry member
        have different := fresh (name, value) (by simp) entry member
        simpa using different
      have read : Target.readMember state name (.object ref) = .ok value state := by
        refine readMember_of_shape state shape name value ?_
        rw [List.find?_append, missing]
        simp
      have shifted :
          Relation.HasOwnFields state.heap ref ((consumed ++ [(name, value)]) ++ rest) := by
        simpa using shape
      have freshRest : ∀ entry ∈ rest, ∀ earlier ∈ consumed ++ [(name, value)],
          earlier.1 ≠ entry.1 := by
        intro entry member earlier earlierMember
        rcases List.mem_append.mp earlierMember with inConsumed | inNew
        · exact fresh entry (by simp [member]) earlier inConsumed
        · have earlierEq : earlier = (name, value) := by simpa using inNew
          subst earlierEq
          intro same
          have nameEq : name = entry.1 := same
          have keyMember : entry.1 ∈ rest.map Prod.fst := List.mem_map_of_mem member
          exact notLater (by rw [nameEq]; exact keyMember)
      simp only [List.map_cons, Target.readPayload, read,
        readPayload_of_entries (consumed ++ [(name, value)]) rest shifted freshRest distinctRest]

/--
The payload of a tagged alternative reads back exactly: reading the constructor's declared field
names off the object the value is represented by answers images representing its arguments, in
declaration order, and changes no state.
-/
theorem readPayload_of_represents {program : Ir.Program} {state : Target.State} {ref : RefId}
    {name : String} {entries : List (String × Value)} {fields : List Ir.Field}
    {arguments : List Source.Value}
    (shape : Relation.HasOwnFields state.heap ref
      (("kind", .primitive (.string (JSString.ofLeanString name))) :: entries))
    (related : Relation.RepresentsArguments program state fields arguments entries)
    (free : ∀ field ∈ fields, field.name ≠ "kind")
    (distinct : (fields.map Ir.Field.name).Nodup) :
    Target.readPayload state (.object ref) (fields.map Ir.Field.name)
      = .ok (entries.map Prod.snd) state := by
  have keys := representsArguments_keys fields arguments entries related
  rw [← keys]
  refine readPayload_of_entries [("kind", .primitive (.string (JSString.ofLeanString name)))]
    entries (by simpa using shape) ?_ (by rw [keys]; exact distinct)
  intro entry member earlier earlierMember
  have earlierEq : earlier = ("kind", .primitive (.string (JSString.ofLeanString name))) := by
    simpa using earlierMember
  subst earlierEq
  have keyMember : entry.1 ∈ fields.map Ir.Field.name := by
    rw [← keys]
    exact List.mem_map_of_mem member
  obtain ⟨field, fieldMember, fieldName⟩ := List.mem_map.mp keyMember
  intro same
  exact free field fieldMember (fieldName.trans same.symm)

/--
The `if` chain of a statement-form match decides the arm whose constructor the value carries, names
that alternative's payload with `const`s, and runs its statements in the scope the source arm sees:
the payload images reversed onto the enclosing scope, which is exactly the scope `evalCases` binds.

Every arm but the last compares the tag the value carries; the last is unconditional, so when the
value decides no arm the source has run out of cases and faults, and a faulting source claims
nothing of the target.
-/
theorem evalArms_refines {program : Ir.Program} {target : Target.Program} {runtime : Runtime}
    {fuel : Nat} {discriminator : Target.Discriminator} {name : String}
    {arguments : List Source.Value} {image : Value} :
    ∀ (cases : List (String × Ir.Expr)) (constructors : List Ir.Constructor)
      (emittedArms : List (String × List String × Target.Body))
      (sourceScope : List Source.Value) (targetScope : List Value) (trace : Source.Trace)
      (state : Target.State),
      EverywhereArms program target runtime fuel constructors cases emittedArms →
      Aligned program sourceScope targetScope trace state →
      Target.discriminate state discriminator image
        = .ok (.primitive (.string (JSString.ofLeanString name))) state →
      (∀ chosen, Ir.constructor? constructors name = some chosen →
        ∃ images, Target.readPayload state image (chosen.fields.map Ir.Field.name)
            = .ok images state ∧
          Relation.RepresentsList program state arguments images) →
      Relation.Refines program state
        (Source.evalCases program fuel sourceScope trace name arguments cases)
        (Target.evalArms target runtime fuel targetScope state image discriminator emittedArms)
  | [], _, _, _, _, _, _, _, _, _, _ => by
      simp only [Source.evalCases]
      exact refines_fault
  | (tag, arm) :: rest, constructors, emittedArms, sourceScope, targetScope, trace, state,
      armsStep, aligned, tagRead, payloadRead => by
      unfold EverywhereArms at armsStep
      obtain ⟨constructor, remaining, emittedArm, restEmitted, constructorsEq, tagEq, emittedEq,
        armStep, restStep⟩ := armsStep
      subst constructorsEq
      subst tagEq
      subst emittedEq
      simp only [Source.evalCases, Target.evalArms]
      by_cases matched : constructor.name = name
      · rw [if_pos matched]
        obtain ⟨images, read, related⟩ :=
          payloadRead constructor (by simp [Ir.constructor?, matched])
        have decided : Target.decideArm state discriminator image constructor.name
            restEmitted.isEmpty = .ok (.primitive (.boolean true)) state := by
          unfold Target.decideArm
          cases final : restEmitted.isEmpty with
          | true => simp
          | false =>
              simp only [Bool.false_eq_true, if_false, tagRead,
                TSLean.Refinement.String.strictEqual_commutes, matched, beq_self_eq_true]
        rw [decided]
        simp only [Value.toBoolean, Primitive.toBoolean, if_true, read]
        refine armStep (arguments.reverse ++ sourceScope) (images.reverse ++ targetScope) trace
          state ⟨aligned.heapValid, aligned.closuresValid, ?_, aligned.trace⟩
        exact represents_append arguments.reverse images.reverse sourceScope targetScope
          (represents_reverse arguments images related) aligned.scope
      · rw [if_neg matched]
        cases final : restEmitted.isEmpty with
        | true =>
            have restEmpty : rest = [] := by
              rcases rest with _ | ⟨⟨secondTag, secondArm⟩, tail⟩
              · rfl
              · unfold EverywhereArms at restStep
                obtain ⟨_, _, _, _, _, _, restEmittedEq, _, _⟩ := restStep
                rw [restEmittedEq] at final
                simp at final
            subst restEmpty
            simp only [Source.evalCases]
            exact refines_fault
        | false =>
            have decided : Target.decideArm state discriminator image constructor.name false
                = .ok (.primitive (.boolean false)) state := by
              unfold Target.decideArm
              have different : (name == constructor.name) = false :=
                beq_eq_false_iff_ne.mpr fun same => matched same.symm
              simp only [Bool.false_eq_true, if_false, tagRead,
                TSLean.Refinement.String.strictEqual_commutes, different]
            rw [decided]
            simp only [Value.toBoolean, Primitive.toBoolean, Bool.false_eq_true, if_false]
            refine evalArms_refines rest remaining restEmitted sourceScope targetScope trace state
              restStep aligned tagRead ?_
            intro chosen selected
            exact payloadRead chosen (by simpa [Ir.constructor?, matched] using selected)

/--
A total case analysis in return position becomes the statement form `emitMatchStatements` builds: the
subject is evaluated once, one `if` per alternative decides it in declaration order with the last
unconditional, and the alternative that decided names its payload with `const`s before running its
own statements.

No re-readability is required of the subject here, and none is assumed: the chain compares the value
the subject already produced, which is what the emitted `const` secures.
-/
theorem branchBody {runtime : Runtime} : ∀ (program : Ir.Program) (target : Target.Program)
    (fuel : Nat) (type : Ir.Ty) (scrutinee : Ir.Expr) (cases : List (String × Ir.Expr))
    (emittedScrutinee : Target.Expr)
    (emittedArms : List (String × List String × Target.Body))
    (discriminator : Target.Discriminator) (constructors : List Ir.Constructor),
    program.constructorsOf type = some constructors →
    type.element? = none →
    (Ir.allNullary constructors = true → discriminator = .tag) →
    (Ir.allNullary constructors = false → discriminator = .tagged) →
    (∀ constructor ∈ constructors, (∀ field ∈ constructor.fields, field.name ≠ "kind") ∧
      (constructor.fields.map Ir.Field.name).Nodup) →
    Everywhere program target runtime fuel scrutinee emittedScrutinee →
    EverywhereArms program target runtime fuel constructors cases emittedArms →
    EverywhereBody program target runtime fuel (.matchOn type scrutinee cases)
      (.branch emittedScrutinee discriminator emittedArms) := by
  intro program target fuel type scrutinee cases emittedScrutinee emittedArms discriminator
    constructors declared notList bareTag taggedObject payloadKeys scrutineeStep armsStep
    sourceScope targetScope trace state aligned
  simp only [Source.eval, Target.evalBody]
  cases scrutineeRun : Source.eval program fuel sourceScope trace scrutinee with
  | fault fault next => exact refines_fault
  | exhausted next =>
      obtain ⟨targetState, targetRun, extension, closuresValid, traceRefines⟩ :=
        refines_exhausted_inv
          (scrutineeRun ▸ scrutineeStep sourceScope targetScope trace state aligned)
      rw [targetRun]
      exact refines_exhausted extension closuresValid traceRefines
  | value produced next =>
      obtain ⟨image, targetState, targetRun, extension, closuresValid, related, traceRefines⟩ :=
        refines_value_inv
          (scrutineeRun ▸ scrutineeStep sourceScope targetScope trace state aligned)
      rw [targetRun]
      have nextAligned := aligned.step extension closuresValid traceRefines
      cases produced with
      | variant valueType valueName valueArguments =>
          dsimp only
          by_cases sameType : valueType = type
          case neg => rw [if_neg sameType]; exact refines_fault
          rw [if_pos sameType]
          subst sameType
          unfold Relation.Represents at related
          obtain ⟨found, foundEq, chosen, selected, body⟩ := related
          rw [declared] at foundEq
          injection foundEq with constructorsEq
          subst constructorsEq
          refine refines_widen extension ?_
          by_cases nullary : Ir.allNullary constructors = true
          · rw [if_pos nullary] at body
            obtain ⟨noArguments, imageEq⟩ := body
            subst noArguments
            subst imageEq
            rw [bareTag nullary]
            refine evalArms_refines cases constructors emittedArms sourceScope targetScope next
              targetState armsStep nextAligned rfl ?_
            intro other otherSelected
            refine ⟨[], ?_, represents_nil⟩
            rw [nullary_fields nullary otherSelected]
            rfl
          · rw [if_neg nullary] at body
            obtain ⟨ref, entries, imageEq, argumentsRelated, shape⟩ := body
            subst imageEq
            rw [taggedObject (by simpa using nullary)]
            obtain ⟨free, distinct⟩ := payloadKeys chosen (List.mem_of_find?_eq_some selected)
            refine evalArms_refines cases constructors emittedArms sourceScope targetScope next
              targetState armsStep nextAligned ?_ ?_
            · simp only [Target.discriminate]
              exact readMember_of_shape targetState shape "kind"
                (.primitive (.string (JSString.ofLeanString valueName))) (by simp)
            · intro other otherSelected
              rw [selected] at otherSelected
              injection otherSelected with chosenEq
              subst chosenEq
              exact ⟨entries.map Prod.snd,
                readPayload_of_represents shape argumentsRelated free distinct,
                representsArguments_values chosen.fields valueArguments entries argumentsRelated⟩
      | array valueElement valueElements =>
          dsimp only
          rw [if_neg (by
            intro listType
            rw [← listType] at notList
            exact absurd notList (by simp [Ir.Ty.element?]))]
          exact refines_fault
      | boolean _ => exact refines_fault
      | nat _ => exact refines_fault
      | int _ => exact refines_fault
      | char _ => exact refines_fault
      | string _ => exact refines_fault
      | record _ _ => exact refines_fault
      | closure _ _ _ => exact refines_fault

/--
A total case analysis becomes one of the two forms `emitter.ts` builds for it: a chain of tag
comparisons where no statement can be emitted, and the statement-form dispatch in return position.
-/
theorem matchOn {runtime : Runtime} : Op.Preserves runtime .matchOn := by
  refine ⟨?_, branchBody⟩
  intro program target fuel type scrutinee cases emittedScrutinee emittedCases chain constructors
    declared nullary readable armsStep built sourceScope targetScope trace state aligned
  simp only [Source.eval]
  rcases readable.sourcePure sourceScope trace with ⟨value, pure⟩ | ⟨fault, pure⟩
  · rw [pure]
    obtain ⟨image, targetState, targetRun, extension, _, related, traceRefines⟩ :=
      refines_value_inv (pure ▸ readable.refines sourceScope targetScope trace state aligned)
    have sameState : targetState = state := readable.targetStable targetScope state image
      targetState targetRun
    rw [sameState] at targetRun related
    cases value with
    | variant valueType valueName valueArguments =>
        dsimp only
        by_cases sameType : valueType = type
        case neg => rw [if_neg sameType]; exact refines_fault
        rw [if_pos sameType]
        subst sameType
        have tagged := tag_of_represents declared nullary related
        subst tagged
        have noArguments : valueArguments = [] := by
          unfold Relation.Represents at related
          obtain ⟨found, foundEq, constructor, selected, body⟩ := related
          rw [declared] at foundEq
          injection foundEq with constructorsEq
          subst constructorsEq
          rw [if_pos nullary] at body
          exact body.1
        subst noArguments
        exact tagChain_refines readable.targetStable cases emittedCases chain valueName sourceScope
          targetScope trace state armsStep built aligned targetRun
    | array valueElement valueElements =>
        dsimp only
        rw [if_neg (by
          intro listType
          have notList := element?_none_of_nullary declared nullary
          rw [← listType] at notList
          exact absurd notList (by simp [Ir.Ty.element?]))]
        exact refines_fault
    | boolean _ => exact refines_fault
    | nat _ => exact refines_fault
    | int _ => exact refines_fault
    | char _ => exact refines_fault
    | string _ => exact refines_fault
    | record _ _ => exact refines_fault
    | closure _ _ _ => exact refines_fault
  · rw [pure]
    exact refines_fault

/-! ## Property reads are own data-property reads -/

/--
Every property read a compiled program performs resolves to an own data property of an object the
same program built, and answers exactly the value it stored there.

This is what makes the null prototype `Target.allocateLiteral` uses unobservable inside the emitted
fragment: a read that always finds an own data property never consults a prototype, so the link the
model omits could not change any answer.
-/
theorem member_reads_own_data_property {program : Ir.Program} {target : Target.Program}
    {runtime : Runtime} {fuel : Nat} {subject : Ir.Expr} {field : String}
    {emittedSubject : Target.Expr}
    (subjectStep : Everywhere program target runtime fuel subject emittedSubject)
    {sourceScope : List Source.Value} {targetScope : List Value} {trace : Source.Trace}
    {state : Target.State} (aligned : Aligned program sourceScope targetScope trace state)
    {value : Source.Value} {next : Source.Trace}
    (sourceRun : Source.eval program fuel sourceScope trace (.fieldGet subject field)
      = .value value next) :
    ∃ ref image final,
      Target.eval target runtime fuel targetScope state emittedSubject
          = .ok (.object ref) final ∧
        final.heap.getOwnProperty ref (Ir.propertyKey field)
          = .ok (some (.data ⟨image, true, true, true⟩)) ∧
        Target.eval target runtime fuel targetScope state (.member emittedSubject field)
          = .ok image final ∧
        Relation.Represents program final value image := by
  simp only [Source.eval] at sourceRun
  cases subjectRun : Source.eval program fuel sourceScope trace subject with
  | fault fault middle => rw [subjectRun] at sourceRun; simp at sourceRun
  | exhausted middle => rw [subjectRun] at sourceRun; simp at sourceRun
  | value produced middle =>
      rw [subjectRun] at sourceRun
      obtain ⟨image, targetState, targetRun, extension, _, related, traceRefines⟩ :=
        refines_value_inv (subjectRun ▸ subjectStep sourceScope targetScope trace state aligned)
      cases produced with
      | boolean _ => simp at sourceRun
      | nat _ => simp at sourceRun
      | int _ => simp at sourceRun
      | char _ => simp at sourceRun
      | string _ => simp at sourceRun
      | array _ _ => simp at sourceRun
      | variant _ _ _ => simp at sourceRun
      | closure _ _ _ => simp at sourceRun
      | record type fields =>
          dsimp only at sourceRun
          unfold Relation.Represents at related
          obtain ⟨ref, entries, imageEq, fieldsRelated, shape⟩ := related
          subst imageEq
          cases lookup : Source.fieldValue? fields field with
          | none => rw [lookup] at sourceRun; simp at sourceRun
          | some found =>
              rw [lookup] at sourceRun
              injection sourceRun with valueEq _
              subst valueEq
              obtain ⟨fieldImage, entryFound, fieldRelated⟩ :=
                fields_lookup fields entries fieldsRelated field found lookup
              refine ⟨ref, fieldImage, targetState, targetRun, ?_, ?_, fieldRelated⟩
              · rw [shape.read field, entryFound]
                rfl
              · simp only [Target.eval, targetRun]
                exact readMember_of_shape targetState shape field fieldImage entryFound

/-! ## The declaration families -/

/--
What one admitted declaration family owes.

A record and an enum have no runtime image — `emitter.ts` gives them an interface or a type alias,
and both erase — so what they owe is that they contribute no runtime declaration *and* that the
representation they induce is exactly the one the refinement relation names. A function owes its
calling convention: the emitted function carries the declared name and arity, and entering it
records one event, spends one unit of fuel, and binds the arguments unchanged in the reversed
positional scope the emitter's parameter list produces.
-/
def Family.Preserves (runtime : Runtime) : Ir.Family → Prop
  | .enum => ∀ (program : Ir.Program) (name : String) (constructors : List Ir.Constructor),
      Compile.declaration program (.enum name constructors) = .ok none ∧
      ∀ (state : Target.State) (type : Ir.Ty) (constructorName : String)
        (arguments : List Source.Value) (image : Value),
        program.constructorsOf type = some constructors →
        Relation.Represents program state (.variant type constructorName arguments) image →
        (Ir.allNullary constructors = true ∧ arguments = [] ∧
            image = .primitive (.string (JSString.ofLeanString constructorName))) ∨
          (Ir.allNullary constructors = false ∧ ∃ ref entries, image = .object ref ∧
            Relation.HasOwnFields state.heap ref
              (("kind", .primitive (.string (JSString.ofLeanString constructorName)))
                :: entries))
  | .record => ∀ (program : Ir.Program) (name constructor : String) (fields : List Ir.Field),
      Compile.declaration program (.record name constructor fields) = .ok none ∧
      ∀ (state : Target.State) (type : Ir.Ty) (values : List (String × Source.Value))
        (image : Value),
        Relation.Represents program state (.record type values) image →
        ∃ ref entries, image = .object ref ∧
          Relation.HasOwnFields state.heap ref entries ∧
          entries.map Prod.fst = values.map Prod.fst ∧
          state.heap.ownPropertyKeys ref = .ok ((values.map Prod.fst).map Ir.propertyKey)
  | .function => ∀ (program : Ir.Program) (target : Target.Program) (fuel : Nat) (name : String)
      (parameters : List Ir.Field) (result : Ir.Ty) (recursion : Ir.Recursion) (body : Ir.Expr)
      (emittedBody : Target.Body) (emitted : Target.Function),
      Compile.returnBody program body = .ok emittedBody →
      Compile.declaration program (.function name parameters result recursion body)
        = .ok (some emitted) →
      emitted.name = name ∧ emitted.parameters = parameters.length ∧
        emitted.body = emittedBody ∧
        ∀ (arguments : List Value) (state : Target.State) (declaration : Target.Function),
          target.find? name = some declaration →
          declaration.parameters = arguments.length →
          Target.enter target runtime (fuel + 1) state name arguments
            = Target.evalBody target runtime fuel arguments.reverse
                (state.record (.function name arguments)) declaration.body
  | .foreign => ∀ (program : Ir.Program) (target : Target.Program) (fuel : Nat) (name : String)
      (host : Ir.HostOp) (parameters : List Ir.Field) (result : Ir.Ty) (reference : Ir.Expr)
      (emittedReference : Target.Body) (emitted : Target.Function),
      Compile.returnBody program reference = .ok emittedReference →
      Compile.declaration program (.foreign name host parameters result reference)
        = .ok (some emitted) →
      emitted.name = name ∧ emitted.parameters = parameters.length ∧
        emitted.body = emittedReference ∧
        program.function? name
          = (match program.find? name with
            | some (.function _ functionParameters functionResult functionRecursion functionBody) =>
                some (functionParameters, functionResult, functionRecursion, functionBody)
            | some (.foreign _ _ foreignParameters foreignResult foreignReference) =>
                some (foreignParameters, foreignResult, .nonrecursive, foreignReference)
            | _ => none) ∧
        ∀ (arguments : List Value) (state : Target.State) (declaration : Target.Function),
          target.find? name = some declaration →
          declaration.parameters = arguments.length →
          Target.enter target runtime (fuel + 1) state name arguments
            = Target.evalBody target runtime fuel arguments.reverse
                (state.record (.function name arguments)) declaration.body

/-- An enum contributes no runtime declaration, and its values are the tag or the tagged object. -/
theorem familyEnum {runtime : Runtime} : Family.Preserves runtime .enum := by
  intro program name constructors
  refine ⟨rfl, ?_⟩
  intro state type constructorName arguments image declared related
  unfold Relation.Represents at related
  obtain ⟨found, foundEq, constructor, selected, body⟩ := related
  rw [declared] at foundEq
  injection foundEq with constructorsEq
  subst constructorsEq
  by_cases nullary : Ir.allNullary constructors = true
  · rw [if_pos nullary] at body
    exact Or.inl ⟨nullary, body.1, body.2⟩
  · rw [if_neg nullary] at body
    obtain ⟨ref, entries, imageEq, _, shape⟩ := body
    exact Or.inr ⟨by simpa using nullary, ref, entries, imageEq, shape⟩

/-- A record contributes no runtime declaration, and its values are objects whose own keys are the
declared field keys in declaration order. -/
theorem familyRecord {runtime : Runtime} : Family.Preserves runtime .record := by
  intro program name constructor fields
  refine ⟨rfl, ?_⟩
  intro state type values image related
  unfold Relation.Represents at related
  obtain ⟨ref, entries, imageEq, fieldsRelated, shape⟩ := related
  refine ⟨ref, entries, imageEq, shape, representsFields_names values entries fieldsRelated, ?_⟩
  rw [shape.keys, ← representsFields_names values entries fieldsRelated, List.map_map]
  rfl

/-- A function contributes exactly one emitted function with its declared name and arity, and
entering it records one event, spends one unit of fuel, and binds its arguments in reverse. -/
theorem familyFunction {runtime : Runtime} : Family.Preserves runtime .function := by
  intro program target fuel name parameters result recursion body emittedBody emitted lowered
    declared
  simp only [Compile.declaration, lowered] at declared
  injection declared with emittedEq
  injection emittedEq with emittedEq
  subst emittedEq
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro arguments state emittedDeclaration found arity
  simp only [Target.enter, found]
  rw [bindArguments_exact arguments emittedDeclaration.parameters arity]

/-! ## Closure -/

/--
The closure over the IR expression registry. It is a total function on `Ir.Op`, so an operation with
no theorem does not compile, and a theorem whose statement drifts from the operation's lowering does
not typecheck here.
-/
theorem registry (runtime : Runtime) : (op : Ir.Op) → Op.Preserves runtime op
  | .varRef => varRef
  | .boolLit => boolLit
  | .natLit => natLit
  | .stringLit => stringLit
  | .letBind => letBind
  | .fieldGet => fieldGet
  | .ifThenElse => ifThenElse
  | .operation => operation
  | .variant => variant
  | .record => record
  | .matchOn => matchOn
  | .lambda => lambda
  | .apply => apply
  | .call => call

/--
A host boundary lowers to a function carrying its reference body, and entering it is entering that
body. The source semantics resolves the name to the same reference, so the two sides run one body;
what the substrate's own implementation does is the separate premise `Program.HostSubstrate`.
-/
theorem familyForeign {runtime : Runtime} : Family.Preserves runtime .foreign := by
  intro program target fuel name host parameters result reference emittedReference emitted lowered
    declared
  simp only [Compile.declaration, lowered] at declared
  injection declared with emittedEq
  injection emittedEq with emittedEq
  subst emittedEq
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro arguments state emittedDeclaration found arity
  simp only [Target.enter, found]
  rw [bindArguments_exact arguments emittedDeclaration.parameters arity]

theorem familyRegistry (runtime : Runtime) : (family : Ir.Family) → Family.Preserves runtime family
  | .enum => familyEnum
  | .record => familyRecord
  | .function => familyFunction
  | .foreign => familyForeign

end Preservation

end TSLean.LeanToTypeScript.Semantics
