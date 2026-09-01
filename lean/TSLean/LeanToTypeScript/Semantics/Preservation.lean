import TSLean.Refinement.Primitive
import TSLean.Refinement.String
import TSLean.LeanToTypeScript.Semantics.Allocation
import TSLean.LeanToTypeScript.Semantics.Closure
import TSLean.LeanToTypeScript.Semantics.Compile

/-!
# Preservation, one theorem per admitted IR operation

`Op.Preserves` states, for each operation of `Ir.Op`, the correspondence that operation's own
lowering claims: given that each subexpression's lowering refines it from every aligned
configuration, the lowered whole refines the whole. `registry` is a total function on `Ir.Op`, so an
operation with no theorem does not compile.

`Family.Preserves` does the same for the three declaration families.
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
  ∀ (name : String) (parameters : List Ir.Field) (result : Ir.Ty) (recursion : Option Nat)
    (body : Ir.Expr),
    program.function? name = some (parameters, result, recursion, body) →
    ∃ emitted, target.find? name = some emitted ∧ emitted.parameters = parameters.length

/-- Every declared function's lowered body refines it, at this fuel. -/
def EveryFunction (program : Ir.Program) (target : Target.Program) (fuel : Nat) : Prop :=
  ∀ (name : String) (parameters : List Ir.Field) (result : Ir.Ty) (recursion : Option Nat)
    (body : Ir.Expr) (emitted : Target.Function),
    program.function? name = some (parameters, result, recursion, body) →
    target.find? name = some emitted →
    EverywhereBody program target runtime fuel body emitted.body

/-! ## Support -/

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
  | .absent, _, related => by
      unfold Relation.Represents at related; subst related; rfl
  | .present inner, target, related => by
      unfold Relation.Represents at related
      exact valueValid_of_represents inner target related
  | .record _ _, _, related => by
      unfold Relation.Represents at related
      obtain ⟨ref, entries, targetEq, _, shape⟩ := related
      subst targetEq
      exact Relation.valueValid_of_hasOwnFields shape
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
def StateStable (target : Target.Program) (fuel : Nat) (emitted : Target.Expr) : Prop :=
  ∀ (targetScope : List Value) (state : Target.State) (produced : Value) (next : Target.State),
    Target.eval target runtime fuel targetScope state emitted = .ok produced next → next = state

/--
A scrutinee the tag chain may read once per arm, and may also drop.

The chain evaluates the scrutinee once per comparison and, when the match has one arm, not at all.
Both are unobservable exactly when reading the scrutinee produces no event, spends no fuel and
changes no state, which is what `emitter.ts` restricts the scrutinee to a binding or a field read to
secure.
-/
structure Readable (program : Ir.Program) (target : Target.Program) (fuel : Nat)
    (scrutinee : Ir.Expr) (emitted : Target.Expr) : Prop where
  refines : Everywhere program target runtime fuel scrutinee emitted
  sourcePure : ∀ (sourceScope : List Source.Value) (trace : Source.Trace),
    (∃ value, Source.eval program fuel sourceScope trace scrutinee = .value value trace) ∨
      (∃ fault, Source.eval program fuel sourceScope trace scrutinee = .fault fault trace)
  targetStable : StateStable target fuel emitted

/-! ## The obligation each operation carries -/

/-- Each arm's lowering refines it, arm for arm and tag for tag. -/
def EverywhereCases (program : Ir.Program) (target : Target.Program) (fuel : Nat) :
    List (String × Ir.Expr) → List (String × Target.Expr) → Prop
  | [], emitted => emitted = []
  | (tag, arm) :: rest, emitted =>
      ∃ (emittedArm : Target.Expr) (restEmitted : List (String × Target.Expr)),
        emitted = (tag, emittedArm) :: restEmitted ∧
          Everywhere program target runtime fuel arm emittedArm ∧
          EverywhereCases program target runtime fuel rest restEmitted

/--
What one admitted IR operation owes: given that each of its subexpressions' lowerings refines it from
every aligned configuration, its own lowering refines it. The lowering named in each clause is
exactly the one `src/lean-to-typescript/emitter.ts` builds for that operation.
-/
def Op.Preserves : Ir.Op → Prop
  | .varRef => ∀ (program : Ir.Program) (target : Target.Program) (fuel index : Nat),
      Everywhere program target runtime fuel (.varRef index) (.binding index)
  | .boolLit => ∀ (program : Ir.Program) (target : Target.Program) (fuel : Nat) (value : Bool),
      Everywhere program target runtime fuel (.boolLit value) (.boolLit value)
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
  | .ifThenElse => ∀ (program : Ir.Program) (target : Target.Program) (fuel : Nat)
      (condition consequent alternate : Ir.Expr)
      (emittedCondition emittedConsequent emittedAlternate : Target.Expr),
      Everywhere program target runtime fuel condition emittedCondition →
      Everywhere program target runtime fuel consequent emittedConsequent →
      Everywhere program target runtime fuel alternate emittedAlternate →
      Everywhere program target runtime fuel (.ifThenElse condition consequent alternate)
        (.conditional emittedCondition emittedConsequent emittedAlternate)
  | .boolEquals => ∀ (program : Ir.Program) (target : Target.Program) (fuel : Nat)
      (left right : Ir.Expr) (emittedLeft emittedRight : Target.Expr),
      Everywhere program target runtime fuel left emittedLeft →
      Everywhere program target runtime fuel right emittedRight →
      Everywhere program target runtime fuel (.boolEquals left right)
          (.strictEquals emittedLeft emittedRight) ∧
        Everywhere program target runtime fuel (.boolEquals left (.boolLit true)) emittedLeft ∧
        Everywhere program target runtime fuel (.boolEquals (.boolLit true) right) emittedRight
  | .boolAnd => ∀ (program : Ir.Program) (target : Target.Program) (fuel : Nat)
      (left right : Ir.Expr) (emittedLeft emittedRight : Target.Expr),
      Everywhere program target runtime fuel left emittedLeft →
      Everywhere program target runtime fuel right emittedRight →
      Everywhere program target runtime fuel (.boolAnd left right) (.logicalAnd emittedLeft emittedRight)
  | .boolOr => ∀ (program : Ir.Program) (target : Target.Program) (fuel : Nat)
      (left right : Ir.Expr) (emittedLeft emittedRight : Target.Expr),
      Everywhere program target runtime fuel left emittedLeft →
      Everywhere program target runtime fuel right emittedRight →
      Everywhere program target runtime fuel (.boolOr left right) (.logicalOr emittedLeft emittedRight)
  | .boolNot => ∀ (program : Ir.Program) (target : Target.Program) (fuel : Nat)
      (operand : Ir.Expr) (emittedOperand : Target.Expr),
      Everywhere program target runtime fuel operand emittedOperand →
      Everywhere program target runtime fuel (.boolNot operand) (.logicalNot emittedOperand)
  | .someValue => ∀ (program : Ir.Program) (target : Target.Program) (fuel : Nat)
      (value : Ir.Expr) (emitted : Target.Expr),
      Everywhere program target runtime fuel value emitted →
      Everywhere program target runtime fuel (.someValue value) emitted
  | .noneValue => ∀ (program : Ir.Program) (target : Target.Program) (fuel : Nat),
      Everywhere program target runtime fuel .noneValue .undefinedLit
  | .variant => ∀ (program : Ir.Program) (target : Target.Program) (fuel : Nat)
      (type name : String) (constructors : List Ir.Constructor) (constructor : Ir.Constructor)
      (arguments : List Ir.Expr) (emittedArguments : List Target.Expr),
      program.enum? type = some constructors →
      Ir.constructor? constructors name = some constructor →
      (∀ field ∈ constructor.fields, Ir.ValidKey field.name ∧ field.name ≠ "kind") →
      (constructor.fields.map Ir.Field.name).Nodup →
      constructor.fields.length = arguments.length →
      arguments.length = emittedArguments.length →
      EverywhereList program target runtime fuel arguments emittedArguments →
      (Ir.allNullary constructors = true →
          Everywhere program target runtime fuel (.variant type name arguments) (.stringLit name)) ∧
        (Ir.allNullary constructors = false →
          Everywhere program target runtime fuel (.variant type name arguments)
            (.objectLiteral (("kind", .stringLit name) ::
              (constructor.fields.map Ir.Field.name).zip emittedArguments)))
  | .record => ∀ (program : Ir.Program) (target : Target.Program) (fuel : Nat) (type : String)
      (fields : List (String × Ir.Expr)) (emittedFields : List (String × Target.Expr)),
      (∀ field ∈ fields, Ir.ValidKey field.1) →
      (fields.map Prod.fst).Nodup →
      EverywhereFields program target runtime fuel fields emittedFields →
      Everywhere program target runtime fuel (.record type fields) (.objectLiteral emittedFields)
  | .matchOn => ∀ (program : Ir.Program) (target : Target.Program) (fuel : Nat) (type : String)
      (scrutinee : Ir.Expr) (cases : List (String × Ir.Expr)) (emittedScrutinee : Target.Expr)
      (emittedCases : List (String × Target.Expr)) (chain : Target.Expr)
      (constructors : List Ir.Constructor),
      program.enum? type = some constructors →
      Ir.allNullary constructors = true →
      Readable program target fuel scrutinee emittedScrutinee →
      EverywhereCases program target runtime fuel cases emittedCases →
      Compile.tagChain emittedScrutinee emittedCases = some chain →
      Everywhere program target runtime fuel (.matchOn type scrutinee cases) chain
  | .call => ∀ (program : Ir.Program) (target : Target.Program) (fuel : Nat) (function : String)
      (arguments : List Ir.Expr) (emittedArguments : List Target.Expr),
      Lowered program target →
      EverywhereList program target runtime fuel arguments emittedArguments →
      (∀ smaller, smaller + 1 = fuel → EveryFunction program target smaller) →
      Everywhere program target runtime fuel (.call function arguments)
        (.callFunction function emittedArguments)
  | .lambda => ∀ (program : Ir.Program) (target : Target.Program) (fuel : Nat)
      (parameters : List Ir.Field) (body : Ir.Expr) (emittedBody : Target.Body),
      Compile.body program body = .ok emittedBody →
      EverywhereBody program target runtime fuel body emittedBody →
      Everywhere program target runtime fuel (.lambda parameters body) (.arrow ⟨parameters, body⟩ emittedBody)
  | .apply => ∀ (program : Ir.Program) (target : Target.Program) (fuel index : Nat)
      (arguments : List Ir.Expr) (emittedArguments : List Target.Expr),
      EverywhereList program target runtime fuel arguments emittedArguments →
      (∀ smaller, smaller + 1 = fuel → ∀ body emittedBody,
        Compile.body program body = .ok emittedBody →
        EverywhereBody program target runtime smaller body emittedBody) →
      Everywhere program target runtime fuel (.apply (.varRef index) arguments)
        (.callValue (.binding index) emittedArguments)

/-! ## The theorems -/

/-- A binding read resolves positionally on both sides, and reads nothing else. -/
theorem varRef : Op.Preserves .varRef := by
  intro program target fuel index sourceScope targetScope trace state aligned
  simp only [Source.eval, Target.eval]
  cases sourceLookup : Source.lookup sourceScope index with
  | none => exact refines_fault
  | some value =>
      obtain ⟨image, targetLookup, related⟩ :=
        lookup_represents sourceScope targetScope index aligned.scope value sourceLookup
      rw [targetLookup]
      exact refines_value (Target.State.Extension.refl state aligned.heapValid) aligned.closuresValid
        related aligned.trace

/-- A `Bool` literal is a JavaScript boolean literal. -/
theorem boolLit : Op.Preserves .boolLit := by
  intro program target fuel value sourceScope targetScope trace state aligned
  simp only [Source.eval, Target.eval]
  refine refines_value (Target.State.Extension.refl state aligned.heapValid) aligned.closuresValid
    ?_ aligned.trace
  unfold Relation.Represents
  rfl

/-- `Option.none` is `undefined`. -/
theorem noneValue : Op.Preserves .noneValue := by
  intro program target fuel sourceScope targetScope trace state aligned
  simp only [Source.eval, Target.eval]
  refine refines_value (Target.State.Extension.refl state aligned.heapValid) aligned.closuresValid
    ?_ aligned.trace
  unfold Relation.Represents
  rfl

/-- `Option.some x` is whatever `x` is: the representation carries no tag, which is why the exporter
refuses a nested `Option`. -/
theorem someValue : Op.Preserves .someValue := by
  intro program target fuel value emitted inner sourceScope targetScope trace state aligned
  simp only [Source.eval]
  cases sourceRun : Source.eval program fuel sourceScope trace value with
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
      refine refines_value extension closuresValid ?_ traceRefines
      unfold Relation.Represents
      exact related

/-- `!` on a JavaScript boolean is `Bool.not`. -/
theorem boolNot : Op.Preserves .boolNot := by
  intro program target fuel operand emittedOperand inner sourceScope targetScope trace state aligned
  simp only [Source.eval, Target.eval]
  cases sourceRun : Source.eval program fuel sourceScope trace operand with
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
      | boolean flag =>
          unfold Relation.Represents at related
          subst related
          refine refines_value extension closuresValid ?_ traceRefines
          unfold Relation.Represents
          rfl
      | absent => exact refines_fault
      | present _ => exact refines_fault
      | record _ _ => exact refines_fault
      | variant _ _ _ => exact refines_fault
      | closure _ _ _ => exact refines_fault

/-- `&&` is `Bool.and`, including its laziness: ECMAScript returns the left operand when it is
falsy, and never evaluates the right one there. -/
theorem boolAnd : Op.Preserves .boolAnd := by
  intro program target fuel left right emittedLeft emittedRight leftStep rightStep
    sourceScope targetScope trace state aligned
  simp only [Source.eval, Target.eval]
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
              simp only [Value.toBoolean, Primitive.toBoolean]
              refine refines_value extension closuresValid ?_ traceRefines
              unfold Relation.Represents
              rfl
          | true =>
              simp only [Value.toBoolean, Primitive.toBoolean, if_true]
              have nextAligned := aligned.step extension closuresValid traceRefines
              cases rightRun : Source.eval program fuel sourceScope next right with
              | fault fault last => exact refines_fault
              | exhausted last =>
                  obtain ⟨lastState, lastRun, lastExtension, lastClosuresValid, lastTrace⟩ :=
                    refines_exhausted_inv
                      (rightRun ▸ rightStep sourceScope targetScope next targetState nextAligned)
                  rw [lastRun]
                  exact refines_exhausted (extension.trans lastExtension) lastClosuresValid lastTrace
              | value second last =>
                  obtain ⟨secondImage, lastState, lastRun, lastExtension, lastClosuresValid,
                    secondRelated, lastTrace⟩ :=
                    refines_value_inv
                      (rightRun ▸ rightStep sourceScope targetScope next targetState nextAligned)
                  rw [lastRun]
                  cases second with
                  | boolean secondFlag =>
                      exact refines_value (extension.trans lastExtension) lastClosuresValid
                        secondRelated lastTrace
                  | absent => exact refines_fault
                  | present _ => exact refines_fault
                  | record _ _ => exact refines_fault
                  | variant _ _ _ => exact refines_fault
                  | closure _ _ _ => exact refines_fault
      | absent => exact refines_fault
      | present _ => exact refines_fault
      | record _ _ => exact refines_fault
      | variant _ _ _ => exact refines_fault
      | closure _ _ _ => exact refines_fault

/-- `||` is `Bool.or`, including its laziness. -/
theorem boolOr : Op.Preserves .boolOr := by
  intro program target fuel left right emittedLeft emittedRight leftStep rightStep
    sourceScope targetScope trace state aligned
  simp only [Source.eval, Target.eval]
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
              simp only [Value.toBoolean, Primitive.toBoolean]
              have nextAligned := aligned.step extension closuresValid traceRefines
              cases rightRun : Source.eval program fuel sourceScope next right with
              | fault fault last => exact refines_fault
              | exhausted last =>
                  obtain ⟨lastState, lastRun, lastExtension, lastClosuresValid, lastTrace⟩ :=
                    refines_exhausted_inv
                      (rightRun ▸ rightStep sourceScope targetScope next targetState nextAligned)
                  rw [lastRun]
                  exact refines_exhausted (extension.trans lastExtension) lastClosuresValid lastTrace
              | value second last =>
                  obtain ⟨secondImage, lastState, lastRun, lastExtension, lastClosuresValid,
                    secondRelated, lastTrace⟩ :=
                    refines_value_inv
                      (rightRun ▸ rightStep sourceScope targetScope next targetState nextAligned)
                  rw [lastRun]
                  cases second with
                  | boolean secondFlag =>
                      exact refines_value (extension.trans lastExtension) lastClosuresValid
                        secondRelated lastTrace
                  | absent => exact refines_fault
                  | present _ => exact refines_fault
                  | record _ _ => exact refines_fault
                  | variant _ _ _ => exact refines_fault
                  | closure _ _ _ => exact refines_fault
      | absent => exact refines_fault
      | present _ => exact refines_fault
      | record _ _ => exact refines_fault
      | variant _ _ _ => exact refines_fault
      | closure _ _ _ => exact refines_fault

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

/-- `? :` selects by truthiness, and a represented `Bool` is truthy exactly when it is `true`. -/
theorem ifThenElse : Op.Preserves .ifThenElse := by
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
      | absent => exact refines_fault
      | present _ => exact refines_fault
      | record _ _ => exact refines_fault
      | variant _ _ _ => exact refines_fault
      | closure _ _ _ => exact refines_fault

/-- `===` on two represented `Bool`s is `Bool` equality, and the two folds the emitter performs when
one side is the `true` literal agree with it. -/
theorem boolEquals : Op.Preserves .boolEquals := by
  intro program target fuel left right emittedLeft emittedRight leftStep rightStep
  refine ⟨?_, ?_, ?_⟩
  · intro sourceScope targetScope trace state aligned
    simp only [Source.eval, Target.eval]
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
            dsimp only
            have nextAligned := aligned.step extension closuresValid traceRefines
            cases rightRun : Source.eval program fuel sourceScope next right with
            | fault fault last => exact refines_fault
            | exhausted last =>
                obtain ⟨lastState, lastRun, lastExtension, lastClosuresValid, lastTrace⟩ :=
                  refines_exhausted_inv
                    (rightRun ▸ rightStep sourceScope targetScope next targetState nextAligned)
                rw [lastRun]
                exact refines_exhausted (extension.trans lastExtension) lastClosuresValid lastTrace
            | value second last =>
                obtain ⟨secondImage, lastState, lastRun, lastExtension, lastClosuresValid,
                  secondRelated, lastTrace⟩ :=
                  refines_value_inv
                    (rightRun ▸ rightStep sourceScope targetScope next targetState nextAligned)
                rw [lastRun]
                cases second with
                | boolean secondFlag =>
                    unfold Relation.Represents at secondRelated
                    subst secondRelated
                    refine refines_value (extension.trans lastExtension) lastClosuresValid ?_ lastTrace
                    unfold Relation.Represents
                    rw [TSLean.Refinement.Bool.strictEqual_commutes flag secondFlag]
                | absent => exact refines_fault
                | present _ => exact refines_fault
                | record _ _ => exact refines_fault
                | variant _ _ _ => exact refines_fault
                | closure _ _ _ => exact refines_fault
        | absent => exact refines_fault
        | present _ => exact refines_fault
        | record _ _ => exact refines_fault
        | variant _ _ _ => exact refines_fault
        | closure _ _ _ => exact refines_fault
  · intro sourceScope targetScope trace state aligned
    simp only [Source.eval]
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
            dsimp only
            refine refines_value extension closuresValid ?_ traceRefines
            unfold Relation.Represents
            cases flag <;> rfl
        | absent => exact refines_fault
        | present _ => exact refines_fault
        | record _ _ => exact refines_fault
        | variant _ _ _ => exact refines_fault
        | closure _ _ _ => exact refines_fault
  · intro sourceScope targetScope trace state aligned
    simp only [Source.eval]
    cases rightRun : Source.eval program fuel sourceScope trace right with
    | fault fault next => exact refines_fault
    | exhausted next =>
        obtain ⟨targetState, targetRun, extension, closuresValid, traceRefines⟩ :=
          refines_exhausted_inv (rightRun ▸ rightStep sourceScope targetScope trace state aligned)
        rw [targetRun]
        exact refines_exhausted extension closuresValid traceRefines
    | value produced next =>
        obtain ⟨image, targetState, targetRun, extension, closuresValid, related, traceRefines⟩ :=
          refines_value_inv (rightRun ▸ rightStep sourceScope targetScope trace state aligned)
        rw [targetRun]
        cases produced with
        | boolean flag =>
            unfold Relation.Represents at related
            subst related
            refine refines_value extension closuresValid ?_ traceRefines
            unfold Relation.Represents
            cases flag <;> rfl
        | absent => exact refines_fault
        | present _ => exact refines_fault
        | record _ _ => exact refines_fault
        | variant _ _ _ => exact refines_fault
        | closure _ _ _ => exact refines_fault

/-- A declared field read is an own-property read of the object the record is represented by. -/
theorem fieldGet : Op.Preserves .fieldGet := by
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
      | absent => exact refines_fault
      | present _ => exact refines_fault
      | variant _ _ _ => exact refines_fault
      | closure _ _ _ => exact refines_fault

/-- A leading `let` becomes a `const` binding, and the body sees it at the same position. -/
theorem letBind : Op.Preserves .letBind := by
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
theorem refinesFields_exhausted_inv {program : Ir.Program} {start : Target.State} {trace : Source.Trace}
    {result : Target.NamedListResult}
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
theorem refinesList_exhausted_inv {program : Ir.Program} {start : Target.State} {trace : Source.Trace}
    {result : Target.ListResult}
    (refines : Relation.RefinesList program start (.exhausted trace) result) :
    ∃ state, result = .exhausted state ∧ Target.State.Extension start state ∧
      state.ClosuresWellFormed ∧ Relation.RefinesTrace program state trace state.trace := by
  cases result with
  | ok targets state => simp only [Relation.RefinesList] at refines
  | thrown error state => simp only [Relation.RefinesList] at refines
  | fault fault state => simp only [Relation.RefinesList] at refines
  | exhausted state => exact ⟨state, rfl, refines.1, refines.2.1, refines.2.2⟩

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
theorem record : Op.Preserves .record := by
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
      obtain ⟨entries, targetState, targetRun, extension, closuresValid, fieldsRelated, traceRefines⟩ :=
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
theorem call : Op.Preserves .call := by
  intro program target fuel function arguments emittedArguments lowered argumentsStep functions
    sourceScope targetScope trace state aligned
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
      obtain ⟨targets, targetState, targetRun, extension, closuresValid, listRelated, traceRefines⟩ :=
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
theorem lambda : Op.Preserves .lambda := by
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

/--
An inline application evaluates the bound closure, then its arguments left to right, reads the
closure's exact captured own properties, checks them against its internal payload, records one
anonymous application event carrying the exact lambda code, spends one unit of fuel, and enters the
stored compiled body with reversed arguments above the captured scope.
-/
theorem apply : Op.Preserves .apply := by
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
      | absent => exact refines_fault
      | present _ => exact refines_fault
      | record _ _ => exact refines_fault
      | variant _ _ _ => exact refines_fault
      | closure captured parameters body =>
          dsimp only
          unfold Relation.Represents at calleeRelated
          obtain ⟨ref, closure, imageEq, closureFound, codeEq, compiledBody, capturedRelated,
            shape⟩ := calleeRelated
          subst imageEq
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
              simp only [Target.invoke]
              have movedClosure : targetState.lookupClosure ref = some closure :=
                extension.closures ref closure closureFound
              have movedCaptured :
                  Relation.RepresentsList program targetState captured closure.captured :=
                Relation.RepresentsList.stable extension captured closure.captured capturedRelated
              have movedShape : Relation.HasOwnFields targetState.heap ref
                  (Ir.closureEntries closure.captured) := shape.stable extension.heap
              rw [movedClosure]
              dsimp only
              rw [Closure.read_captured_all movedShape]
              dsimp only
              rw [if_pos rfl]
              unfold Source.applyClosure
              by_cases arity : parameters.length = produced.length
              · rw [if_pos arity]
                have targetArity : closure.code.parameters.length = targets.length := by
                  simp only [codeEq]
                  rw [arity, representsList_length produced targets listRelated]
                rw [bindArguments_exact targets closure.code.parameters.length targetArity]
                cases fuel with
                | zero => exact refines_exhausted extension closuresValid traceRefines
                | succ remaining =>
                    dsimp only
                    have recorded := Target.State.record_extension targetState
                      (.application closure.code targets) extension.nextWellFormed
                    refine refines_widen extension ?_
                    refine refines_widen recorded ?_
                    refine bodyAtLower remaining rfl body closure.body compiledBody
                      (produced.reverse ++ captured) (targets.reverse ++ closure.captured)
                      (next ++ [.application ⟨parameters, body⟩ produced])
                      (targetState.record (.application closure.code targets)) ?_
                    refine ⟨extension.nextWellFormed, closuresValid, ?_, ?_⟩
                    · exact represents_append produced.reverse targets.reverse captured
                        closure.captured
                        (Relation.RepresentsList.stable recorded produced.reverse targets.reverse
                          (represents_reverse produced targets listRelated))
                        (Relation.RepresentsList.stable recorded captured closure.captured
                          movedCaptured)
                    · exact refinesTrace_append next targetState.trace
                        (.application ⟨parameters, body⟩ produced)
                        (.application closure.code targets)
                        (Relation.RefinesTrace.stable recorded next targetState.trace traceRefines)
                        ⟨codeEq.symm,
                          Relation.RepresentsList.stable recorded produced targets listRelated⟩
              · rw [if_neg arity]
                exact refines_fault

/-! ## The two constraints the decoder enforces, stated -/

/-- A lambda captures exactly the enclosing binders, in scope order. -/
theorem lambda_captures_enclosing_scope (program : Ir.Program) (fuel : Nat)
    (parameters : List Ir.Field) (body : Ir.Expr) (scope : List Source.Value)
    (trace : Source.Trace) :
    Source.eval program fuel scope trace (.lambda parameters body)
      = .value (.closure scope parameters body) trace := by
  simp only [Source.eval]

/--
An application's callee is a bound variable. `src/lean-to-typescript/ir.ts` admits nothing else, and
the lowering refuses anything else rather than inventing a form for it, so every application the
model lowers is one the `apply` theorem covers.
-/
theorem apply_callee_is_bound {program : Ir.Program} {callee : Ir.Expr}
    {arguments : List Ir.Expr} {emitted : Target.Expr}
    (compiled : Compile.expr program (.apply callee arguments) = .ok emitted) :
    ∃ index, callee = .varRef index := by
  cases callee
  case varRef index => exact ⟨index, rfl⟩
  all_goals simp [Compile.expr, throw, throwThe, MonadExceptOf.throw] at compiled

/-- A named property list whose values are an argument list evaluates to those arguments' values,
paired with the names in order. -/
theorem evalProperties_zip_ok {target : Target.Program} {fuel : Nat} {targetScope : List Value} :
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
          cases tailRun : Target.evalList target runtime fuel targetScope middle restExpressions with
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
theorem evalProperties_zip_exhausted {target : Target.Program} {fuel : Nat}
    {targetScope : List Value} :
    ∀ (names : List String) (expressions : List Target.Expr) (state : Target.State)
      (next : Target.State),
      names.length = expressions.length →
      Target.evalList target runtime fuel targetScope state expressions = .exhausted next →
      Target.evalProperties target runtime fuel targetScope state (names.zip expressions) = .exhausted next
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
          cases tailRun : Target.evalList target runtime fuel targetScope middle restExpressions with
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

/-- An enum with no payload anywhere declares only nullary constructors. -/
theorem nullary_fields {constructors : List Ir.Constructor} {name : String}
    {constructor : Ir.Constructor} (nullary : Ir.allNullary constructors = true)
    (selected : Ir.constructor? constructors name = some constructor) : constructor.fields = [] := by
  unfold Ir.allNullary at nullary
  have member : constructor ∈ constructors := List.mem_of_find?_eq_some selected
  have empty := (List.all_eq_true.mp nullary) constructor member
  exact List.isEmpty_iff.mp empty

/--
A constructor value is the representation the emitter builds for it: an enum with no payload
anywhere becomes its own tag string, and every other enum becomes an object carrying `kind` and then
the constructor's declared fields.
-/
theorem variant : Op.Preserves .variant := by
  intro program target fuel type name constructors constructor arguments emittedArguments
    declared selected keys distinct arity emittedArity argumentsStep
  refine ⟨?_, ?_⟩
  · intro nullary sourceScope targetScope trace state aligned
    have noFields := nullary_fields nullary selected
    have noArguments : arguments = [] := by
      rw [noFields] at arity
      exact List.eq_nil_of_length_eq_zero arity.symm
    subst noArguments
    simp only [Source.eval, Source.evalList, Target.eval]
    refine refines_value (Target.State.Extension.refl state aligned.heapValid) aligned.closuresValid
      ?_ aligned.trace
    unfold Relation.Represents
    refine ⟨constructors, declared, constructor, selected, ?_⟩
    rw [if_pos nullary]
    exact ⟨rfl, rfl⟩
  · intro carries sourceScope targetScope trace state aligned
    simp only [Source.eval, Target.eval, Target.evalProperties]
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
        obtain ⟨targets, targetState, targetRun, extension, closuresValid, listRelated, traceRefines⟩ :=
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
        obtain ⟨ref, final, allocated, traceEq, _, finalExtension, finalClosuresValid, _, shape⟩ :=
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
              · have valueMember : entry.2 ∈ targets := by
                  have := List.of_mem_zip tail
                  exact this.2
                exact representsList_valuesValid produced targets listRelated entry.2 valueMember)
        rw [allocated]
        refine refines_value (extension.trans finalExtension) finalClosuresValid ?_ ?_
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

/-- A represented tag is the constructor's own name as a JavaScript string. -/
theorem tag_of_represents {program : Ir.Program} {state : Target.State} {type name : String}
    {arguments : List Source.Value} {image : Value} {constructors : List Ir.Constructor}
    (declared : program.enum? type = some constructors)
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

/-- The tag chain decides the arm whose tag the scrutinee carries, reading the scrutinee once per
comparison without that repetition being observable. -/
theorem tagChain_refines {program : Ir.Program} {target : Target.Program} {fuel : Nat}
    {emittedScrutinee : Target.Expr} (stable : StateStable target fuel emittedScrutinee) :
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
              Primitive.toBoolean, Bool.false_eq_true, if_false] using tagChain_refines stable ((secondTag, secondArm) :: rest)
                ((secondTag, emittedSecond) :: tailEmitted) alternate tagName sourceScope targetScope
                trace state restStep alternateBuilt aligned scrutineeRun

/--
A total case analysis over an enum with no payload anywhere becomes a chain of tag comparisons, in
declaration order, with the final arm unconditional.
-/
theorem matchOn : Op.Preserves .matchOn := by
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
    | boolean _ => exact refines_fault
    | absent => exact refines_fault
    | present _ => exact refines_fault
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
theorem member_reads_own_data_property {program : Ir.Program} {target : Target.Program} {fuel : Nat}
    {subject : Ir.Expr} {field : String} {emittedSubject : Target.Expr}
    (subjectStep : Everywhere program target runtime fuel subject emittedSubject)
    {sourceScope : List Source.Value} {targetScope : List Value} {trace : Source.Trace}
    {state : Target.State} (aligned : Aligned program sourceScope targetScope trace state)
    {value : Source.Value} {next : Source.Trace}
    (sourceRun : Source.eval program fuel sourceScope trace (.fieldGet subject field)
      = .value value next) :
    ∃ ref image final,
      Target.eval target runtime fuel targetScope state emittedSubject = .ok (.object ref) final ∧
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
      | absent => simp at sourceRun
      | present _ => simp at sourceRun
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
def Family.Preserves : Ir.Family → Prop
  | .enum => ∀ (program : Ir.Program) (name : String) (constructors : List Ir.Constructor),
      Compile.declaration program (.enum name constructors) = .ok none ∧
      ∀ (state : Target.State) (type constructorName : String) (arguments : List Source.Value)
        (image : Value),
        program.enum? type = some constructors →
        Relation.Represents program state (.variant type constructorName arguments) image →
        (Ir.allNullary constructors = true ∧ arguments = [] ∧
            image = .primitive (.string (JSString.ofLeanString constructorName))) ∨
          (Ir.allNullary constructors = false ∧ ∃ ref entries, image = .object ref ∧
            Relation.HasOwnFields state.heap ref
              (("kind", .primitive (.string (JSString.ofLeanString constructorName)))
                :: entries))
  | .record => ∀ (program : Ir.Program) (name : String) (fields : List Ir.Field),
      Compile.declaration program (.record name fields) = .ok none ∧
      ∀ (state : Target.State) (type : String) (values : List (String × Source.Value))
        (image : Value),
        Relation.Represents program state (.record type values) image →
        ∃ ref entries, image = .object ref ∧
          Relation.HasOwnFields state.heap ref entries ∧
          entries.map Prod.fst = values.map Prod.fst ∧
          state.heap.ownPropertyKeys ref = .ok ((values.map Prod.fst).map Ir.propertyKey)
  | .function => ∀ (program : Ir.Program) (target : Target.Program) (fuel : Nat) (name : String)
      (parameters : List Ir.Field) (result : Ir.Ty) (recursion : Option Nat) (body : Ir.Expr)
      (emittedBody : Target.Body) (emitted : Target.Function),
      Compile.body program body = .ok emittedBody →
      Compile.declaration program (.function name parameters result recursion body)
        = .ok (some emitted) →
      emitted.name = name ∧ emitted.parameters = parameters.length ∧
        emitted.body = emittedBody ∧
        ∀ (arguments : List Value) (state : Target.State) (declaration : Target.Function),
          target.find? name = some declaration →
          declaration.parameters = arguments.length →
          Target.enter target (fuel + 1) state name arguments
            = Target.evalBody target runtime fuel arguments.reverse
                (state.record (.function name arguments)) declaration.body

/-- An enum contributes no runtime declaration, and its values are the tag or the tagged object. -/
theorem familyEnum : Family.Preserves .enum := by
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
theorem familyRecord : Family.Preserves .record := by
  intro program name fields
  refine ⟨rfl, ?_⟩
  intro state type values image related
  unfold Relation.Represents at related
  obtain ⟨ref, entries, imageEq, fieldsRelated, shape⟩ := related
  refine ⟨ref, entries, imageEq, shape, representsFields_names values entries fieldsRelated, ?_⟩
  rw [shape.keys, ← representsFields_names values entries fieldsRelated, List.map_map]
  rfl

/-- A function contributes exactly one emitted function with its declared name and arity, and
entering it records one event, spends one unit of fuel, and binds its arguments in reverse. -/
theorem familyFunction : Family.Preserves .function := by
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
theorem registry : (op : Ir.Op) → Op.Preserves op
  | .varRef => varRef
  | .boolLit => boolLit
  | .letBind => letBind
  | .fieldGet => fieldGet
  | .ifThenElse => ifThenElse
  | .boolEquals => boolEquals
  | .boolAnd => boolAnd
  | .boolOr => boolOr
  | .boolNot => boolNot
  | .someValue => someValue
  | .noneValue => noneValue
  | .variant => variant
  | .record => record
  | .matchOn => matchOn
  | .call => call
  | .lambda => lambda
  | .apply => apply

/-- The closure over the declaration-family registry, total on `Ir.Family`. -/
theorem familyRegistry : (family : Ir.Family) → Family.Preserves family
  | .enum => familyEnum
  | .record => familyRecord
  | .function => familyFunction

end Preservation

end TSLean.LeanToTypeScript.Semantics
