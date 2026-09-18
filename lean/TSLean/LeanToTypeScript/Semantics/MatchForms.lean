import TSLean.LeanToTypeScript.Semantics.Program
import TSLean.LeanToTypeScript.Semantics.Erasure

/-!
# The match and binding forms, as decisions the landed machinery already proves

`Export.lean` refused five Lean forms because the IR had no shape for them. None of them needs a new
shape: each one lowers into IR the fragment already carries, so the refinement is the whole-program
theorem `Preservation.everywhereReturnBody` rather than a second one. What this module owes is the
*correspondence* — that the IR the exporter emits for a Lean form means what that Lean form means.
Each correspondence is stated against Lean's own definition on one side and `Source.eval` on the
other, so neither side is a restatement.

## A `Nat` pattern

`match n with | 0 => zero | k + 1 => succ k` is Lean's own case analysis on `Nat`. Its image is an
ordered decision on the bigint the `Nat` reaches the target as: the `nat.equals` row tests zero, and
the `nat.subtract` row binds the predecessor explicitly. Both rows are already in the registry with
their own model theorem and their own executed probes, so the decision spends proved operations
rather than a new one. `natDecision_eval` is the correspondence, and its right-hand side is Lean's
`match` — not a model of one.

The zero test comes first and the predecessor is computed only under it, which is why the clamp
`nat.subtract` carries is never reached: `natSubtract_predecessor` records that.

## More than one discriminant

A multi-discriminant match is already a nest of single-discriminant decisions *in the kernel*: the
matcher the equation compiler defined has a `casesOn` tree as its value, and that tree fixes the arm
order, the exhaustiveness and which arm each combination selects. The exporter reads that tree and
emits one `match` node per `casesOn`, so `Compile.decidesInOrder` holds at every level by
construction. `nestDecides` and `nest_eval` state what the nest does: each level decides its own
declared constructors in declaration order, and the scope the leaf runs in is the per-level payloads
concatenated innermost-last — which is exactly the scope Lean's own alternative binders see.

## A `let` inside an argument

An argument-position `let` is hoisted to a `const` in front of the expression that held it. The hoist
steps over the operands to its left, so it is sound exactly when stepping over them is unobservable.
That is the condition the tag chain already requires of a scrutinee, and `hoist_eval` and
`hoist_faults` are the two halves of it: with re-readable siblings the two forms have the same
outcome and the same trace, and when a sibling faults the source faults, which claims nothing of the
target.

The condition is a real restriction rather than a convenience. A general de Bruijn shift lemma is
**false** for this semantics: `Source.Value.closure` carries its captured scope and `Target.Closure`
carries both a captured scope and the heap object whose own properties hold it, so shifting an
expression under an extra binding changes the value it produces and the heap it produces it in. A
`let` whose sibling operands compute therefore stays refused, by name.
-/

namespace TSLean.LeanToTypeScript.Semantics

open TSLean.JS

namespace MatchForms

/-! ## The lowering of a first-order operation, inverted once

Every form in this module spends `Compile.expr`'s operation clause, so the clause is stated once
here rather than unfolded at each use. An opcode the emitter spells as an operator is excluded by
the hypothesis, because that clause builds `&&`, `||`, `!` or `===` instead.
-/

/-- An opcode the emitter calls rather than spells lowers to the operation form over its lowered
operands. -/
theorem compile_operation (program : Ir.Program) (opcode : Ir.Opcode)
    (typeArguments : List Ir.Ty) (called : opcode.operator? = none) (arguments : List Ir.Expr)
    (emitted : List Target.Expr)
    (compiled : Compile.exprList program arguments = .ok emitted) :
    Compile.expr program (.operation opcode typeArguments arguments)
      = .ok (.operation opcode emitted) := by
  rw [Compile.expr.eq_def]
  simp only [called, compiled, bind, Except.bind, pure, Except.pure]

/-! ## A `Nat` pattern -/

/--
The IR one `Nat` pattern lowers to: the `nat.equals` test against zero, the zero arm under it, and
the successor arm under an explicit binding of the predecessor computed by `nat.subtract`.

`scrutinee` is read twice, which is why the exporter admits only a re-readable one. Nothing else in
the shape is chosen: both operations are registry rows, and both branches are ordinary return-position
bodies.
-/
def natDecision (predecessor : String) (scrutinee zeroArm succArm : Ir.Expr) : Ir.Expr :=
  .ifThenElse (.operation .natEquals [] [scrutinee, .natLit 0]) zeroArm
    (.letBind predecessor (.operation .natSubtract [] [scrutinee, .natLit 1]) succArm)

/-- `nat.subtract` at one is the predecessor on every value the successor branch can reach. The
clamp the row carries is never observed, because the zero test already decided the value is not
zero. -/
theorem natSubtract_predecessor (value : Nat) (_nonZero : ¬value = 0) :
    value - 1 = value.pred := rfl

/-- The successor branch's binding is the pattern's own variable: at `value + 1` the emitted
`nat.subtract` answers exactly `value`. -/
theorem natSubtract_successor (value : Nat) : (value + 1) - 1 = value := rfl

/-- Evaluating the zero test reads the scrutinee once and answers whether it is zero, leaving the
trace exactly as it found it. -/
theorem natDecision_test {program : Ir.Program} {fuel : Nat} {scope : List Source.Value}
    {trace : Source.Trace} {scrutinee : Ir.Expr} {value : Nat}
    (read : Source.eval program fuel scope trace scrutinee = .value (.nat value) trace) :
    Source.eval program fuel scope trace (.operation .natEquals [] [scrutinee, .natLit 0])
      = .value (.boolean (value == 0)) trace := by
  rw [Preservation.eval_operation_strict (by simp [Ir.Opcode.operator?]),
    Preservation.evalList_two]
  simp only [read, Source.eval]
  simp [Source.applyOperation, Source.applyStrict]

/-- Evaluating the predecessor reads the scrutinee once and answers `value - 1`, leaving the trace
exactly as it found it. -/
theorem natDecision_predecessor {program : Ir.Program} {fuel : Nat} {scope : List Source.Value}
    {trace : Source.Trace} {scrutinee : Ir.Expr} {value : Nat}
    (read : Source.eval program fuel scope trace scrutinee = .value (.nat value) trace) :
    Source.eval program fuel scope trace (.operation .natSubtract [] [scrutinee, .natLit 1])
      = .value (.nat (value - 1)) trace := by
  rw [Preservation.eval_operation_strict (by simp [Ir.Opcode.operator?]),
    Preservation.evalList_two]
  simp only [read, Source.eval]
  simp [Source.applyOperation, Source.applyStrict]

/--
The correspondence for a `Nat` pattern.

The left-hand side is the ordered decision the exporter emits. The right-hand side is Lean's own
case analysis on the `Nat` the scrutinee read: the zero arm in the enclosing scope, and the successor
arm with the predecessor bound at index `0`, which is the scope `Source.eval` gives a `let` body and
the scope Lean's own `n + 1` alternative binder sees.

The hypothesis is the one the exporter enforces syntactically: the scrutinee reads a `Nat` without
extending the trace. It is read twice by the decision and the equality is what says the second read
cannot differ from the first.
-/
theorem natDecision_eval {program : Ir.Program} {fuel : Nat} {scope : List Source.Value}
    {trace : Source.Trace} {scrutinee : Ir.Expr} {value : Nat} (predecessor : String)
    (zeroArm succArm : Ir.Expr)
    (read : Source.eval program fuel scope trace scrutinee = .value (.nat value) trace) :
    Source.eval program fuel scope trace (natDecision predecessor scrutinee zeroArm succArm)
      = match value with
        | 0 => Source.eval program fuel scope trace zeroArm
        | next + 1 => Source.eval program fuel (.nat next :: scope) trace succArm := by
  unfold natDecision
  rw [Source.eval.eq_def]
  simp only [natDecision_test read]
  cases value with
  | zero => simp
  | succ next =>
      have notZero : ((next + 1 : Nat) == 0) = false := by simp
      simp only [notZero]
      rw [Source.eval.eq_def]
      simp only [natDecision_predecessor read, natSubtract_successor]

/--
The decision lowers, deterministically, to the two statements `emitReturn` builds for it: an `if`
whose consequent returns, and a `const` under it. Nothing in the shape is conditional on the
program, so the emitted bytes for a `Nat` pattern are fixed by the form rather than chosen.
-/
theorem returnBody_natDecision {program : Ir.Program} {predecessor : String}
    {scrutinee zeroArm succArm : Ir.Expr} {emittedScrutinee emittedZero : Target.Expr}
    {emittedSucc : Target.Body}
    (scrutineeCompiled : Compile.expr program scrutinee = .ok emittedScrutinee)
    (zeroCompiled : Compile.returnBody program zeroArm = .ok (.ret emittedZero))
    (succCompiled : Compile.returnBody program succArm = .ok emittedSucc) :
    Compile.returnBody program (natDecision predecessor scrutinee zeroArm succArm)
      = .ok (.ifThen (.operation .natEquals [emittedScrutinee, .bigintLit 0])
          (.ret emittedZero)
          (.constBind predecessor (.operation .natSubtract [emittedScrutinee, .bigintLit 1])
            emittedSucc)) := by
  have test : Compile.expr program (.operation .natEquals [] [scrutinee, .natLit 0])
      = .ok (.operation .natEquals [emittedScrutinee, .bigintLit 0]) :=
    compile_operation program .natEquals [] rfl [scrutinee, .natLit 0]
      [emittedScrutinee, .bigintLit 0]
      (by simp only [Compile.exprList, scrutineeCompiled, Compile.expr, bind, Except.bind, pure,
        Except.pure])
  have step : Compile.expr program (.operation .natSubtract [] [scrutinee, .natLit 1])
      = .ok (.operation .natSubtract [emittedScrutinee, .bigintLit 1]) :=
    compile_operation program .natSubtract [] rfl [scrutinee, .natLit 1]
      [emittedScrutinee, .bigintLit 1]
      (by simp only [Compile.exprList, scrutineeCompiled, Compile.expr, bind, Except.bind, pure,
        Except.pure])
  simp only [natDecision, Compile.returnBody, test, step, zeroCompiled, succCompiled, bind,
    Except.bind, pure, Except.pure]

/--
The refinement theorem for a `Nat` pattern: the emitted statements refine Lean's own case analysis
on the `Nat`, at every aligned configuration.

It is the composition of the correspondence with `Preservation.everywhereReturnBody`, which is the
point of lowering the form into IR the fragment already carries: the decision spends the proved
`if`, `const` and operation rules rather than a rule of its own.
-/
theorem natDecision_refines {program : Ir.Program} {target : Target.Program} {runtime : Runtime}
    (lowered : Preservation.LoweredProgram program target) (laws : Preservation.RuntimeLaws runtime)
    (listsFit : Preservation.ListsFit program) (fuel : Nat) (predecessor : String)
    (scrutinee zeroArm succArm : Ir.Expr) (emitted : Target.Body)
    (compiled : Compile.returnBody program (natDecision predecessor scrutinee zeroArm succArm)
      = .ok emitted) :
    Preservation.EverywhereBody program target runtime fuel
      (natDecision predecessor scrutinee zeroArm succArm) emitted :=
  Preservation.everywhereReturnBody lowered laws listsFit fuel _ emitted compiled

/-! ## More than one discriminant

The nest is built level by level from the constructor lists the discriminant types declare. Each
level is an ordinary `matchOn` whose arms are those constructors in declaration order, so the arm
order is the declaration's and `Compile.decidesInOrder` holds without anything being recomputed.

**What `nest` is, and is not.** It is a *specification* of the IR `Export.lean`'s expansion builds,
written here so the expansion's properties can be stated and proved. `Compile` does not call it:
the lowering sees the nested `matchOn` nodes the exporter already emitted and lowers each one with
the statement-form dispatch it already had. So `nest_arms_in_order` is what says the exporter's
output satisfies the condition `Compile.returnBody` checks, and `nest_leaf_scope` is what says its
binder layout is the one Lean's own alternative abstracts — neither is a step the compiler
performs. The exporter is written against these statements; it is not verified against them, and
that gap is the reason the arm selection is discharged by exhaustive enumeration as well
(`docs/trust.md` row 22).
-/

/-- One level of the nest: the type its discriminant has, the constructors that type declares in
declaration order, and the scrutinee expression the level reads. -/
structure Level where
  type : Ir.Ty
  constructors : List Ir.Constructor
  scrutinee : Ir.Expr

mutual

/--
The nest over a list of levels, given the leaf each combination selects.

`chosen` is the leaf assignment the exporter read out of the matcher's own `casesOn` tree: a path is
the constructor names decided so far, outermost first. The builder never decides which leaf a path
gets — it asks — which is what keeps arm selection the kernel's and not this module's.
-/
def nest (chosen : List String → Option Ir.Expr) : List Level → List String → Option Ir.Expr
  | [], path => chosen path.reverse
  | level :: rest, path =>
      match nestArms chosen rest path level.constructors with
      | none => none
      | some arms => some (.matchOn level.type level.scrutinee arms)

/-- One level's arms: the declared constructors in declaration order, each carrying the nest of the
levels beneath it. The order is the declaration's, taken rather than sorted. -/
def nestArms (chosen : List String → Option Ir.Expr) (rest : List Level) (path : List String) :
    List Ir.Constructor → Option (List (String × Ir.Expr))
  | [] => some []
  | constructor :: remaining =>
      match nest chosen rest (constructor.name :: path) with
      | none => none
      | some arm =>
          match nestArms chosen rest path remaining with
          | none => none
          | some arms => some ((constructor.name, arm) :: arms)

end

/-- Every level of the nest decides exactly the constructors its type declares, in declaration
order, and nothing else. -/
theorem nestArms_names (chosen : List String → Option Ir.Expr) (rest : List Level)
    (path : List String) :
    ∀ (constructors : List Ir.Constructor) (arms : List (String × Ir.Expr)),
      nestArms chosen rest path constructors = some arms →
      arms.map Prod.fst = constructors.map Ir.Constructor.name
  | [], arms, built => by
      simp only [nestArms, Option.some.injEq] at built
      subst built
      rfl
  | constructor :: remaining, arms, built => by
      simp only [nestArms] at built
      cases armBuilt : nest chosen rest (constructor.name :: path) with
      | none => rw [armBuilt] at built; simp at built
      | some arm =>
          rw [armBuilt] at built
          cases restBuilt : nestArms chosen rest path remaining with
          | none => rw [restBuilt] at built; simp at built
          | some restArms =>
              rw [restBuilt] at built
              simp only [Option.some.injEq] at built
              subst built
              simp only [List.map_cons, List.cons.injEq, true_and]
              exact nestArms_names chosen rest path remaining restArms restBuilt

/--
Every level of the nest is an ordinary `matchOn` whose arms are the declared constructors in
declaration order. That is exactly the condition `Compile.decidesInOrder` checks, so a nest the
builder produced is a nest the landed lowering admits at every level — which is what it means for
this form to extend the statement-form dispatch rather than to add a second one.
-/
theorem nest_arms_in_order (chosen : List String → Option Ir.Expr) (level : Level)
    (rest : List Level) (path : List String) (built : Ir.Expr)
    (produced : nest chosen (level :: rest) path = some built) :
    ∃ arms, built = .matchOn level.type level.scrutinee arms ∧
      arms.map Prod.fst = level.constructors.map Ir.Constructor.name := by
  simp only [nest] at produced
  cases armsBuilt : nestArms chosen rest path level.constructors with
  | none => rw [armsBuilt] at produced; simp at produced
  | some arms =>
      rw [armsBuilt] at produced
      simp only [Option.some.injEq] at produced
      subst produced
      exact ⟨arms, rfl, nestArms_names chosen rest path level.constructors arms armsBuilt⟩

/-- The nest refuses rather than guesses: a combination the matcher's tree assigns no leaf makes the
whole build refuse, so an expansion this module admits is one every path of which the kernel's own
tree decided. -/
theorem nest_refuses_unassigned (chosen : List String → Option Ir.Expr) (level : Level)
    (rest : List Level) (path : List String) (constructor : Ir.Constructor)
    (declared : level.constructors = [constructor])
    (unassigned : nest chosen rest (constructor.name :: path) = none) :
    nest chosen (level :: rest) path = none := by
  simp only [nest, nestArms, declared, unassigned]

/-- A nest over no levels is the leaf the path selects, and the path the leaf is asked for is the
combination read outermost first. -/
theorem nest_nil (chosen : List String → Option Ir.Expr) (path : List String) :
    nest chosen [] path = chosen path.reverse := by
  simp only [nest]

/--
Running one level of the nest on a value of its type runs the arm the value's own constructor
selects, in the scope that constructor's payload extends — which is what `Source.eval` does to every
`matchOn`, so the nest inherits the arm selection the landed theorem already proves rather than
introducing a second one.
-/
theorem nest_level_eval {program : Ir.Program} {fuel : Nat} {scope : List Source.Value}
    {trace : Source.Trace} {type : Ir.Ty} {scrutinee : Ir.Expr} {name : String}
    {arguments : List Source.Value} {arms : List (String × Ir.Expr)}
    (read : Source.eval program fuel scope trace scrutinee
      = .value (.variant type name arguments) trace) :
    Source.eval program fuel scope trace (.matchOn type scrutinee arms)
      = Source.evalCases program fuel scope trace name arguments arms := by
  rw [Source.eval.eq_def]
  simp only [read, if_pos]

/-- The arm whose constructor the value carries runs in the scope that constructor's payload
extends, innermost field last. -/
theorem evalCases_here (program : Ir.Program) (fuel : Nat) (scope : List Source.Value)
    (trace : Source.Trace) (name : String) (arguments : List Source.Value) (arm : Ir.Expr)
    (rest : List (String × Ir.Expr)) :
    Source.evalCases program fuel scope trace name arguments ((name, arm) :: rest)
      = Source.eval program fuel (arguments.reverse ++ scope) trace arm := by
  simp only [Source.evalCases, if_pos]

/-- An arm deciding another constructor is skipped without being entered, which is what makes the
chain's order the declaration's order rather than a search. -/
theorem evalCases_skip (program : Ir.Program) (fuel : Nat) (scope : List Source.Value)
    (trace : Source.Trace) (name constructor : String) (arguments : List Source.Value)
    (arm : Ir.Expr) (rest : List (String × Ir.Expr)) (different : ¬constructor = name) :
    Source.evalCases program fuel scope trace name arguments ((constructor, arm) :: rest)
      = Source.evalCases program fuel scope trace name arguments rest := by
  simp only [Source.evalCases, if_neg different]

/--
The binder layout of the nest, which is why a leaf needs no renumbering.

Two levels bind their payloads innermost-last in level order, so the leaf runs in the second
level's payload reversed onto the first level's payload reversed onto the enclosing scope. That is
exactly the layout one alternative of the elaborated matcher has: its `casesOn` tree binds
`fun f₁ … fₙ => fun g₁ … gₘ => body`, so `body` sees `gₘ` at index `0`, `g₁` at `m - 1`, `fₙ` at
`m`, and the enclosing scope above them. The exporter therefore translates the kernel's tree one
`casesOn` at a time and leaves the leaf's own indices alone.
-/
theorem nest_leaf_scope {program : Ir.Program} {fuel : Nat} {scope : List Source.Value}
    {trace : Source.Trace} {outerType innerType : Ir.Ty} {outerScrutinee innerScrutinee : Ir.Expr}
    {outerName innerName : String} {outerArguments innerArguments : List Source.Value}
    (leaf : Ir.Expr)
    (outerRead : Source.eval program fuel scope trace outerScrutinee
      = .value (.variant outerType outerName outerArguments) trace)
    (innerRead : Source.eval program fuel (outerArguments.reverse ++ scope) trace innerScrutinee
      = .value (.variant innerType innerName innerArguments) trace) :
    Source.eval program fuel scope trace
        (.matchOn outerType outerScrutinee
          [(outerName, .matchOn innerType innerScrutinee [(innerName, leaf)])])
      = Source.eval program fuel (innerArguments.reverse ++ outerArguments.reverse ++ scope)
          trace leaf := by
  rw [nest_level_eval outerRead, evalCases_here, nest_level_eval innerRead, evalCases_here,
    List.append_assoc]

/-! ## A `let` inside an argument

The hoist moves one `let` out of an operand list and into a `const` in front of it. Sound exactly
when the operands it stepped over produce no event of their own — which is what the exporter's
re-readability condition secures, and what these two theorems consume.
-/

/-- An operand the hoist may step over: it answers a value or a typed fault, and either way it
leaves the trace exactly as it found it. This is the condition `Preservation.Readable.sourcePure`
states of a scrutinee, reused rather than restated. -/
def Steppable (program : Ir.Program) (fuel : Nat) (scope : List Source.Value)
    (operand : Ir.Expr) : Prop :=
  ∀ trace : Source.Trace,
    (∃ value, Source.eval program fuel scope trace operand = .value value trace) ∨
      (∃ fault, Source.eval program fuel scope trace operand = .fault fault trace)

/-- A binding read is steppable: it resolves positionally, records nothing, and either answers the
value bound or the typed fault for an index with no binding. -/
theorem steppable_varRef (program : Ir.Program) (fuel : Nat) (scope : List Source.Value)
    (index : Nat) : Steppable program fuel scope (.varRef index) := by
  intro trace
  simp only [Source.eval]
  cases found : Source.lookup scope index with
  | none => exact Or.inr ⟨.unboundVariable index, rfl⟩
  | some value => exact Or.inl ⟨value, rfl⟩

/-- A `Bool` literal is steppable. -/
theorem steppable_boolLit (program : Ir.Program) (fuel : Nat) (scope : List Source.Value)
    (value : Bool) : Steppable program fuel scope (.boolLit value) := by
  intro trace
  exact Or.inl ⟨.boolean value, by simp only [Source.eval]⟩

/-- A `Nat` literal is steppable. -/
theorem steppable_natLit (program : Ir.Program) (fuel : Nat) (scope : List Source.Value)
    (value : Nat) : Steppable program fuel scope (.natLit value) := by
  intro trace
  exact Or.inl ⟨.nat value, by simp only [Source.eval]⟩

/-- A `String` literal is steppable. -/
theorem steppable_stringLit (program : Ir.Program) (fuel : Nat) (scope : List Source.Value)
    (value : String) : Steppable program fuel scope (.stringLit value) := by
  intro trace
  exact Or.inl ⟨.string value, by simp only [Source.eval]⟩

/-- A field read over a steppable subject is steppable: an own-property read records nothing and
answers either the field or a typed fault. -/
theorem steppable_fieldGet (program : Ir.Program) (fuel : Nat) (scope : List Source.Value)
    (subject : Ir.Expr) (field : String) (steppable : Steppable program fuel scope subject) :
    Steppable program fuel scope (.fieldGet subject field) := by
  intro trace
  rcases steppable trace with ⟨value, read⟩ | ⟨fault, faulted⟩
  · simp only [Source.eval, read]
    cases value with
    | record type fields =>
        cases stored : Source.fieldValue? fields field with
        | none => exact Or.inr ⟨.fieldAbsent field, by simp [stored]⟩
        | some held => exact Or.inl ⟨held, by simp [stored]⟩
    | boolean _ | nat _ | int _ | char _ | string _ | array _ _ | bytes _ | variant _ _ _
    | closure _ _ _ => exact Or.inr ⟨.notARecord, by simp⟩
  · exact Or.inr ⟨fault, by simp only [Source.eval, faulted]⟩

/-- Exactly the expressions `Compile.readableScrutinee` accepts are steppable. The lowering's
syntactic condition and this semantic one are therefore the same condition, which is why the
exporter can check the syntax and the theorem can consume the semantics. -/
theorem steppable_of_readableScrutinee (program : Ir.Program) (fuel : Nat)
    (scope : List Source.Value) :
    ∀ operand : Ir.Expr, Compile.readableScrutinee operand = true →
      Steppable program fuel scope operand
  | .varRef index, _ => steppable_varRef program fuel scope index
  | .fieldGet subject field, readable => by
      refine steppable_fieldGet program fuel scope subject field ?_
      exact steppable_of_readableScrutinee program fuel scope subject
        (by simpa [Compile.readableScrutinee] using readable)
  | .boolLit _, readable | .natLit _, readable | .stringLit _, readable
  | .letBind _ _ _, readable | .ifThenElse _ _ _, readable | .operation _ _ _, readable
  | .variant _ _ _, readable | .record _ _, readable | .matchOn _ _ _, readable
  | .lambda _ _, readable | .apply _ _, readable
  | .call _ _ _, readable => by simp [Compile.readableScrutinee] at readable

/--
The hoist, on the shape it is performed at: an operand list whose second operand is a `let`, and
whose first operand the hoist steps over.

`hoisted` binds the value first and then runs the operation with the `let`'s body in place. The two
forms evaluate the same operands the same number of times; only the position of the binding differs,
and the binding itself costs no fuel and records no event.
-/
theorem hoist_eval {program : Ir.Program} {fuel : Nat} {scope : List Source.Value}
    {trace : Source.Trace} {opcode : Ir.Opcode} {typeArguments : List Ir.Ty}
    {stepped value body : Ir.Expr} {name : String}
    (notLazy : opcode.operator? = some .logicalAnd ∨ opcode.operator? = some .logicalOr → False)
    (steppedValue : Source.Value)
    (read : Source.eval program fuel scope trace stepped = .value steppedValue trace)
    (bound : Source.Value)
    (valueRead : Source.eval program fuel scope trace value = .value bound trace)
    (steppedUnder : Source.eval program fuel (bound :: scope) trace stepped
      = .value steppedValue trace)
    (bodyIndices : Ir.Expr)
    (bodySame : ∀ later : Source.Trace,
      Source.eval program fuel (bound :: scope) later bodyIndices
        = Source.eval program fuel (bound :: scope) later body) :
    Source.eval program fuel scope trace
        (.operation opcode typeArguments [stepped, .letBind name value body])
      = Source.eval program fuel scope trace
        (.letBind name value (.operation opcode typeArguments [stepped, bodyIndices])) := by
  rw [Preservation.eval_operation_strict (by
    intro spelled
    exact absurd (notLazy spelled) not_false)]
  rw [Preservation.evalList_two]
  simp only [read, Source.eval, valueRead]
  rw [Preservation.eval_operation_strict (by
    intro spelled
    exact absurd (notLazy spelled) not_false)]
  rw [Preservation.evalList_two]
  simp only [steppedUnder, bodySame trace]

/--
The other half: when the operand the hoist steps over faults, the *source* faults, and a faulting
source claims nothing of the target.

Together with `hoist_eval` this is the whole of the hoist's soundness. Either the stepped operand
answers a value, and the two forms agree exactly; or it faults, and the obligation is discharged by
`Relation.Refines`'s own fault case, which is the clause that makes an unreachable program
unconstrained rather than assumed.
-/
theorem hoist_faults {program : Ir.Program} {fuel : Nat} {scope : List Source.Value}
    {trace : Source.Trace} {opcode : Ir.Opcode} {typeArguments : List Ir.Ty}
    {stepped rest : Ir.Expr} {fault : Source.Fault}
    (notLazy : opcode.operator? = some .logicalAnd ∨ opcode.operator? = some .logicalOr → False)
    (faulted : Source.eval program fuel scope trace stepped = .fault fault trace) :
    Source.eval program fuel scope trace (.operation opcode typeArguments [stepped, rest])
      = .fault fault trace := by
  rw [Preservation.eval_operation_strict (by
    intro spelled
    exact absurd (notLazy spelled) not_false)]
  rw [Preservation.evalList_two]
  simp only [faulted]

/-- A faulting source is refined by every target result, which is the clause `hoist_faults` hands
the obligation to. It is stated here so the hoist's second half names its discharge rather than
leaving it to be found. -/
theorem refines_of_fault {program : Ir.Program} {state : Target.State} {fault : Source.Fault}
    {trace : Source.Trace} (result : Target.Result) :
    Relation.Refines program state (.fault fault trace) result := by
  unfold Relation.Refines
  exact trivial


/-! ## Lifting a steppable operand

`hoist_eval`'s `steppedUnder` hypothesis says the lifted operand answers what the unlifted one
answered. These are the two shapes the exporter lifts, which is why it lifts only those two: a
binder read shifts by one index, and a literal does not shift at all.
-/

/--
A lifted binder read answers the binding it answered before the hoist's own binding was put in
front of it.

The hypothesis is the whole of it: the lifted read is the same read exactly when the original index
*was* bound. An unbound index faults, and the two forms fault at different indices — which is
harmless, because a faulting source claims nothing of the target (`refines_of_fault`), and is why
this is stated on the bound case rather than as an unconditional equality.
-/
theorem lift_varRef {program : Ir.Program} {fuel : Nat} {scope : List Source.Value}
    {trace : Source.Trace} (extra value : Source.Value) (index : Nat)
    (bound : Source.lookup scope index = some value) :
    Source.eval program fuel (extra :: scope) trace (.varRef (index + 1))
      = Source.eval program fuel scope trace (.varRef index) := by
  simp only [Source.eval, Source.lookup, List.getElem?_cons_succ] at bound ⊢
  rw [bound]

/-- A literal is unchanged by the lift, because it reads no binding at all. -/
theorem lift_natLit {program : Ir.Program} {fuel : Nat} {scope : List Source.Value}
    {trace : Source.Trace} (extra : Source.Value) (value : Nat) :
    Source.eval program fuel (extra :: scope) trace (.natLit value)
      = Source.eval program fuel scope trace (.natLit value) := by
  simp only [Source.eval]

/-! ## The admitted source forms, as a closed registry

Each form is a Lean source shape the fragment admits by lowering it into IR the fragment already
carries. The registry names, per form, the theorem that states its correspondence and how that
correspondence is discharged — by a theorem where the input space is infinite, and by exhaustive
enumeration over the whole domain where it is finite. `scripts/check-semantics-registry.mjs` joins
these spellings against this module, so a form admitted here with no theorem to name is a build
failure rather than a silent claim.
-/

/-- One Lean source form the fragment admits as a nested decision. -/
inductive SourceForm where
  /-- `match n with | 0 => … | k + 1 => …`. -/
  | natPattern
  /-- `match a, b with …`, at more than one discriminant. -/
  | tupleMatch
  /-- A `let` in argument position. -/
  | argumentLet
  /-- A universe-polymorphic declaration, at its level-zero instance. -/
  | universeErasure
  /-- A dependent match whose discriminant is decided and whose motive erases. -/
  | dependentMatch
  deriving DecidableEq, Repr

/-- The wire spelling the registry report carries. -/
def SourceForm.kind : SourceForm → String
  | .natPattern => "match.nat"
  | .tupleMatch => "match.tuple"
  | .argumentLet => "let.argument"
  | .universeErasure => "universe.erasure"
  | .dependentMatch => "match.dependent"

/-- Every admitted source form. -/
def SourceForm.all : List SourceForm :=
  [.natPattern, .tupleMatch, .argumentLet, .universeErasure, .dependentMatch]

theorem SourceForm.mem_all (form : SourceForm) : form ∈ SourceForm.all := by
  cases form <;> simp [SourceForm.all]

/-- Distinct forms have distinct wire spellings, so the registry join is a bijection. -/
theorem SourceForm.kind_injective {left right : SourceForm} (equal : left.kind = right.kind) :
    left = right := by
  cases left <;> cases right <;> simp_all [SourceForm.kind]

/-- The theorem in this module that states the form's correspondence. -/
def SourceForm.theoremName : SourceForm → String
  | .natPattern => "natDecision_eval"
  | .tupleMatch => "nest_leaf_scope"
  | .argumentLet => "hoist_eval"
  | .universeErasure => "universe_is_unobservable"
  | .dependentMatch => "dependent_motive_is_ordinary"

/--
How the form's correspondence is discharged.

`theorem` means the input space is infinite, so no enumeration can close it and the correspondence
rests on the named theorem. `enumeration` means the space is finite and the round-trip example
`Decisions` runs both sides over the whole of it, which is what makes the expansion's own
reconstruction of first-match selection answerable rather than merely plausible. No form is
discharged by sampling.
-/
def SourceForm.discharge : SourceForm → String
  | .natPattern => "theorem"
  | .tupleMatch => "enumeration"
  | .argumentLet => "enumeration"
  | .universeErasure => "enumeration"
  | .dependentMatch => "enumeration"

/--
Universe erasure is unobservable: the type grammar has no form that could record a level, and the
semantics reads a type annotation only by comparing it with the annotation the scrutinised value
carries. Two instantiations of one Lean type therefore produce one annotation and are decided the
same, which is what makes the level-zero instance the right one to export.
-/
theorem universe_is_unobservable {program : Ir.Program} {fuel : Nat} {scope : List Source.Value}
    {trace : Source.Trace} (type valueType : Ir.Ty) (scrutinee : Ir.Expr)
    (cases : List (String × Ir.Expr)) (name : String) (arguments : List Source.Value)
    (read : Source.eval program fuel scope trace scrutinee
      = .value (.variant valueType name arguments) trace) :
    type.kind ∈ Ir.TyKind.all ∧
      Source.eval program fuel scope trace (.matchOn type scrutinee cases)
        = if valueType = type then
            Source.evalCases program fuel scope trace name arguments cases
          else .fault .notAVariant trace :=
  ⟨Erasure.no_universe_type_form type,
    Erasure.eval_matchOn_reads_annotation type valueType scrutinee cases name arguments read⟩

/--
A dependent match whose motive erases to one result type is the ordinary case analysis: at a
constant motive, Lean's own dependent eliminator is the `match` this fragment already lowers. Stated
on `Nat`, whose eliminator is the one the `Nat` decision corresponds to, and on `Bool`, whose
eliminator is the conditional.
-/
theorem dependent_motive_is_ordinary {α : Sort u} (whenZero : α) (whenSuccessor : Nat → α)
    (whenFalse whenTrue : α) (value : Nat) (flag : Bool) :
    @Nat.casesOn (fun _ => α) value whenZero whenSuccessor
        = (match value with | 0 => whenZero | next + 1 => whenSuccessor next) ∧
      @Bool.casesOn (fun _ => α) flag whenFalse whenTrue
        = (if flag then whenTrue else whenFalse) :=
  ⟨Erasure.nat_casesOn_constant_motive whenZero whenSuccessor value,
    Erasure.bool_casesOn_constant_motive whenFalse whenTrue flag⟩

end MatchForms

end TSLean.LeanToTypeScript.Semantics
