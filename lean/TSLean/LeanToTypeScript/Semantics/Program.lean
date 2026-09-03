import TSLean.LeanToTypeScript.Semantics.Preservation

/-!
# Whole-program preservation

`everywhere` closes the per-operation theorems into one statement over whole programs: every
expression the lowering admits refines its source, from every aligned configuration, at every fuel.
It discharges every hypothesis the per-operation theorems take — the subexpression obligations, the
readable-scrutinee obligation, the key and field refusals, the opcode laws and the callee obligation
at lower fuel — from three premises: the program's lowering, the engine's recorded assumption
closures, and ECMAScript's array-length cap.
-/

namespace TSLean.LeanToTypeScript.Semantics

open TSLean.JS

namespace Preservation

/--
The target is the lowering of the program: every declared function has a lowered counterpart
declaring the same number of parameters, whose body is the lowered body. Inline arrows are not
program declarations; their exact body lowering is carried by the closure representation itself.
-/
structure LoweredProgram (program : Ir.Program) (target : Target.Program) : Prop where
  functions : ∀ (name : String) (parameters : List Ir.Field) (result : Ir.Ty)
    (recursion : Ir.Recursion) (body : Ir.Expr),
    program.function? name = some (parameters, result, recursion, body) →
    ∃ emitted, target.find? name = some emitted ∧ emitted.parameters = parameters.length ∧
      Compile.returnBody program body = .ok emitted.body

/--
The one premise a host boundary adds to the trusted computing base.

Inside this model a `foreign` declaration lowers to a function carrying its exported reference body,
so `loweredProgram_of_compile` discharges `LoweredProgram` for it exactly as it does for a
`function`. In deployment that binding is *replaced*: the emitted module imports the substrate's
implementation under the host name instead of declaring the reference. `HostSubstrate` is that
replacement's requirement, stated on the same equation `LoweredProgram` uses — the target module's
binding at the host name has the boundary's arity and the lowering of the reference body as its
body.

Nothing here proves it, and no axiom asserts it. It is discharged one row per host operation by the
substrate's own laws (`AgentCore.Substrate.<Seam>Laws`) and the conformance gate that binds those
laws to the adapter, which is why the compiler's audit stays at the three standard axioms while the
host boundary remains an explicit, countable premise.
-/
def HostSubstrate (program : Ir.Program) (target : Target.Program) : Prop :=
  ∀ (name : String) (parameters : List Ir.Field) (result : Ir.Ty) (reference : Ir.Expr),
    (∃ host, program.find? name = some (.foreign name host parameters result reference)) →
    ∃ emitted, target.find? name = some emitted ∧ emitted.parameters = parameters.length ∧
      Compile.returnBody program reference = .ok emitted.body

/--
Every admitted opcode's recorded assumption closure holds of the engine.

`Opcode.registry` turns one of these into that opcode's law, so the `operation` row consumes a proved
statement rather than an assumption, and an opcode whose closure was widened or narrowed would not
typecheck there.
-/
def RuntimeLaws (runtime : Runtime) : Prop :=
  ∀ code : Ir.Opcode, Assumption.Holds runtime code.requires

/-- A lowered program has a lowered counterpart for every declared function. -/
theorem lowered_of_loweredProgram {program : Ir.Program} {target : Target.Program}
    (lowered : LoweredProgram program target) : Lowered program target := by
  intro name parameters result recursion body declared
  obtain ⟨emitted, found, arity, _⟩ :=
    lowered.functions name parameters result recursion body declared
  exact ⟨emitted, found, arity⟩

/--
A lowered program satisfies the host premise. This is what makes `HostSubstrate` a *replacement*
requirement rather than a second idea of what a host boundary owes: the model's own lowering already
meets it, so the premise says exactly that the substrate's binding meets what the reference binding
met, and nothing more.
-/
theorem hostSubstrate_of_loweredProgram {program : Ir.Program} {target : Target.Program}
    (lowered : LoweredProgram program target) : HostSubstrate program target := by
  intro name parameters result reference boundary
  obtain ⟨host, found⟩ := boundary
  exact lowered.functions name parameters result .nonrecursive reference
    (by simp only [Ir.Program.function?, found])

/-- An option is absent or holds a value, without generalising the goal. -/
theorem option_cases {α : Type} (value : Option α) :
    value = none ∨ ∃ held, value = some held := by
  cases value with
  | none => exact Or.inl rfl
  | some held => exact Or.inr ⟨held, rfl⟩

/-- Peels one `Except` bind, which is the shape every `Compile` clause has. -/
theorem bind_ok {α β : Type} {value : Except Compile.Fault α}
    {next : α → Except Compile.Fault β} {result : β} (run : value >>= next = .ok result) :
    ∃ produced, value = .ok produced ∧ next produced = .ok result := by
  cases value with
  | error fault => simp [Bind.bind, Except.bind] at run
  | ok produced => exact ⟨produced, rfl, run⟩

/-- Reading a readable scrutinee produces no event on the source side. -/
theorem sourcePure_of_readable {program : Ir.Program} {fuel : Nat} :
    ∀ (scrutinee : Ir.Expr), Compile.readableScrutinee scrutinee = true →
      ∀ (sourceScope : List Source.Value) (trace : Source.Trace),
        (∃ value, Source.eval program fuel sourceScope trace scrutinee = .value value trace) ∨
          (∃ fault, Source.eval program fuel sourceScope trace scrutinee = .fault fault trace)
  | .varRef index, _, sourceScope, trace => by
      simp only [Source.eval]
      cases lookup : Source.lookup sourceScope index with
      | none => exact Or.inr ⟨_, rfl⟩
      | some value => exact Or.inl ⟨value, rfl⟩
  | .fieldGet subject field, readable, sourceScope, trace => by
      simp only [Compile.readableScrutinee] at readable
      simp only [Source.eval]
      rcases sourcePure_of_readable subject readable sourceScope trace with
        ⟨value, run⟩ | ⟨fault, run⟩
      · rw [run]
        cases value with
        | record type fields =>
            dsimp only
            cases lookup : Source.fieldValue? fields field with
            | none => exact Or.inr ⟨_, rfl⟩
            | some found => exact Or.inl ⟨found, rfl⟩
        | boolean _ => exact Or.inr ⟨_, rfl⟩
        | nat _ => exact Or.inr ⟨_, rfl⟩
        | int _ => exact Or.inr ⟨_, rfl⟩
        | string _ => exact Or.inr ⟨_, rfl⟩
        | char _ => exact Or.inr ⟨_, rfl⟩
        | array _ _ => exact Or.inr ⟨_, rfl⟩
        | variant _ _ _ => exact Or.inr ⟨_, rfl⟩
        | closure _ _ _ => exact Or.inr ⟨_, rfl⟩
      · rw [run]
        exact Or.inr ⟨fault, rfl⟩

/-- Running the lowering of a readable scrutinee changes no state. -/
theorem targetStable_of_readable {program : Ir.Program} {target : Target.Program}
    {runtime : Runtime} {fuel : Nat} :
    ∀ (scrutinee : Ir.Expr) (emitted : Target.Expr),
      Compile.readableScrutinee scrutinee = true →
      Compile.expr program scrutinee = .ok emitted →
      StateStable target runtime fuel emitted
  | .varRef index, emitted, _, compiled => by
      simp only [Compile.expr] at compiled
      injection compiled with emittedEq
      subst emittedEq
      intro targetScope state produced next run
      simp only [Target.eval] at run
      cases lookup : Target.lookup targetScope index with
      | none => rw [lookup] at run; simp at run
      | some value => rw [lookup] at run; injection run with _ stateEq; exact stateEq.symm
  | .fieldGet subject field, emitted, readable, compiled => by
      simp only [Compile.readableScrutinee] at readable
      simp only [Compile.expr] at compiled
      obtain ⟨emittedSubject, subjectCompiled, shape⟩ := bind_ok compiled
      injection shape with emittedEq
      subst emittedEq
      have inner : StateStable target runtime fuel emittedSubject :=
        targetStable_of_readable subject emittedSubject readable subjectCompiled
      intro targetScope state produced next run
      simp only [Target.eval] at run
      cases subjectRun : Target.eval target runtime fuel targetScope state emittedSubject with
      | thrown error middle => rw [subjectRun] at run; simp at run
      | fault fault middle => rw [subjectRun] at run; simp at run
      | exhausted middle => rw [subjectRun] at run; simp at run
      | ok value middle =>
          rw [subjectRun] at run
          have sameMiddle := inner targetScope state value middle subjectRun
          subst sameMiddle
          simp only [Target.readMember] at run
          cases value with
          | object ref =>
              dsimp only at run
              cases read : middle.heap.getOwnProperty ref (Ir.propertyKey field) with
              | error fault => rw [read] at run; simp at run
              | ok descriptor =>
                  rw [read] at run
                  cases descriptor with
                  | none => injection run with _ stateEq; exact stateEq.symm
                  | some entry =>
                      cases entry with
                      | data data => injection run with _ stateEq; exact stateEq.symm
                      | accessor accessor => simp at run
          | primitive value =>
              cases value with
              | undefined => simp at run
              | null => simp at run
              | boolean _ => simp at run
              | number _ => simp at run
              | string _ => simp at run
              | bigint _ => simp at run
              | symbol _ => simp at run

/-! ## List simulations -/

/-- The empty argument list refines the empty argument list. -/
theorem everywhereList_nil {program : Ir.Program} {target : Target.Program} {runtime : Runtime}
    {fuel : Nat} : EverywhereList program target runtime fuel [] [] := by
  intro sourceScope targetScope trace state aligned
  simp only [Source.evalList, Target.evalList, Relation.RefinesList]
  exact ⟨Target.State.Extension.refl state aligned.heapValid, aligned.closuresValid,
    represents_nil, aligned.trace⟩

/-- An argument list is evaluated left to right, once each. -/
theorem everywhereList_cons {program : Ir.Program} {target : Target.Program} {runtime : Runtime}
    {fuel : Nat} {head : Ir.Expr} {emittedHead : Target.Expr} {rest : List Ir.Expr}
    {emittedRest : List Target.Expr}
    (headStep : Everywhere program target runtime fuel head emittedHead)
    (restStep : EverywhereList program target runtime fuel rest emittedRest) :
    EverywhereList program target runtime fuel (head :: rest) (emittedHead :: emittedRest) := by
  intro sourceScope targetScope trace state aligned
  simp only [Source.evalList, Target.evalList]
  cases headRun : Source.eval program fuel sourceScope trace head with
  | fault fault next => simp only [Relation.RefinesList]
  | exhausted next =>
      obtain ⟨targetState, targetRun, extension, closuresValid, traceRefines⟩ :=
        refines_exhausted_inv (headRun ▸ headStep sourceScope targetScope trace state aligned)
      rw [targetRun]
      simp only [Relation.RefinesList]
      exact ⟨extension, closuresValid, traceRefines⟩
  | value produced next =>
      obtain ⟨image, targetState, targetRun, extension, closuresValid, related, traceRefines⟩ :=
        refines_value_inv (headRun ▸ headStep sourceScope targetScope trace state aligned)
      rw [targetRun]
      dsimp only
      have nextAligned := aligned.step extension closuresValid traceRefines
      cases restRun : Source.evalList program fuel sourceScope next rest with
      | fault fault last => simp only [Relation.RefinesList]
      | exhausted last =>
          obtain ⟨lastState, lastRun, lastExtension, lastValid, lastTrace⟩ :=
            refinesList_exhausted_inv
              (restRun ▸ restStep sourceScope targetScope next targetState nextAligned)
          rw [lastRun]
          simp only [Relation.RefinesList]
          exact ⟨extension.trans lastExtension, lastValid, lastTrace⟩
      | values values last =>
          obtain ⟨targets, lastState, lastRun, lastExtension, lastValid, listRelated,
            lastTrace⟩ :=
            refinesList_inv
              (restRun ▸ restStep sourceScope targetScope next targetState nextAligned)
          rw [lastRun]
          simp only [Relation.RefinesList]
          refine ⟨extension.trans lastExtension, lastValid, ?_, lastTrace⟩
          unfold Relation.RepresentsList
          exact ⟨image, targets, rfl,
            Relation.Represents.stable lastExtension produced image related, listRelated⟩

/-- The empty field list refines the empty property list. -/
theorem everywhereFields_nil {program : Ir.Program} {target : Target.Program} {runtime : Runtime}
    {fuel : Nat} : EverywhereFields program target runtime fuel [] [] := by
  intro sourceScope targetScope trace state aligned
  simp only [Source.evalFields, Target.evalProperties, Relation.RefinesFields]
  refine ⟨Target.State.Extension.refl state aligned.heapValid, aligned.closuresValid, ?_,
    aligned.trace⟩
  unfold Relation.RepresentsFields
  rfl

/-- A field list is evaluated left to right, once each, keeping declaration order. -/
theorem everywhereFields_cons {program : Ir.Program} {target : Target.Program} {runtime : Runtime}
    {fuel : Nat} {name : String} {head : Ir.Expr} {emittedHead : Target.Expr}
    {rest : List (String × Ir.Expr)} {emittedRest : List (String × Target.Expr)}
    (headStep : Everywhere program target runtime fuel head emittedHead)
    (restStep : EverywhereFields program target runtime fuel rest emittedRest) :
    EverywhereFields program target runtime fuel ((name, head) :: rest)
      ((name, emittedHead) :: emittedRest) := by
  intro sourceScope targetScope trace state aligned
  simp only [Source.evalFields, Target.evalProperties]
  cases headRun : Source.eval program fuel sourceScope trace head with
  | fault fault next => simp only [Relation.RefinesFields]
  | exhausted next =>
      obtain ⟨targetState, targetRun, extension, closuresValid, traceRefines⟩ :=
        refines_exhausted_inv (headRun ▸ headStep sourceScope targetScope trace state aligned)
      rw [targetRun]
      simp only [Relation.RefinesFields]
      exact ⟨extension, closuresValid, traceRefines⟩
  | value produced next =>
      obtain ⟨image, targetState, targetRun, extension, closuresValid, related, traceRefines⟩ :=
        refines_value_inv (headRun ▸ headStep sourceScope targetScope trace state aligned)
      rw [targetRun]
      dsimp only
      have nextAligned := aligned.step extension closuresValid traceRefines
      cases restRun : Source.evalFields program fuel sourceScope next rest with
      | fault fault last => simp only [Relation.RefinesFields]
      | exhausted last =>
          obtain ⟨lastState, lastRun, lastExtension, lastValid, lastTrace⟩ :=
            refinesFields_exhausted_inv
              (restRun ▸ restStep sourceScope targetScope next targetState nextAligned)
          rw [lastRun]
          simp only [Relation.RefinesFields]
          exact ⟨extension.trans lastExtension, lastValid, lastTrace⟩
      | fields values last =>
          obtain ⟨entries, lastState, lastRun, lastExtension, lastValid, fieldsRelated,
            lastTrace⟩ :=
            refinesFields_inv
              (restRun ▸ restStep sourceScope targetScope next targetState nextAligned)
          rw [lastRun]
          simp only [Relation.RefinesFields]
          refine ⟨extension.trans lastExtension, lastValid, ?_, lastTrace⟩
          unfold Relation.RepresentsFields
          exact ⟨image, entries, rfl,
            Relation.Represents.stable lastExtension produced image related, fieldsRelated⟩

/-- Lowering an argument list keeps its length. -/
theorem exprList_length {program : Ir.Program} :
    ∀ (expressions : List Ir.Expr) (emitted : List Target.Expr),
      Compile.exprList program expressions = .ok emitted →
      emitted.length = expressions.length
  | [], emitted, compiled => by
      simp only [Compile.exprList, pure, Except.pure] at compiled
      injection compiled with emittedEq
      subst emittedEq
      rfl
  | expression :: rest, emitted, compiled => by
      simp only [Compile.exprList] at compiled
      obtain ⟨emittedHead, _, more⟩ := bind_ok compiled
      obtain ⟨emittedRest, restCompiled, shape⟩ := bind_ok more
      simp only [pure, Except.pure] at shape
      injection shape with emittedEq
      subst emittedEq
      simp only [List.length_cons]
      rw [exprList_length rest emittedRest restCompiled]

/-- A lowered body is either a `const` binding of a leading `let`, or one `return`. -/
theorem body_inversion {program : Ir.Program} {expression : Ir.Expr} {emitted : Target.Body}
    (compiled : Compile.body program expression = .ok emitted) :
    (∃ name value rest emittedValue emittedRest, expression = .letBind name value rest ∧
        emitted = .constBind name emittedValue emittedRest ∧
        Compile.expr program value = .ok emittedValue ∧
        Compile.body program rest = .ok emittedRest) ∨
      (∃ emittedExpression, emitted = .ret emittedExpression ∧
        Compile.expr program expression = .ok emittedExpression) := by
  cases expression
  case letBind name value rest =>
    simp only [Compile.body] at compiled
    obtain ⟨emittedValue, valueCompiled, more⟩ := bind_ok compiled
    obtain ⟨emittedRest, restCompiled, shape⟩ := bind_ok more
    simp only [pure, Except.pure] at shape
    injection shape with emittedEq
    exact Or.inl ⟨name, value, rest, emittedValue, emittedRest, rfl, emittedEq.symm, valueCompiled,
      restCompiled⟩
  all_goals (
    simp only [Compile.body] at compiled
    obtain ⟨emittedExpression, expressionCompiled, shape⟩ := bind_ok compiled
    simp only [pure, Except.pure] at shape
    injection shape with emittedEq
    exact Or.inr ⟨emittedExpression, emittedEq.symm, expressionCompiled⟩)

/--
The payload check accepts exactly the alternatives whose payload the emitted object presents back:
every field name is an own key in declaration order, no two of them are the same, and none of them is
the `kind` the tag occupies. Those are the three conditions `readPayload_of_represents` reads the
payload under.
-/
theorem payloadKeys_of_checkPayloads {type : Ir.Ty} :
    ∀ (constructors : List Ir.Constructor),
      Compile.checkPayloads type constructors = .ok () →
      ∀ constructor ∈ constructors, (∀ field ∈ constructor.fields, field.name ≠ "kind") ∧
        (constructor.fields.map Ir.Field.name).Nodup
  | [], _, _, member => absurd member (by simp)
  | head :: rest, checked, constructor, member => by
      simp only [Compile.checkPayloads] at checked
      by_cases unpresentable : Compile.presentableKeys (head.fields.map Ir.Field.name) = false
      · rw [if_pos unpresentable] at checked
        simp [throw, throwThe, MonadExceptOf.throw] at checked
      · rw [if_neg unpresentable] at checked
        by_cases reserved : (head.fields.map Ir.Field.name).all (· != "kind") = false
        · rw [if_pos reserved] at checked
          simp [throw, throwThe, MonadExceptOf.throw] at checked
        · rw [if_neg reserved] at checked
          rcases List.mem_cons.mp member with headEq | tailMember
          · subst headEq
            obtain ⟨_, distinct⟩ :=
              Compile.presentableKeys_iff.mp (by simpa using unpresentable)
            exact ⟨by simpa using reserved, distinct⟩
          · exact payloadKeys_of_checkPayloads rest checked constructor tailMember

/-! ## Inverting the lowering of an operation

`Compile.expr` decides an operation's target form from `Ir.Opcode.operator?` and the operand count,
so one case analysis over those two answers every question the `operation` row asks.
-/

/-- An opcode spelled as one operator is spelled as no other. -/
private theorem notOperator_of_arity {opcode : Ir.Opcode} {form : Ir.OperatorForm}
    {arguments : List Ir.Expr} (spelled : opcode.operator? = some form)
    (arity : arguments.length ≠ form.operands) :
    ∀ candidate, opcode.operator? = some candidate → arguments.length ≠ candidate.operands := by
  intro candidate candidateEq
  rw [spelled] at candidateEq
  injection candidateEq with formEq
  subst formEq
  exact arity

/-- Every target form `Compile.expr` gives an operation, and the operands it gives it for. -/
theorem compile_operation_inv {program : Ir.Program} {opcode : Ir.Opcode}
    {typeArguments : List Ir.Ty} {arguments : List Ir.Expr} {emitted : Target.Expr}
    (compiled : Compile.expr program (.operation opcode typeArguments arguments) = .ok emitted) :
    (∃ left right emittedLeft emittedRight, opcode = .boolAnd ∧ arguments = [left, right] ∧
        Compile.expr program left = .ok emittedLeft ∧
        Compile.expr program right = .ok emittedRight ∧
        emitted = .logicalAnd emittedLeft emittedRight) ∨
      (∃ left right emittedLeft emittedRight, opcode = .boolOr ∧ arguments = [left, right] ∧
        Compile.expr program left = .ok emittedLeft ∧
        Compile.expr program right = .ok emittedRight ∧
        emitted = .logicalOr emittedLeft emittedRight) ∨
      (∃ operand emittedOperand, opcode = .boolNot ∧ arguments = [operand] ∧
        Compile.expr program operand = .ok emittedOperand ∧
        emitted = .logicalNot emittedOperand) ∨
      (∃ left right, opcode = .boolEquals ∧ arguments = [left, right] ∧
        right = .boolLit true ∧ Compile.expr program left = .ok emitted) ∨
      (∃ left right, opcode = .boolEquals ∧ arguments = [left, right] ∧
        left = .boolLit true ∧ Compile.expr program right = .ok emitted) ∨
      (∃ left right emittedLeft emittedRight, opcode = .boolEquals ∧ arguments = [left, right] ∧
        Compile.expr program left = .ok emittedLeft ∧
        Compile.expr program right = .ok emittedRight ∧
        emitted = .strictEquals emittedLeft emittedRight) ∨
      ((∀ form, opcode.operator? = some form → arguments.length ≠ form.operands) ∧
        ∃ emittedArguments, Compile.exprList program arguments = .ok emittedArguments ∧
          emitted = .operation opcode emittedArguments) := by
  rw [Compile.expr.eq_def] at compiled
  dsimp only at compiled
  have general : ∀ notOperator : ∀ form, opcode.operator? = some form →
        arguments.length ≠ form.operands,
      (do pure (.operation opcode (← Compile.exprList program arguments)) :
          Except Compile.Fault Target.Expr) = .ok emitted →
      ((∀ form, opcode.operator? = some form → arguments.length ≠ form.operands) ∧
        ∃ emittedArguments, Compile.exprList program arguments = .ok emittedArguments ∧
          emitted = .operation opcode emittedArguments) := by
    intro notOperator run
    obtain ⟨emittedArguments, argumentsCompiled, shape⟩ := bind_ok run
    simp only [pure, Except.pure] at shape
    injection shape with emittedEq
    exact ⟨notOperator, emittedArguments, argumentsCompiled, emittedEq.symm⟩
  rcases option_cases opcode.operator? with spelled | ⟨form, spelled⟩
  · rw [spelled] at compiled
    simp only at compiled
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (general (by intro form formEq; rw [spelled] at formEq; simp at formEq) compiled))))))
  · rw [spelled] at compiled
    cases form with
      | logicalAnd =>
          have opcodeEq := Ir.Opcode.eq_boolAnd_of_operator? spelled
          cases arguments with
          | nil =>
              simp only at compiled
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                (general (notOperator_of_arity spelled (by simp [Ir.OperatorForm.operands]))
                  compiled))))))
          | cons left rest =>
              cases rest with
              | nil =>
                  simp only at compiled
                  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                    (general (notOperator_of_arity spelled (by simp [Ir.OperatorForm.operands]))
                      compiled))))))
              | cons right tail =>
                  cases tail with
                  | cons third more =>
                      simp only at compiled
                      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                        (general (notOperator_of_arity spelled
                          (by simp [Ir.OperatorForm.operands])) compiled))))))
                  | nil =>
                      simp only at compiled
                      obtain ⟨emittedLeft, leftCompiled, more⟩ := bind_ok compiled
                      obtain ⟨emittedRight, rightCompiled, shape⟩ := bind_ok more
                      simp only [pure, Except.pure] at shape
                      injection shape with emittedEq
                      exact Or.inl ⟨left, right, emittedLeft, emittedRight, opcodeEq, rfl,
                        leftCompiled, rightCompiled, emittedEq.symm⟩
      | logicalOr =>
          have opcodeEq := Ir.Opcode.eq_boolOr_of_operator? spelled
          cases arguments with
          | nil =>
              simp only at compiled
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                (general (notOperator_of_arity spelled (by simp [Ir.OperatorForm.operands]))
                  compiled))))))
          | cons left rest =>
              cases rest with
              | nil =>
                  simp only at compiled
                  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                    (general (notOperator_of_arity spelled (by simp [Ir.OperatorForm.operands]))
                      compiled))))))
              | cons right tail =>
                  cases tail with
                  | cons third more =>
                      simp only at compiled
                      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                        (general (notOperator_of_arity spelled
                          (by simp [Ir.OperatorForm.operands])) compiled))))))
                  | nil =>
                      simp only at compiled
                      obtain ⟨emittedLeft, leftCompiled, more⟩ := bind_ok compiled
                      obtain ⟨emittedRight, rightCompiled, shape⟩ := bind_ok more
                      simp only [pure, Except.pure] at shape
                      injection shape with emittedEq
                      exact Or.inr (Or.inl ⟨left, right, emittedLeft, emittedRight, opcodeEq, rfl,
                        leftCompiled, rightCompiled, emittedEq.symm⟩)
      | logicalNot =>
          have opcodeEq := Ir.Opcode.eq_boolNot_of_operator? spelled
          cases arguments with
          | nil =>
              simp only at compiled
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                (general (notOperator_of_arity spelled (by simp [Ir.OperatorForm.operands]))
                  compiled))))))
          | cons operand rest =>
              cases rest with
              | cons second tail =>
                  simp only at compiled
                  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                    (general (notOperator_of_arity spelled (by simp [Ir.OperatorForm.operands]))
                      compiled))))))
              | nil =>
                  simp only at compiled
                  obtain ⟨emittedOperand, operandCompiled, shape⟩ := bind_ok compiled
                  simp only [pure, Except.pure] at shape
                  injection shape with emittedEq
                  exact Or.inr (Or.inr (Or.inl ⟨operand, emittedOperand, opcodeEq, rfl,
                    operandCompiled, emittedEq.symm⟩))
      | strictEquals =>
          have opcodeEq := Ir.Opcode.eq_boolEquals_of_operator? spelled
          cases arguments with
          | nil =>
              simp only at compiled
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                (general (notOperator_of_arity spelled (by simp [Ir.OperatorForm.operands]))
                  compiled))))))
          | cons left rest =>
              cases rest with
              | nil =>
                  simp only at compiled
                  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                    (general (notOperator_of_arity spelled (by simp [Ir.OperatorForm.operands]))
                      compiled))))))
              | cons right tail =>
                  cases tail with
                  | cons third more =>
                      simp only at compiled
                      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                        (general (notOperator_of_arity spelled
                          (by simp [Ir.OperatorForm.operands])) compiled))))))
                  | nil =>
                      simp only at compiled
                      by_cases foldRight : right.isTrueLiteral = true
                      · rw [if_pos foldRight] at compiled
                        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨left, right, opcodeEq, rfl,
                          Ir.Expr.eq_of_isTrueLiteral foldRight, compiled⟩)))
                      · rw [if_neg foldRight] at compiled
                        by_cases foldLeft : left.isTrueLiteral = true
                        · rw [if_pos foldLeft] at compiled
                          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨left, right, opcodeEq, rfl,
                            Ir.Expr.eq_of_isTrueLiteral foldLeft, compiled⟩))))
                        · rw [if_neg foldLeft] at compiled
                          obtain ⟨emittedLeft, leftCompiled, more⟩ := bind_ok compiled
                          obtain ⟨emittedRight, rightCompiled, shape⟩ := bind_ok more
                          simp only [pure, Except.pure] at shape
                          injection shape with emittedEq
                          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                            ⟨left, right, emittedLeft, emittedRight, opcodeEq, rfl, leftCompiled,
                              rightCompiled, emittedEq.symm⟩)))))

/-! ## Inverting the lowering of a constructor -/

/-- Every target form `Compile.expr` gives a constructor, and the arguments it gives it for. -/
theorem compile_variant_inv {program : Ir.Program} {type : Ir.Ty} {name : String}
    {arguments : List Ir.Expr} {emitted : Target.Expr}
    (compiled : Compile.expr program (.variant type name arguments) = .ok emitted) :
    (∃ element, type = .list element ∧ name = "nil" ∧ arguments = [] ∧
        emitted = .arrayEmpty) ∨
      (∃ element head tail emittedHead emittedTail, type = .list element ∧ name = "cons" ∧
        arguments = [head, tail] ∧ Compile.expr program head = .ok emittedHead ∧
        Compile.expr program tail = .ok emittedTail ∧
        emitted = .arrayCons emittedHead emittedTail) ∨
      (type.element? = none ∧ ∃ constructors constructor emittedArguments,
        program.constructorsOf type = some constructors ∧
        Ir.constructor? constructors name = some constructor ∧
        Compile.exprList program arguments = .ok emittedArguments ∧
        constructor.fields.length = emittedArguments.length ∧
        Compile.presentableKeys (constructor.fields.map Ir.Field.name) = true ∧
        (constructor.fields.map Ir.Field.name).all (· != "kind") = true ∧
        emitted = (if Ir.allNullary constructors && constructor.fields.isEmpty then
            .stringLit name
          else .objectLiteral (("kind", .stringLit name) ::
            (constructor.fields.map Ir.Field.name).zip emittedArguments))) := by
  rw [Compile.expr.eq_def] at compiled
  dsimp only at compiled
  rcases option_cases type.element? with notList | ⟨element, isList⟩
  · rw [notList] at compiled
    simp only at compiled
    rcases option_cases (program.constructorsOf type) with declared | ⟨constructors, declared⟩
    · rw [declared] at compiled
      simp [throw, throwThe, MonadExceptOf.throw] at compiled
    · rw [declared] at compiled
      dsimp only at compiled
      rcases option_cases (Ir.constructor? constructors name) with selected | ⟨constructor, selected⟩
      · rw [selected] at compiled
        simp [throw, throwThe, MonadExceptOf.throw] at compiled
      · rw [selected] at compiled
        dsimp only at compiled
        obtain ⟨emittedArguments, argumentsCompiled, rest⟩ := bind_ok compiled
        by_cases arity : constructor.fields.length ≠ emittedArguments.length
        · rw [if_pos arity] at rest
          simp [throw, throwThe, MonadExceptOf.throw] at rest
        · rw [if_neg arity] at rest
          by_cases unpresentable :
              Compile.presentableKeys (constructor.fields.map Ir.Field.name) = false
          · rw [if_pos unpresentable] at rest
            simp [throw, throwThe, MonadExceptOf.throw] at rest
          · rw [if_neg unpresentable] at rest
            by_cases reserved :
                (constructor.fields.map Ir.Field.name).all (· != "kind") = false
            · rw [if_pos reserved] at rest
              simp [throw, throwThe, MonadExceptOf.throw] at rest
            · rw [if_neg reserved] at rest
              refine Or.inr (Or.inr ⟨notList, constructors, constructor, emittedArguments,
                declared, selected, argumentsCompiled,
                Decidable.byContradiction fun different => arity different,
                by simpa using unpresentable, by simpa using reserved, ?_⟩)
              by_cases nullary :
                  (Ir.allNullary constructors && constructor.fields.isEmpty) = true
              · rw [if_pos nullary] at rest ⊢
                simp only [pure, Except.pure] at rest
                injection rest with emittedEq
                exact emittedEq.symm
              · rw [if_neg nullary] at rest ⊢
                simp only [pure, Except.pure] at rest
                injection rest with emittedEq
                exact emittedEq.symm
  · rw [isList] at compiled
    have typeEq := Ir.Ty.eq_list_of_element? isList
    simp only at compiled
    split at compiled
    · simp only [pure, Except.pure] at compiled
      injection compiled with emittedEq
      exact Or.inl ⟨element, typeEq, rfl, rfl, emittedEq.symm⟩
    · rename_i head tail
      obtain ⟨emittedHead, headCompiled, more⟩ := bind_ok compiled
      obtain ⟨emittedTail, tailCompiled, shape⟩ := bind_ok more
      simp only [pure, Except.pure] at shape
      injection shape with emittedEq
      exact Or.inr (Or.inl ⟨element, head, tail, emittedHead, emittedTail, typeEq, rfl, rfl,
        headCompiled, tailCompiled, emittedEq.symm⟩)
    · simp [throw, throwThe, MonadExceptOf.throw] at compiled

/-! ## The two constraints the decoder enforces, stated -/

/-- A lambda captures exactly the enclosing binders, in scope order. -/
theorem lambda_captures_enclosing_scope (program : Ir.Program) (fuel : Nat)
    (parameters : List Ir.Field) (body : Ir.Expr) (scope : List Source.Value)
    (trace : Source.Trace) :
    Source.eval program fuel scope trace (.lambda parameters body)
      = .value (.closure scope parameters body) trace := by
  simp only [Source.eval]


/-! ## The whole-program theorem -/

mutual

/-- Every expression the lowering admits refines its source, from every aligned configuration. -/
theorem everywhere {program : Ir.Program} {target : Target.Program} {runtime : Runtime}
    (lowered : LoweredProgram program target) (laws : RuntimeLaws runtime)
    (listsFit : ListsFit program) (fuel : Nat) :
    ∀ (expression : Ir.Expr) (emitted : Target.Expr),
      Compile.expr program expression = .ok emitted →
      Everywhere program target runtime fuel expression emitted
  | .varRef index, emitted, compiled => by
      simp only [Compile.expr, pure, Except.pure] at compiled
      injection compiled with emittedEq
      subst emittedEq
      exact varRef program target fuel index
  | .boolLit value, emitted, compiled => by
      simp only [Compile.expr, pure, Except.pure] at compiled
      injection compiled with emittedEq
      subst emittedEq
      exact boolLit program target fuel value
  | .natLit value, emitted, compiled => by
      simp only [Compile.expr, pure, Except.pure] at compiled
      injection compiled with emittedEq
      subst emittedEq
      exact natLit program target fuel value
  | .stringLit value, emitted, compiled => by
      simp only [Compile.expr, pure, Except.pure] at compiled
      injection compiled with emittedEq
      subst emittedEq
      exact stringLit program target fuel value
  | .letBind name value body, emitted, compiled => by
      simp only [Compile.expr, throw, throwThe, MonadExceptOf.throw] at compiled
      exact absurd compiled (by simp)
  | .fieldGet subject field, emitted, compiled => by
      simp only [Compile.expr] at compiled
      obtain ⟨emittedSubject, subjectCompiled, shape⟩ := bind_ok compiled
      simp only [pure, Except.pure] at shape
      injection shape with emittedEq
      subst emittedEq
      exact fieldGet program target fuel subject field emittedSubject
        (everywhere lowered laws listsFit fuel subject emittedSubject subjectCompiled)
  | .ifThenElse condition consequent alternate, emitted, compiled => by
      simp only [Compile.expr] at compiled
      obtain ⟨emittedCondition, conditionCompiled, rest⟩ := bind_ok compiled
      obtain ⟨emittedConsequent, consequentCompiled, more⟩ := bind_ok rest
      obtain ⟨emittedAlternate, alternateCompiled, shape⟩ := bind_ok more
      simp only [pure, Except.pure] at shape
      injection shape with emittedEq
      subst emittedEq
      exact (ifThenElse (runtime := runtime)).1 program target fuel condition consequent alternate
        emittedCondition
        emittedConsequent emittedAlternate
        (everywhere lowered laws listsFit fuel condition emittedCondition conditionCompiled)
        (everywhere lowered laws listsFit fuel consequent emittedConsequent consequentCompiled)
        (everywhere lowered laws listsFit fuel alternate emittedAlternate alternateCompiled)
  | .operation opcode typeArguments arguments, emitted, compiled => by
      have rows := operation (runtime := runtime) program target fuel
      have bodyAtLower : ∀ smaller, smaller + 1 = fuel →
          ∀ (inner : Ir.Expr) (emittedInner : Target.Body),
            Compile.body program inner = .ok emittedInner →
            EverywhereBody program target runtime smaller inner emittedInner := by
        intro smaller step inner emittedInner innerCompiled
        subst step
        exact everywhereBody lowered laws listsFit smaller inner emittedInner innerCompiled
      rcases compile_operation_inv compiled with
        ⟨left, right, emittedLeft, emittedRight, opcodeEq, argumentsEq, leftCompiled,
          rightCompiled, emittedEq⟩ |
        ⟨left, right, emittedLeft, emittedRight, opcodeEq, argumentsEq, leftCompiled,
          rightCompiled, emittedEq⟩ |
        ⟨operand, emittedOperand, opcodeEq, argumentsEq, operandCompiled, emittedEq⟩ |
        ⟨left, right, opcodeEq, argumentsEq, rightTrue, leftCompiled⟩ |
        ⟨left, right, opcodeEq, argumentsEq, leftTrue, rightCompiled⟩ |
        ⟨left, right, emittedLeft, emittedRight, opcodeEq, argumentsEq, leftCompiled,
          rightCompiled, emittedEq⟩ |
        ⟨notOperator, emittedArguments, argumentsCompiled, emittedEq⟩
      · subst opcodeEq
        subst argumentsEq
        subst emittedEq
        exact rows.1 typeArguments left right emittedLeft emittedRight
          (everywhere lowered laws listsFit fuel left emittedLeft leftCompiled)
          (everywhere lowered laws listsFit fuel right emittedRight rightCompiled)
      · subst opcodeEq
        subst argumentsEq
        subst emittedEq
        exact rows.2.1 typeArguments left right emittedLeft emittedRight
          (everywhere lowered laws listsFit fuel left emittedLeft leftCompiled)
          (everywhere lowered laws listsFit fuel right emittedRight rightCompiled)
      · subst opcodeEq
        subst argumentsEq
        subst emittedEq
        exact rows.2.2.1 typeArguments operand emittedOperand
          (everywhere lowered laws listsFit fuel operand emittedOperand operandCompiled)
      · subst opcodeEq
        subst argumentsEq
        subst rightTrue
        exact (rows.2.2.2.1 typeArguments left (.boolLit true) emitted (.boolLit true)
          (everywhere lowered laws listsFit fuel left emitted leftCompiled)
          (everywhere lowered laws listsFit fuel (.boolLit true) (.boolLit true)
            (by simp [Compile.expr, pure, Except.pure]))).2.1
      · subst opcodeEq
        subst argumentsEq
        subst leftTrue
        exact (rows.2.2.2.1 typeArguments (.boolLit true) right (.boolLit true) emitted
          (everywhere lowered laws listsFit fuel (.boolLit true) (.boolLit true)
            (by simp [Compile.expr, pure, Except.pure]))
          (everywhere lowered laws listsFit fuel right emitted rightCompiled)).2.2
      · subst opcodeEq
        subst argumentsEq
        subst emittedEq
        exact (rows.2.2.2.1 typeArguments left right emittedLeft emittedRight
          (everywhere lowered laws listsFit fuel left emittedLeft leftCompiled)
          (everywhere lowered laws listsFit fuel right emittedRight rightCompiled)).1
      · subst emittedEq
        exact rows.2.2.2.2 opcode typeArguments arguments emittedArguments notOperator
          (Opcode.registry runtime opcode (laws opcode)) listsFit
          (everywhereList lowered laws listsFit fuel arguments emittedArguments argumentsCompiled)
          bodyAtLower
  | .variant type name arguments, emitted, compiled => by
      have rows := variant (runtime := runtime) program target fuel
      rcases compile_variant_inv compiled with
        ⟨element, typeEq, nameEq, argumentsEq, emittedEq⟩ |
        ⟨element, head, tail, emittedHead, emittedTail, typeEq, nameEq, argumentsEq, headCompiled,
          tailCompiled, emittedEq⟩ |
        ⟨notList, constructors, constructor, emittedArguments, declared, selected,
          argumentsCompiled, arity, presentable, reserved, emittedEq⟩
      · subst typeEq
        subst nameEq
        subst argumentsEq
        subst emittedEq
        exact rows.2.1 element
      · subst typeEq
        subst nameEq
        subst argumentsEq
        subst emittedEq
        exact rows.2.2 element head tail emittedHead emittedTail listsFit
          (everywhere lowered laws listsFit fuel head emittedHead headCompiled)
          (everywhere lowered laws listsFit fuel tail emittedTail tailCompiled)
      · obtain ⟨keys, distinct⟩ := Compile.presentableKeys_iff.mp presentable
        have notReserved : ∀ field ∈ constructor.fields, ¬field.name = "kind" := by
          simpa using reserved
        have lengths : emittedArguments.length = arguments.length :=
          exprList_length arguments emittedArguments argumentsCompiled
        have fieldArity : constructor.fields.length = arguments.length := by rw [arity, lengths]
        have fieldKeys : ∀ field ∈ constructor.fields,
            Ir.ValidKey field.name ∧ field.name ≠ "kind" := fun field member =>
          ⟨keys field.name (List.mem_map_of_mem member), notReserved field member⟩
        have rowPair := rows.1 type name constructors constructor arguments emittedArguments notList
          declared selected fieldKeys distinct fieldArity lengths.symm
          (everywhereList lowered laws listsFit fuel arguments emittedArguments argumentsCompiled)
        by_cases nullary : (Ir.allNullary constructors && constructor.fields.isEmpty) = true
        · rw [if_pos nullary] at emittedEq
          subst emittedEq
          refine rowPair.1 ?_
          simp only [Bool.and_eq_true] at nullary
          exact nullary.1
        · rw [if_neg nullary] at emittedEq
          subst emittedEq
          refine rowPair.2 ?_
          cases allNullary : Ir.allNullary constructors with
          | false => rfl
          | true =>
              refine absurd ?_ nullary
              simp only [Bool.and_eq_true]
              exact ⟨allNullary, List.isEmpty_iff.mpr (nullary_fields allNullary selected)⟩
  | .record type fields, emitted, compiled => by
      rw [Compile.expr.eq_def] at compiled
      dsimp only at compiled
      rcases option_cases (program.constructorsOf type) with declared | ⟨constructors, declared⟩
      · rw [declared] at compiled
        simp [throw, throwThe, MonadExceptOf.throw] at compiled
      · rw [declared] at compiled
        cases constructors with
        | nil => simp [throw, throwThe, MonadExceptOf.throw] at compiled
        | cons constructor rest =>
            cases rest with
            | cons second more => simp [throw, throwThe, MonadExceptOf.throw] at compiled
            | nil =>
                dsimp only at compiled
                by_cases mismatch :
                    (fields.map Prod.fst) ≠ (constructor.fields.map Ir.Field.name)
                · rw [if_pos mismatch] at compiled
                  simp [throw, throwThe, MonadExceptOf.throw] at compiled
                · rw [if_neg mismatch] at compiled
                  by_cases unpresentable :
                      Compile.presentableKeys (fields.map Prod.fst) = false
                  · rw [if_pos unpresentable] at compiled
                    simp [throw, throwThe, MonadExceptOf.throw] at compiled
                  · rw [if_neg unpresentable] at compiled
                    obtain ⟨emittedFields, fieldsCompiled, shape⟩ := bind_ok compiled
                    simp only [pure, Except.pure] at shape
                    injection shape with emittedEq
                    subst emittedEq
                    obtain ⟨keys, distinct⟩ :=
                      Compile.presentableKeys_iff.mp (by simpa using unpresentable)
                    exact record program target fuel type fields emittedFields
                      (fun field member => keys field.1 (List.mem_map_of_mem member)) distinct
                      (everywhereFields lowered laws listsFit fuel fields emittedFields
                        fieldsCompiled)
  | .matchOn type scrutinee cases, emitted, compiled => by
      rw [Compile.expr.eq_def] at compiled
      dsimp only at compiled
      rcases option_cases (program.constructorsOf type) with declared | ⟨constructors, declared⟩
      · rw [declared] at compiled
        simp [throw, throwThe, MonadExceptOf.throw] at compiled
      · rw [declared] at compiled
        dsimp only at compiled
        by_cases payload : Ir.allNullary constructors = false
        · rw [if_pos payload] at compiled
          simp [throw, throwThe, MonadExceptOf.throw] at compiled
        · rw [if_neg payload] at compiled
          by_cases computed : Compile.readableScrutinee scrutinee = false
          · rw [if_pos computed] at compiled
            simp [throw, throwThe, MonadExceptOf.throw] at compiled
          · rw [if_neg computed] at compiled
            obtain ⟨emittedScrutinee, scrutineeCompiled, rest⟩ := bind_ok compiled
            obtain ⟨emittedCases, casesCompiled, shape⟩ := bind_ok rest
            rcases option_cases (Compile.tagChain emittedScrutinee emittedCases) with
              built | ⟨chain, built⟩
            · rw [built] at shape
              simp [throw, throwThe, MonadExceptOf.throw] at shape
            · rw [built] at shape
              simp only [pure, Except.pure] at shape
              injection shape with emittedEq
              subst emittedEq
              have readable : Compile.readableScrutinee scrutinee = true := by simpa using computed
              exact (matchOn (runtime := runtime)).1 program target fuel type scrutinee cases
                emittedScrutinee
                emittedCases chain constructors declared (by simpa using payload)
                ⟨everywhere lowered laws listsFit fuel scrutinee emittedScrutinee scrutineeCompiled,
                  sourcePure_of_readable scrutinee readable,
                  targetStable_of_readable scrutinee emittedScrutinee readable scrutineeCompiled⟩
                (everywhereCases lowered laws listsFit fuel cases emittedCases casesCompiled) built
  | .lambda parameters body, emitted, compiled => by
      simp only [Compile.expr] at compiled
      obtain ⟨emittedBody, bodyCompiled, shape⟩ := bind_ok compiled
      simp only [pure, Except.pure] at shape
      injection shape with emittedEq
      subst emittedEq
      exact lambda program target fuel parameters body emittedBody bodyCompiled
        (everywhereBody lowered laws listsFit fuel body emittedBody bodyCompiled)
  | .apply callee arguments, emitted, compiled => by
      cases callee with
      | varRef index =>
          simp only [Compile.expr] at compiled
          obtain ⟨emittedArguments, argumentsCompiled, shape⟩ := bind_ok compiled
          simp only [pure, Except.pure] at shape
          injection shape with emittedEq
          subst emittedEq
          refine (apply (runtime := runtime)).1 program target fuel index arguments emittedArguments
            (everywhereList lowered laws listsFit fuel arguments emittedArguments argumentsCompiled) ?_
          intro smaller step body emittedBody bodyCompiled
          subst step
          exact everywhereBody lowered laws listsFit smaller body emittedBody bodyCompiled
      | fieldGet subject field =>
          simp only [Compile.expr] at compiled
          obtain ⟨emittedSubject, subjectCompiled, more⟩ := bind_ok compiled
          obtain ⟨emittedArguments, argumentsCompiled, shape⟩ := bind_ok more
          simp only [pure, Except.pure] at shape
          injection shape with emittedEq
          subst emittedEq
          refine applyField program target fuel subject field emittedSubject arguments emittedArguments
            (everywhere lowered laws listsFit fuel subject emittedSubject subjectCompiled)
            (everywhereList lowered laws listsFit fuel arguments emittedArguments argumentsCompiled) ?_
          intro smaller step body emittedBody bodyCompiled
          subst step
          exact everywhereBody lowered laws listsFit smaller body emittedBody bodyCompiled
      | boolLit _ | natLit _ | stringLit _ | letBind _ _ _ | ifThenElse _ _ _ | operation _ _ _
      | variant _ _ _ | record _ _ | matchOn _ _ _ | lambda _ _ | apply _ _ | call _ _ _ =>
          simp [Compile.expr, throw, throwThe, MonadExceptOf.throw] at compiled
  | .call function typeArguments arguments, emitted, compiled => by
      rw [Compile.expr.eq_def] at compiled
      dsimp only at compiled
      rcases option_cases (program.function? function) with declared | ⟨declaration, declared⟩
      · rw [declared] at compiled
        simp [throw, throwThe, MonadExceptOf.throw] at compiled
      · rw [declared] at compiled
        dsimp only at compiled
        obtain ⟨emittedArguments, argumentsCompiled, shape⟩ := bind_ok compiled
        simp only [pure, Except.pure] at shape
        injection shape with emittedEq
        subst emittedEq
        refine call program target fuel function typeArguments arguments emittedArguments
          (lowered_of_loweredProgram lowered)
          (everywhereList lowered laws listsFit fuel arguments emittedArguments argumentsCompiled)
          ?_
        intro smaller step
        intro name parameters result recursion body emittedFunction functionDeclared found
        obtain ⟨candidate, candidateFound, _, bodyCompiled⟩ :=
          lowered.functions name parameters result recursion body functionDeclared
        rw [candidateFound] at found
        injection found with functionEq
        subst step
        rw [functionEq] at bodyCompiled
        exact everywhereReturnBody lowered laws listsFit smaller body emittedFunction.body
          bodyCompiled
termination_by expression => (fuel, sizeOf expression, 0)

/-- Every function body the lowering admits refines its source. -/
theorem everywhereBody {program : Ir.Program} {target : Target.Program} {runtime : Runtime}
    (lowered : LoweredProgram program target) (laws : RuntimeLaws runtime)
    (listsFit : ListsFit program) (fuel : Nat) :
    ∀ (body : Ir.Expr) (emitted : Target.Body),
      Compile.body program body = .ok emitted →
      EverywhereBody program target runtime fuel body emitted
  | .letBind name value rest, emitted, compiled => by
      simp only [Compile.body] at compiled
      obtain ⟨emittedValue, valueCompiled, more⟩ := bind_ok compiled
      obtain ⟨emittedRest, restCompiled, shape⟩ := bind_ok more
      simp only [pure, Except.pure] at shape
      injection shape with emittedEq
      subst emittedEq
      exact letBind program target fuel name value rest emittedValue emittedRest
        (everywhere lowered laws listsFit fuel value emittedValue valueCompiled)
        (everywhereBody lowered laws listsFit fuel rest emittedRest restCompiled)
  | body, emitted, compiled => by
      rcases body_inversion compiled with
        ⟨name, value, rest, emittedValue, emittedRest, bodyEq, emittedEq, valueCompiled,
          restCompiled⟩ | ⟨emittedExpression, emittedEq, expressionCompiled⟩
      · subst bodyEq
        subst emittedEq
        exact letBind program target fuel name value rest emittedValue emittedRest
          (everywhere lowered laws listsFit fuel value emittedValue valueCompiled)
          (everywhereBody lowered laws listsFit fuel rest emittedRest restCompiled)
      · subst emittedEq
        intro sourceScope targetScope trace state aligned
        simp only [Target.evalBody]
        exact everywhere lowered laws listsFit fuel body emittedExpression expressionCompiled
          sourceScope targetScope trace state aligned
termination_by body => (fuel, sizeOf body, 1)

/-- Every argument list the lowering admits refines its source. -/
theorem everywhereList {program : Ir.Program} {target : Target.Program} {runtime : Runtime}
    (lowered : LoweredProgram program target) (laws : RuntimeLaws runtime)
    (listsFit : ListsFit program) (fuel : Nat) :
    ∀ (expressions : List Ir.Expr) (emitted : List Target.Expr),
      Compile.exprList program expressions = .ok emitted →
      EverywhereList program target runtime fuel expressions emitted
  | [], emitted, compiled => by
      simp only [Compile.exprList, pure, Except.pure] at compiled
      injection compiled with emittedEq
      subst emittedEq
      exact everywhereList_nil
  | expression :: rest, emitted, compiled => by
      simp only [Compile.exprList] at compiled
      obtain ⟨emittedHead, headCompiled, more⟩ := bind_ok compiled
      obtain ⟨emittedRest, restCompiled, shape⟩ := bind_ok more
      simp only [pure, Except.pure] at shape
      injection shape with emittedEq
      subst emittedEq
      exact everywhereList_cons
        (everywhere lowered laws listsFit fuel expression emittedHead headCompiled)
        (everywhereList lowered laws listsFit fuel rest emittedRest restCompiled)
termination_by expressions => (fuel, sizeOf expressions, 0)

/-- Every field list the lowering admits refines its source. -/
theorem everywhereFields {program : Ir.Program} {target : Target.Program} {runtime : Runtime}
    (lowered : LoweredProgram program target) (laws : RuntimeLaws runtime)
    (listsFit : ListsFit program) (fuel : Nat) :
    ∀ (fields : List (String × Ir.Expr)) (emitted : List (String × Target.Expr)),
      Compile.exprFields program fields = .ok emitted →
      EverywhereFields program target runtime fuel fields emitted
  | [], emitted, compiled => by
      simp only [Compile.exprFields, pure, Except.pure] at compiled
      injection compiled with emittedEq
      subst emittedEq
      exact everywhereFields_nil
  | (name, expression) :: rest, emitted, compiled => by
      simp only [Compile.exprFields] at compiled
      obtain ⟨emittedHead, headCompiled, more⟩ := bind_ok compiled
      obtain ⟨emittedRest, restCompiled, shape⟩ := bind_ok more
      simp only [pure, Except.pure] at shape
      injection shape with emittedEq
      subst emittedEq
      exact everywhereFields_cons
        (everywhere lowered laws listsFit fuel expression emittedHead headCompiled)
        (everywhereFields lowered laws listsFit fuel rest emittedRest restCompiled)
termination_by fields => (fuel, sizeOf fields, 0)

/-- Every match arm the lowering admits refines its source. -/
theorem everywhereCases {program : Ir.Program} {target : Target.Program} {runtime : Runtime}
    (lowered : LoweredProgram program target) (laws : RuntimeLaws runtime)
    (listsFit : ListsFit program) (fuel : Nat) :
    ∀ (cases : List (String × Ir.Expr)) (emitted : List (String × Target.Expr)),
      Compile.exprCases program cases = .ok emitted →
      EverywhereCases program target runtime fuel cases emitted
  | [], emitted, compiled => by
      simp only [Compile.exprCases, pure, Except.pure] at compiled
      injection compiled with emittedEq
      subst emittedEq
      unfold EverywhereCases
      rfl
  | (tag, arm) :: rest, emitted, compiled => by
      simp only [Compile.exprCases] at compiled
      obtain ⟨emittedArm, armCompiled, more⟩ := bind_ok compiled
      obtain ⟨emittedRest, restCompiled, shape⟩ := bind_ok more
      simp only [pure, Except.pure] at shape
      injection shape with emittedEq
      subst emittedEq
      unfold EverywhereCases
      exact ⟨emittedArm, emittedRest, rfl,
        everywhere lowered laws listsFit fuel arm emittedArm armCompiled,
        everywhereCases lowered laws listsFit fuel rest emittedRest restCompiled⟩
termination_by cases => (fuel, sizeOf cases, 0)

/-- Every declaration body the lowering admits refines its source, through the statements
`emitReturn` builds for it: the `const` run, the statement-form `if`, the statement-form dispatch,
and the `return` a branch ends in. -/
theorem everywhereReturnBody {program : Ir.Program} {target : Target.Program} {runtime : Runtime}
    (lowered : LoweredProgram program target) (laws : RuntimeLaws runtime)
    (listsFit : ListsFit program) (fuel : Nat) :
    ∀ (body : Ir.Expr) (emitted : Target.Body),
      Compile.returnBody program body = .ok emitted →
      EverywhereBody program target runtime fuel body emitted
  | .letBind name value rest, emitted, compiled => by
      simp only [Compile.returnBody] at compiled
      obtain ⟨emittedValue, valueCompiled, more⟩ := bind_ok compiled
      obtain ⟨emittedRest, restCompiled, shape⟩ := bind_ok more
      simp only [pure, Except.pure] at shape
      injection shape with emittedEq
      subst emittedEq
      exact letBind program target fuel name value rest emittedValue emittedRest
        (everywhere lowered laws listsFit fuel value emittedValue valueCompiled)
        (everywhereReturnBody lowered laws listsFit fuel rest emittedRest restCompiled)
  | .ifThenElse condition consequent alternate, emitted, compiled => by
      simp only [Compile.returnBody] at compiled
      obtain ⟨emittedCondition, conditionCompiled, more⟩ := bind_ok compiled
      obtain ⟨emittedConsequent, consequentCompiled, rest⟩ := bind_ok more
      obtain ⟨emittedAlternate, alternateCompiled, shape⟩ := bind_ok rest
      simp only [pure, Except.pure] at shape
      injection shape with emittedEq
      subst emittedEq
      exact ifThenBody program target fuel condition consequent alternate emittedCondition
        emittedConsequent emittedAlternate
        (everywhere lowered laws listsFit fuel condition emittedCondition conditionCompiled)
        (everywhereReturnBody lowered laws listsFit fuel consequent emittedConsequent
          consequentCompiled)
        (everywhereReturnBody lowered laws listsFit fuel alternate emittedAlternate
          alternateCompiled)
  | .matchOn type scrutinee cases, emitted, compiled => by
      rw [Compile.returnBody.eq_def] at compiled
      dsimp only at compiled
      rcases option_cases (program.constructorsOf type) with declared | ⟨constructors, declared⟩
      · rw [declared] at compiled
        simp [throw, throwThe, MonadExceptOf.throw] at compiled
      · rw [declared] at compiled
        dsimp only at compiled
        by_cases listType : type.element?.isSome = true
        · rw [if_pos listType] at compiled
          simp [throw, throwThe, MonadExceptOf.throw] at compiled
        · rw [if_neg listType] at compiled
          by_cases structured : Compile.destructurable program type = false
          · rw [if_pos structured] at compiled
            simp [throw, throwThe, MonadExceptOf.throw] at compiled
          · rw [if_neg structured] at compiled
            by_cases noArms : cases.isEmpty = true
            · rw [if_pos noArms] at compiled
              simp [throw, throwThe, MonadExceptOf.throw] at compiled
            · rw [if_neg noArms] at compiled
              by_cases drifted : Compile.decidesInOrder constructors cases = false
              · rw [if_pos drifted] at compiled
                simp [throw, throwThe, MonadExceptOf.throw] at compiled
              · rw [if_neg drifted] at compiled
                obtain ⟨_, checked, rest⟩ := bind_ok compiled
                obtain ⟨emittedScrutinee, scrutineeCompiled, more⟩ := bind_ok rest
                obtain ⟨emittedArms, armsCompiled, shape⟩ := bind_ok more
                simp only [pure, Except.pure] at shape
                injection shape with emittedEq
                subst emittedEq
                have notList : type.element? = none := by
                  cases held : type.element? with
                  | none => rfl
                  | some element => rw [held] at listType; simp at listType
                have ordered : cases.map Prod.fst = constructors.map Ir.Constructor.name := by
                  have decided : Compile.decidesInOrder constructors cases = true := by
                    simpa using drifted
                  simp only [Compile.decidesInOrder, Bool.and_eq_true, beq_iff_eq] at decided
                  exact decided.1
                exact (matchOn (runtime := runtime)).2 program target fuel type scrutinee cases
                  emittedScrutinee emittedArms
                  (if Ir.allNullary constructors = true then .tag else .tagged) constructors
                  declared notList (fun nullary => by rw [if_pos nullary])
                  (fun payload => by rw [if_neg (by simp [payload])])
                  (payloadKeys_of_checkPayloads constructors checked)
                  (everywhere lowered laws listsFit fuel scrutinee emittedScrutinee
                    scrutineeCompiled)
                  (everywhereArms lowered laws listsFit fuel type constructors cases emittedArms
                    ordered armsCompiled)
  | .varRef _, emitted, compiled | .boolLit _, emitted, compiled
  | .natLit _, emitted, compiled | .stringLit _, emitted, compiled
  | .fieldGet _ _, emitted, compiled | .operation _ _ _, emitted, compiled
  | .variant _ _ _, emitted, compiled | .record _ _, emitted, compiled
  | .lambda _ _, emitted, compiled | .apply _ _, emitted, compiled
  | .call _ _ _, emitted, compiled => by
      simp only [Compile.returnBody] at compiled
      obtain ⟨emittedExpression, expressionCompiled, shape⟩ := bind_ok compiled
      simp only [pure, Except.pure] at shape
      injection shape with emittedEq
      subst emittedEq
      intro sourceScope targetScope trace state aligned
      simp only [Target.evalBody]
      exact everywhere lowered laws listsFit fuel _ emittedExpression expressionCompiled
        sourceScope targetScope trace state aligned
termination_by body => (fuel, sizeOf body, 1)

/-- Every match arm the statement-form lowering admits refines its source, arm for arm. The arm at
each position carries the constructor the declaration carries there, which is what the order check
`Compile.decidesInOrder` secures and what this theorem consumes. -/
theorem everywhereArms {program : Ir.Program} {target : Target.Program} {runtime : Runtime}
    (lowered : LoweredProgram program target) (laws : RuntimeLaws runtime)
    (listsFit : ListsFit program) (fuel : Nat) (type : Ir.Ty) :
    ∀ (constructors : List Ir.Constructor) (cases : List (String × Ir.Expr))
      (emitted : List (String × List String × Target.Body)),
      cases.map Prod.fst = constructors.map Ir.Constructor.name →
      Compile.returnArms program type constructors cases = .ok emitted →
      EverywhereArms program target runtime fuel constructors cases emitted
  | [], [], emitted, _, compiled => by
      simp only [Compile.returnArms, pure, Except.pure] at compiled
      injection compiled with emittedEq
      subst emittedEq
      unfold EverywhereArms
      exact ⟨rfl, rfl⟩
  | constructor :: constructors, (tag, arm) :: cases, emitted, ordered, compiled => by
      simp only [List.map_cons, List.cons.injEq] at ordered
      obtain ⟨tagEq, restOrdered⟩ := ordered
      simp only [Compile.returnArms] at compiled
      obtain ⟨emittedArm, armCompiled, more⟩ := bind_ok compiled
      obtain ⟨emittedRest, restCompiled, shape⟩ := bind_ok more
      simp only [pure, Except.pure] at shape
      injection shape with emittedEq
      subst emittedEq
      unfold EverywhereArms
      exact ⟨constructor, constructors, emittedArm, emittedRest, rfl, tagEq, rfl,
        everywhereReturnBody lowered laws listsFit fuel arm emittedArm armCompiled,
        everywhereArms lowered laws listsFit fuel type constructors cases emittedRest restOrdered
          restCompiled⟩
  | [], _ :: _, emitted, ordered, compiled => by simp at ordered
  | _ :: _, [], emitted, ordered, compiled => by simp at ordered
termination_by _ cases => (fuel, sizeOf cases, 0)

end

/-! ## The lowered-program premise, derived -/

/-- Lowering a function declaration yields an emitted function with that name, arity and body. -/
theorem declaration_function {program : Ir.Program} {name : String} {parameters : List Ir.Field}
    {result : Ir.Ty} {recursion : Ir.Recursion} {body : Ir.Expr} {emitted : Option Target.Function}
    (compiled : Compile.declaration program (.function name parameters result recursion body)
      = .ok emitted) :
    ∃ emittedBody, emitted = some ⟨name, parameters.length, emittedBody⟩ ∧
      Compile.returnBody program body = .ok emittedBody := by
  simp only [Compile.declaration] at compiled
  obtain ⟨emittedBody, bodyCompiled, shape⟩ := bind_ok compiled
  simp only [pure, Except.pure] at shape
  injection shape with emittedEq
  exact ⟨emittedBody, emittedEq.symm, bodyCompiled⟩

/-- Lowering a host boundary yields an emitted function with that name, arity and reference body.
The emitted module imports the substrate's implementation at that name instead; `HostSubstrate` is
the premise that the two agree, and it is stated separately rather than assumed here. -/
theorem declaration_foreign {program : Ir.Program} {name : String} {host : Ir.HostOp}
    {parameters : List Ir.Field} {result : Ir.Ty} {reference : Ir.Expr}
    {emitted : Option Target.Function}
    (compiled : Compile.declaration program (.foreign name host parameters result reference)
      = .ok emitted) :
    ∃ emittedBody, emitted = some ⟨name, parameters.length, emittedBody⟩ ∧
      Compile.returnBody program reference = .ok emittedBody := by
  simp only [Compile.declaration] at compiled
  obtain ⟨emittedBody, bodyCompiled, shape⟩ := bind_ok compiled
  simp only [pure, Except.pure] at shape
  injection shape with emittedEq
  exact ⟨emittedBody, emittedEq.symm, bodyCompiled⟩

/--
The lowering of a declaration list carries every declared callable through with its name, its arity
and its lowered body, and the first emitted function of a name is the lowering of the first declared
callable of that name.

A callable is a `function` declaration or a `foreign` host boundary: the two lower identically, which
is exactly why the model runs one body on both sides of a host call and the substrate's own agreement
with that body is a separate, named premise.
-/
theorem lowered_of_declarations {program : Ir.Program} :
    ∀ (declarations : List Ir.Decl) (functions : List Target.Function),
      Compile.declarations program declarations = .ok functions →
      ∀ (name : String) (parameters : List Ir.Field) (result : Ir.Ty) (recursion : Ir.Recursion)
        (body : Ir.Expr),
        ((declarations.find? fun declaration => declaration.name == name)
              = some (.function name parameters result recursion body) ∨
          ∃ host, (declarations.find? fun declaration => declaration.name == name)
              = some (.foreign name host parameters result body)) →
        ∃ emitted, (functions.find? fun emitted => emitted.name == name) = some emitted ∧
          emitted.parameters = parameters.length ∧
            Compile.returnBody program body = .ok emitted.body
  | [], functions, _, name, _, _, _, _, found => by
      rcases found with found | ⟨_, found⟩ <;> simp at found
  | declaration :: rest, functions, compiled, name, parameters, result, recursion, body, found => by
      simp only [Compile.declarations] at compiled
      obtain ⟨head, headCompiled, more⟩ := bind_ok compiled
      simp only [List.find?_cons] at found
      cases matched : declaration.name == name with
      | true =>
        obtain ⟨emittedBody, headEq, bodyCompiled⟩ : ∃ emittedBody,
            head = some ⟨name, parameters.length, emittedBody⟩ ∧
              Compile.returnBody program body = .ok emittedBody := by
          rcases found with found | ⟨host, found⟩
          · rw [matched] at found
            dsimp only at found
            injection found with declarationEq
            subst declarationEq
            exact declaration_function headCompiled
          · rw [matched] at found
            dsimp only at found
            injection found with declarationEq
            subst declarationEq
            exact declaration_foreign headCompiled
        subst headEq
        simp only at more
        obtain ⟨tail, tailCompiled, shape⟩ := bind_ok more
        simp only [pure, Except.pure] at shape
        injection shape with functionsEq
        subst functionsEq
        refine ⟨⟨name, parameters.length, emittedBody⟩, ?_, rfl, bodyCompiled⟩
        simp only [List.find?_cons, beq_self_eq_true]
      | false =>
        rw [matched] at found
        dsimp only at found
        have different : ¬(declaration.name = name) := by simpa using matched
        cases head with
        | none =>
            simp only at more
            refine lowered_of_declarations rest functions more name parameters result recursion
              body ?_
            rcases found with found | ⟨host, found⟩
            · exact Or.inl found
            · exact Or.inr ⟨host, found⟩
        | some emittedHead =>
            simp only at more
            obtain ⟨tail, tailCompiled, shape⟩ := bind_ok more
            simp only [pure, Except.pure] at shape
            injection shape with functionsEq
            subst functionsEq
            have headName : emittedHead.name = declaration.name := by
              cases declaration with
              | enum _ _ =>
                  simp only [Compile.declaration, pure, Except.pure] at headCompiled
                  injection headCompiled with headEq
                  exact absurd headEq.symm (by simp)
              | record _ _ _ =>
                  simp only [Compile.declaration, pure, Except.pure] at headCompiled
                  injection headCompiled with headEq
                  exact absurd headEq.symm (by simp)
              | function declaredName _ _ _ _ =>
                  obtain ⟨_, headEq, _⟩ := declaration_function headCompiled
                  injection headEq with headEq
                  subst headEq
                  rfl
              | foreign declaredName _ _ _ _ =>
                  obtain ⟨_, headEq, _⟩ := declaration_foreign headCompiled
                  injection headEq with headEq
                  subst headEq
                  rfl
            obtain ⟨emitted, emittedFound, arity, bodyCompiled⟩ := by
              refine lowered_of_declarations rest tail tailCompiled name parameters result recursion
                body ?_
              rcases found with found | ⟨host, found⟩
              · exact Or.inl found
              · exact Or.inr ⟨host, found⟩
            refine ⟨emitted, ?_, arity, bodyCompiled⟩
            simp only [List.find?_cons]
            rw [show (emittedHead.name == name) = false from by
              simpa [headName] using different]
            dsimp only
            exact emittedFound

/-- A program the lowering admits satisfies the whole-program function premise. Inline lambda bodies
are discharged where their `Compile.body` result occurs, not from a second program registry. -/
theorem loweredProgram_of_compile {program : Ir.Program} {target : Target.Program}
    (compiled : Compile.program program = .ok target) : LoweredProgram program target := by
  refine ⟨?_⟩
  intro name parameters result recursion body declared
  simp only [Compile.program] at compiled
  obtain ⟨_, _, more⟩ := bind_ok compiled
  obtain ⟨functions, functionsCompiled, shape⟩ := bind_ok more
  simp only [pure, Except.pure] at shape
  injection shape with targetEq
  subst targetEq
  simp only [Ir.Program.function?, Ir.Program.find?] at declared
  rcases option_cases (program.declarations.find? fun declaration => declaration.name == name) with
    lookup | ⟨declaration, lookup⟩
  · rw [lookup] at declared
    simp at declared
  · rw [lookup] at declared
    cases declaration with
    | enum _ _ => simp at declared
    | record _ _ _ => simp at declared
    | function declaredName declaredParameters declaredResult declaredRecursion declaredBody =>
        simp only [Option.some.injEq, Prod.mk.injEq] at declared
        obtain ⟨parametersEq, resultEq, recursionEq, bodyEq⟩ := declared
        subst parametersEq
        subst resultEq
        subst recursionEq
        subst bodyEq
        have nameEq : declaredName = name := by
          have := List.find?_some lookup
          simpa [Ir.Decl.name] using this
        subst nameEq
        obtain ⟨emitted, emittedFound, arity, bodyCompiled⟩ :=
          lowered_of_declarations program.declarations functions functionsCompiled declaredName
            declaredParameters declaredResult declaredRecursion declaredBody (Or.inl lookup)
        exact ⟨emitted, emittedFound, arity, bodyCompiled⟩
    | foreign declaredName declaredHost declaredParameters declaredResult declaredReference =>
        simp only [Option.some.injEq, Prod.mk.injEq] at declared
        obtain ⟨parametersEq, resultEq, recursionEq, referenceEq⟩ := declared
        subst parametersEq
        subst resultEq
        subst recursionEq
        subst referenceEq
        have nameEq : declaredName = name := by
          have := List.find?_some lookup
          simpa [Ir.Decl.name] using this
        subst nameEq
        obtain ⟨emitted, emittedFound, arity, bodyCompiled⟩ :=
          lowered_of_declarations program.declarations functions functionsCompiled declaredName
            declaredParameters declaredResult .nonrecursive declaredReference
            (Or.inr ⟨declaredHost, lookup⟩)
        exact ⟨emitted, emittedFound, arity, bodyCompiled⟩

/-! ## Entering a declared function, and applying an inline closure -/

/--
The whole-program statement: for a program whose lowering is `target`, entering any declared function
on representing arguments refines entering it in the source, at every fuel.

Every hypothesis the per-operation theorems take is discharged here from `LoweredProgram`,
`RuntimeLaws` and `ListsFit` alone: the subexpression obligations by `everywhere`, the
readable-scrutinee obligation by `sourcePure_of_readable` and `targetStable_of_readable`, the key and
field refusals by `Compile.presentableKeys_iff`, the opcode laws by `Opcode.registry`, and the callee
obligation at lower fuel by `everywhereBody`.
-/
theorem entering {program : Ir.Program} {target : Target.Program} {runtime : Runtime}
    (lowered : LoweredProgram program target) (laws : RuntimeLaws runtime)
    (listsFit : ListsFit program) (fuel : Nat) (name : String)
    (parameters : List Ir.Field) (result : Ir.Ty) (recursion : Ir.Recursion) (body : Ir.Expr)
    (declared : program.function? name = some (parameters, result, recursion, body))
    (arguments : List Source.Value) (targets : List Value) (trace : Source.Trace)
    (state : Target.State) (heapValid : state.heap.WellFormed)
    (closuresValid : state.ClosuresWellFormed)
    (related : Relation.RepresentsList program state arguments targets)
    (traceRefines : Relation.RefinesTrace program state trace state.trace) :
    Relation.Refines program state
      (Source.enter program fuel trace name arguments)
      (Target.enter target runtime fuel state name targets) := by
  obtain ⟨emitted, found, arity, bodyCompiled⟩ :=
    lowered.functions name parameters result recursion body declared
  simp only [Source.enter, Target.enter, declared, found]
  by_cases matched : parameters.length = arguments.length
  · rw [if_pos matched]
    have lengths : emitted.parameters = targets.length := by
      rw [arity, matched, representsList_length arguments targets related]
    rw [bindArguments_exact targets emitted.parameters lengths]
    cases fuel with
    | zero =>
        exact refines_exhausted (Target.State.Extension.refl state heapValid) closuresValid
          traceRefines
    | succ remaining =>
        dsimp only
        have recorded := Target.State.record_extension state (.function name targets) heapValid
        refine refines_widen recorded ?_
        refine everywhereReturnBody lowered laws listsFit remaining body emitted.body bodyCompiled
          arguments.reverse targets.reverse (trace ++ [.function name arguments])
          (state.record (.function name targets)) ?_
        exact ⟨heapValid, closuresValid,
          Relation.RepresentsList.stable recorded arguments.reverse targets.reverse
            (represents_reverse arguments targets related),
          refinesTrace_append trace state.trace (.function name arguments) (.function name targets)
            (Relation.RefinesTrace.stable recorded trace state.trace traceRefines)
            ⟨rfl, Relation.RepresentsList.stable recorded arguments targets related⟩⟩
  · rw [if_neg matched]
    exact refines_fault

/--
The inline-closure capstone: the target function object at `ref` owns its exact code and compiled
body. Applying it reads its exact captured own properties, checks its payload, records one
application event, consumes one unit of fuel and enters the stored body with reversed arguments
above the captured scope. The only whole-program premise is the usual lowering of declared
functions used by that body.
-/
theorem applying {program : Ir.Program} {target : Target.Program} {runtime : Runtime}
    (lowered : LoweredProgram program target) (laws : RuntimeLaws runtime)
    (listsFit : ListsFit program) (fuel : Nat)
    (parameters : List Ir.Field) (body : Ir.Expr) (emittedBody : Target.Body)
    (compiledBody : Compile.body program body = .ok emittedBody)
    (captured : List Source.Value) (capturedImages : List Value)
    (arguments : List Source.Value) (targets : List Value) (trace : Source.Trace)
    (state : Target.State) (ref : RefId) (heapValid : state.heap.WellFormed)
    (closuresValid : state.ClosuresWellFormed)
    (closureFound :
      state.lookupClosure ref = some ⟨⟨parameters, body⟩, emittedBody, capturedImages⟩)
    (shape : Relation.HasOwnFields state.heap ref (Ir.closureEntries capturedImages))
    (capturedRelated : Relation.RepresentsList program state captured capturedImages)
    (related : Relation.RepresentsList program state arguments targets)
    (traceRefines : Relation.RefinesTrace program state trace state.trace) :
    Relation.Refines program state
      (Source.applyClosure program fuel trace captured parameters body arguments)
      (Target.invoke target runtime fuel state (.object ref) targets) := by
  refine invoke_refines ?_ heapValid closuresValid ?_ related traceRefines
  · intro smaller step inner emittedInner innerCompiled
    subst step
    exact everywhereBody lowered laws listsFit smaller inner emittedInner innerCompiled
  · unfold Relation.Represents
    exact ⟨ref, ⟨⟨parameters, body⟩, emittedBody, capturedImages⟩, rfl, closureFound, rfl,
      compiledBody, capturedRelated, shape⟩

end Preservation

end TSLean.LeanToTypeScript.Semantics
