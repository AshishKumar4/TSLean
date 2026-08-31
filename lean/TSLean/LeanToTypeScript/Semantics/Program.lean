import TSLean.LeanToTypeScript.Semantics.Preservation

/-!
# Whole-program preservation

`everywhere` closes the per-operation theorems into one statement over whole programs: every
expression the lowering admits refines its source, from every aligned configuration, at every fuel.
It discharges every hypothesis the per-operation theorems take — the subexpression obligations, the
readable-scrutinee obligation, the key and field refusals, and the callee obligation at lower fuel —
from one premise about the program and its lowering.
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
    (recursion : Option Nat) (body : Ir.Expr),
    program.function? name = some (parameters, result, recursion, body) →
    ∃ emitted, target.find? name = some emitted ∧ emitted.parameters = parameters.length ∧
      Compile.body program body = .ok emitted.body

/-- A lowered program has a lowered counterpart for every declared function. -/
theorem lowered_of_loweredProgram {program : Ir.Program} {target : Target.Program}
    (lowered : LoweredProgram program target) : Lowered program target := by
  intro name parameters result recursion body declared
  obtain ⟨emitted, found, arity, _⟩ :=
    lowered.functions name parameters result recursion body declared
  exact ⟨emitted, found, arity⟩

/-- Peels one `Except` bind, which is the shape every `Compile` clause has. -/
private theorem bind_ok {α β : Type} {value : Except Compile.Fault α}
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
        | absent => exact Or.inr ⟨_, rfl⟩
        | present _ => exact Or.inr ⟨_, rfl⟩
        | variant _ _ _ => exact Or.inr ⟨_, rfl⟩
        | closure _ _ _ => exact Or.inr ⟨_, rfl⟩
      · rw [run]
        exact Or.inr ⟨fault, rfl⟩

/-- Running the lowering of a readable scrutinee changes no state. -/
theorem targetStable_of_readable {program : Ir.Program} {target : Target.Program} {fuel : Nat} :
    ∀ (scrutinee : Ir.Expr) (emitted : Target.Expr),
      Compile.readableScrutinee scrutinee = true →
      Compile.expr program scrutinee = .ok emitted →
      StateStable target fuel emitted
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
      have inner : StateStable target fuel emittedSubject :=
        targetStable_of_readable subject emittedSubject readable subjectCompiled
      intro targetScope state produced next run
      simp only [Target.eval] at run
      cases subjectRun : Target.eval target fuel targetScope state emittedSubject with
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
theorem everywhereList_nil {program : Ir.Program} {target : Target.Program} {fuel : Nat} :
    EverywhereList program target fuel [] [] := by
  intro sourceScope targetScope trace state aligned
  simp only [Source.evalList, Target.evalList, Relation.RefinesList]
  exact ⟨Target.State.Extension.refl state aligned.heapValid, aligned.closuresValid,
    represents_nil, aligned.trace⟩

/-- An argument list is evaluated left to right, once each. -/
theorem everywhereList_cons {program : Ir.Program} {target : Target.Program} {fuel : Nat}
    {head : Ir.Expr} {emittedHead : Target.Expr} {rest : List Ir.Expr}
    {emittedRest : List Target.Expr}
    (headStep : Everywhere program target fuel head emittedHead)
    (restStep : EverywhereList program target fuel rest emittedRest) :
    EverywhereList program target fuel (head :: rest) (emittedHead :: emittedRest) := by
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
          obtain ⟨lastState, lastRun, lastExtension, lastClosuresValid, lastTrace⟩ :=
            refinesList_exhausted_inv
              (restRun ▸ restStep sourceScope targetScope next targetState nextAligned)
          rw [lastRun]
          simp only [Relation.RefinesList]
          exact ⟨extension.trans lastExtension, lastClosuresValid, lastTrace⟩
      | values values last =>
          obtain ⟨targets, lastState, lastRun, lastExtension, lastClosuresValid, listRelated,
            lastTrace⟩ :=
            refinesList_inv
              (restRun ▸ restStep sourceScope targetScope next targetState nextAligned)
          rw [lastRun]
          simp only [Relation.RefinesList]
          refine ⟨extension.trans lastExtension, lastClosuresValid, ?_, lastTrace⟩
          unfold Relation.RepresentsList
          exact ⟨image, targets, rfl,
            Relation.Represents.stable lastExtension produced image related, listRelated⟩

/-- The empty field list refines the empty property list. -/
theorem everywhereFields_nil {program : Ir.Program} {target : Target.Program} {fuel : Nat} :
    EverywhereFields program target fuel [] [] := by
  intro sourceScope targetScope trace state aligned
  simp only [Source.evalFields, Target.evalProperties, Relation.RefinesFields]
  refine ⟨Target.State.Extension.refl state aligned.heapValid, aligned.closuresValid, ?_,
    aligned.trace⟩
  unfold Relation.RepresentsFields
  rfl

/-- A field list is evaluated left to right, once each, keeping declaration order. -/
theorem everywhereFields_cons {program : Ir.Program} {target : Target.Program} {fuel : Nat}
    {name : String} {head : Ir.Expr} {emittedHead : Target.Expr}
    {rest : List (String × Ir.Expr)} {emittedRest : List (String × Target.Expr)}
    (headStep : Everywhere program target fuel head emittedHead)
    (restStep : EverywhereFields program target fuel rest emittedRest) :
    EverywhereFields program target fuel ((name, head) :: rest) ((name, emittedHead) :: emittedRest) := by
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
          obtain ⟨lastState, lastRun, lastExtension, lastClosuresValid, lastTrace⟩ :=
            refinesFields_exhausted_inv
              (restRun ▸ restStep sourceScope targetScope next targetState nextAligned)
          rw [lastRun]
          simp only [Relation.RefinesFields]
          exact ⟨extension.trans lastExtension, lastClosuresValid, lastTrace⟩
      | fields values last =>
          obtain ⟨entries, lastState, lastRun, lastExtension, lastClosuresValid, fieldsRelated,
            lastTrace⟩ :=
            refinesFields_inv
              (restRun ▸ restStep sourceScope targetScope next targetState nextAligned)
          rw [lastRun]
          simp only [Relation.RefinesFields]
          refine ⟨extension.trans lastExtension, lastClosuresValid, ?_, lastTrace⟩
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

/-! ## The whole-program theorem -/

mutual

/-- Every expression the lowering admits refines its source, from every aligned configuration. -/
theorem everywhere {program : Ir.Program} {target : Target.Program}
    (lowered : LoweredProgram program target) (fuel : Nat) :
    ∀ (expression : Ir.Expr) (emitted : Target.Expr),
      Compile.expr program expression = .ok emitted →
      Everywhere program target fuel expression emitted
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
  | .letBind name value body, emitted, compiled => by
      simp only [Compile.expr, throw, throwThe, MonadExceptOf.throw] at compiled
      exact absurd compiled (by simp)
  | .noneValue, emitted, compiled => by
      simp only [Compile.expr, pure, Except.pure] at compiled
      injection compiled with emittedEq
      subst emittedEq
      exact noneValue program target fuel
  | .someValue value, emitted, compiled => by
      simp only [Compile.expr] at compiled
      exact someValue program target fuel value emitted (everywhere lowered fuel value emitted compiled)
  | .boolNot operand, emitted, compiled => by
      simp only [Compile.expr] at compiled
      obtain ⟨emittedOperand, operandCompiled, shape⟩ := bind_ok compiled
      simp only [pure, Except.pure] at shape
      injection shape with emittedEq
      subst emittedEq
      exact boolNot program target fuel operand emittedOperand
        (everywhere lowered fuel operand emittedOperand operandCompiled)
  | .fieldGet subject field, emitted, compiled => by
      simp only [Compile.expr] at compiled
      obtain ⟨emittedSubject, subjectCompiled, shape⟩ := bind_ok compiled
      simp only [pure, Except.pure] at shape
      injection shape with emittedEq
      subst emittedEq
      exact fieldGet program target fuel subject field emittedSubject
        (everywhere lowered fuel subject emittedSubject subjectCompiled)
  | .boolAnd left right, emitted, compiled => by
      simp only [Compile.expr] at compiled
      obtain ⟨emittedLeft, leftCompiled, rest⟩ := bind_ok compiled
      obtain ⟨emittedRight, rightCompiled, shape⟩ := bind_ok rest
      simp only [pure, Except.pure] at shape
      injection shape with emittedEq
      subst emittedEq
      exact boolAnd program target fuel left right emittedLeft emittedRight
        (everywhere lowered fuel left emittedLeft leftCompiled)
        (everywhere lowered fuel right emittedRight rightCompiled)
  | .boolOr left right, emitted, compiled => by
      simp only [Compile.expr] at compiled
      obtain ⟨emittedLeft, leftCompiled, rest⟩ := bind_ok compiled
      obtain ⟨emittedRight, rightCompiled, shape⟩ := bind_ok rest
      simp only [pure, Except.pure] at shape
      injection shape with emittedEq
      subst emittedEq
      exact boolOr program target fuel left right emittedLeft emittedRight
        (everywhere lowered fuel left emittedLeft leftCompiled)
        (everywhere lowered fuel right emittedRight rightCompiled)
  | .ifThenElse condition consequent alternate, emitted, compiled => by
      simp only [Compile.expr] at compiled
      obtain ⟨emittedCondition, conditionCompiled, rest⟩ := bind_ok compiled
      obtain ⟨emittedConsequent, consequentCompiled, more⟩ := bind_ok rest
      obtain ⟨emittedAlternate, alternateCompiled, shape⟩ := bind_ok more
      simp only [pure, Except.pure] at shape
      injection shape with emittedEq
      subst emittedEq
      exact ifThenElse program target fuel condition consequent alternate emittedCondition
        emittedConsequent emittedAlternate
        (everywhere lowered fuel condition emittedCondition conditionCompiled)
        (everywhere lowered fuel consequent emittedConsequent consequentCompiled)
        (everywhere lowered fuel alternate emittedAlternate alternateCompiled)
  | .boolEquals left right, emitted, compiled => by
      simp only [Compile.expr] at compiled
      by_cases foldRight : right.isTrueLiteral = true
      · rw [if_pos foldRight] at compiled
        have rightEq := Ir.Expr.eq_of_isTrueLiteral foldRight
        subst rightEq
        exact (boolEquals program target fuel left (.boolLit true) emitted (.boolLit true)
          (everywhere lowered fuel left emitted compiled)
          (everywhere lowered fuel (.boolLit true) (.boolLit true) (by simp [Compile.expr, pure, Except.pure]))).2.1
      · rw [if_neg foldRight] at compiled
        by_cases foldLeft : left.isTrueLiteral = true
        · rw [if_pos foldLeft] at compiled
          have leftEq := Ir.Expr.eq_of_isTrueLiteral foldLeft
          subst leftEq
          exact (boolEquals program target fuel (.boolLit true) right (.boolLit true) emitted
            (everywhere lowered fuel (.boolLit true) (.boolLit true) (by simp [Compile.expr, pure, Except.pure]))
            (everywhere lowered fuel right emitted compiled)).2.2
        · rw [if_neg foldLeft] at compiled
          obtain ⟨emittedLeft, leftCompiled, rest⟩ := bind_ok compiled
          obtain ⟨emittedRight, rightCompiled, shape⟩ := bind_ok rest
          simp only [pure, Except.pure] at shape
          injection shape with emittedEq
          subst emittedEq
          exact (boolEquals program target fuel left right emittedLeft emittedRight
            (everywhere lowered fuel left emittedLeft leftCompiled)
            (everywhere lowered fuel right emittedRight rightCompiled)).1
  | .call function arguments, emitted, compiled => by
      simp only [Compile.expr] at compiled
      cases declared : program.function? function with
      | none => rw [declared] at compiled; simp [throw, throwThe, MonadExceptOf.throw] at compiled
      | some declaration =>
          rw [declared] at compiled
          dsimp only at compiled
          obtain ⟨emittedArguments, argumentsCompiled, shape⟩ := bind_ok compiled
          simp only [pure, Except.pure] at shape
          injection shape with emittedEq
          subst emittedEq
          refine call program target fuel function arguments emittedArguments
            (lowered_of_loweredProgram lowered)
            (everywhereList lowered fuel arguments emittedArguments argumentsCompiled) ?_
          intro smaller step
          intro name parameters result recursion body emittedFunction functionDeclared found
          obtain ⟨candidate, candidateFound, _, bodyCompiled⟩ :=
            lowered.functions name parameters result recursion body functionDeclared
          rw [candidateFound] at found
          injection found with functionEq
          subst step
          rw [functionEq] at bodyCompiled
          exact everywhereBody lowered smaller body emittedFunction.body bodyCompiled
  | .record type fields, emitted, compiled => by
      simp only [Compile.expr] at compiled
      cases declared : program.record? type with
      | none => rw [declared] at compiled; simp [throw, throwThe, MonadExceptOf.throw] at compiled
      | some declaredFields =>
          rw [declared] at compiled
          dsimp only at compiled
          by_cases mismatch : (fields.map Prod.fst) ≠ (declaredFields.map Ir.Field.name)
          · rw [if_pos mismatch] at compiled
            simp [throw, throwThe, MonadExceptOf.throw] at compiled
          · rw [if_neg mismatch] at compiled
            by_cases unpresentable : Compile.presentableKeys (fields.map Prod.fst) = false
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
                (everywhereFields lowered fuel fields emittedFields fieldsCompiled)
  | .variant type name arguments, emitted, compiled => by
      simp only [Compile.expr] at compiled
      cases declared : program.enum? type with
      | none => rw [declared] at compiled; simp [throw, throwThe, MonadExceptOf.throw] at compiled
      | some constructors =>
          rw [declared] at compiled
          dsimp only at compiled
          cases selected : Ir.constructor? constructors name with
          | none => rw [selected] at compiled; simp [throw, throwThe, MonadExceptOf.throw] at compiled
          | some constructor =>
              rw [selected] at compiled
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
                    obtain ⟨keys, distinct⟩ :=
                      Compile.presentableKeys_iff.mp (by simpa using unpresentable)
                    have notReserved : ∀ field ∈ constructor.fields, ¬field.name = "kind" := by
                      simpa using reserved
                    have lengths : emittedArguments.length = arguments.length :=
                      exprList_length arguments emittedArguments argumentsCompiled
                    have sameLength :
                        constructor.fields.length = emittedArguments.length :=
                      Decidable.byContradiction fun different => arity different
                    have fieldArity : constructor.fields.length = arguments.length := by
                      rw [sameLength, lengths]
                    have fieldKeys : ∀ field ∈ constructor.fields,
                        Ir.ValidKey field.name ∧ field.name ≠ "kind" := by
                      intro field member
                      exact ⟨keys field.name (List.mem_map_of_mem member),
                        notReserved field member⟩
                    have rows := variant program target fuel type name constructors constructor
                      arguments emittedArguments declared selected fieldKeys distinct fieldArity
                      lengths.symm
                      (everywhereList lowered fuel arguments emittedArguments argumentsCompiled)
                    by_cases nullary :
                        (Ir.allNullary constructors && constructor.fields.isEmpty) = true
                    · rw [if_pos nullary] at rest
                      simp only [pure, Except.pure] at rest
                      injection rest with emittedEq
                      subst emittedEq
                      refine rows.1 ?_
                      simp only [Bool.and_eq_true] at nullary
                      exact nullary.1
                    · rw [if_neg nullary] at rest
                      simp only [pure, Except.pure] at rest
                      injection rest with emittedEq
                      subst emittedEq
                      refine rows.2 ?_
                      cases allNullary : Ir.allNullary constructors with
                      | false => rfl
                      | true =>
                          refine absurd ?_ nullary
                          simp only [Bool.and_eq_true]
                          exact ⟨allNullary,
                            List.isEmpty_iff.mpr (nullary_fields allNullary selected)⟩
  | .matchOn type scrutinee cases, emitted, compiled => by
      simp only [Compile.expr] at compiled
      cases declared : program.enum? type with
      | none => rw [declared] at compiled; simp [throw, throwThe, MonadExceptOf.throw] at compiled
      | some constructors =>
          rw [declared] at compiled
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
              cases built : Compile.tagChain emittedScrutinee emittedCases with
              | none => rw [built] at shape; simp [throw, throwThe, MonadExceptOf.throw] at shape
              | some chain =>
                  rw [built] at shape
                  simp only [pure, Except.pure] at shape
                  injection shape with emittedEq
                  subst emittedEq
                  have readable : Compile.readableScrutinee scrutinee = true := by
                    simpa using computed
                  exact matchOn program target fuel type scrutinee cases emittedScrutinee
                    emittedCases chain constructors declared (by simpa using payload)
                    ⟨everywhere lowered fuel scrutinee emittedScrutinee scrutineeCompiled,
                      sourcePure_of_readable scrutinee readable,
                      targetStable_of_readable scrutinee emittedScrutinee readable scrutineeCompiled⟩
                    (everywhereCases lowered fuel cases emittedCases casesCompiled) built
  | .lambda parameters body, emitted, compiled => by
      simp only [Compile.expr] at compiled
      obtain ⟨emittedBody, bodyCompiled, shape⟩ := bind_ok compiled
      simp only [pure, Except.pure] at shape
      injection shape with emittedEq
      subst emittedEq
      exact lambda program target fuel parameters body emittedBody bodyCompiled
        (everywhereBody lowered fuel body emittedBody bodyCompiled)
  | .apply callee arguments, emitted, compiled => by
      obtain ⟨index, calleeEq⟩ := apply_callee_is_bound compiled
      subst calleeEq
      simp only [Compile.expr] at compiled
      obtain ⟨emittedArguments, argumentsCompiled, shape⟩ := bind_ok compiled
      simp only [pure, Except.pure] at shape
      injection shape with emittedEq
      subst emittedEq
      refine apply program target fuel index arguments emittedArguments
        (everywhereList lowered fuel arguments emittedArguments argumentsCompiled) ?_
      intro smaller step body emittedBody bodyCompiled
      subst step
      exact everywhereBody lowered smaller body emittedBody bodyCompiled
termination_by expression => (fuel, sizeOf expression, 0)

/-- Every function body the lowering admits refines its source. -/
theorem everywhereBody {program : Ir.Program} {target : Target.Program}
    (lowered : LoweredProgram program target) (fuel : Nat) :
    ∀ (body : Ir.Expr) (emitted : Target.Body),
      Compile.body program body = .ok emitted →
      EverywhereBody program target fuel body emitted
  | .letBind name value rest, emitted, compiled => by
      simp only [Compile.body] at compiled
      obtain ⟨emittedValue, valueCompiled, more⟩ := bind_ok compiled
      obtain ⟨emittedRest, restCompiled, shape⟩ := bind_ok more
      simp only [pure, Except.pure] at shape
      injection shape with emittedEq
      subst emittedEq
      exact letBind program target fuel name value rest emittedValue emittedRest
        (everywhere lowered fuel value emittedValue valueCompiled)
        (everywhereBody lowered fuel rest emittedRest restCompiled)
  | body, emitted, compiled => by
      rcases body_inversion compiled with
        ⟨name, value, rest, emittedValue, emittedRest, bodyEq, emittedEq, valueCompiled,
          restCompiled⟩ | ⟨emittedExpression, emittedEq, expressionCompiled⟩
      · subst bodyEq
        subst emittedEq
        exact letBind program target fuel name value rest emittedValue emittedRest
          (everywhere lowered fuel value emittedValue valueCompiled)
          (everywhereBody lowered fuel rest emittedRest restCompiled)
      · subst emittedEq
        intro sourceScope targetScope trace state aligned
        simp only [Target.evalBody]
        exact everywhere lowered fuel body emittedExpression expressionCompiled sourceScope
          targetScope trace state aligned
termination_by body => (fuel, sizeOf body, 1)

/-- Every argument list the lowering admits refines its source. -/
theorem everywhereList {program : Ir.Program} {target : Target.Program}
    (lowered : LoweredProgram program target) (fuel : Nat) :
    ∀ (expressions : List Ir.Expr) (emitted : List Target.Expr),
      Compile.exprList program expressions = .ok emitted →
      EverywhereList program target fuel expressions emitted
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
      exact everywhereList_cons (everywhere lowered fuel expression emittedHead headCompiled)
        (everywhereList lowered fuel rest emittedRest restCompiled)
termination_by expressions => (fuel, sizeOf expressions, 0)

/-- Every field list the lowering admits refines its source. -/
theorem everywhereFields {program : Ir.Program} {target : Target.Program}
    (lowered : LoweredProgram program target) (fuel : Nat) :
    ∀ (fields : List (String × Ir.Expr)) (emitted : List (String × Target.Expr)),
      Compile.exprFields program fields = .ok emitted →
      EverywhereFields program target fuel fields emitted
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
      exact everywhereFields_cons (everywhere lowered fuel expression emittedHead headCompiled)
        (everywhereFields lowered fuel rest emittedRest restCompiled)
termination_by fields => (fuel, sizeOf fields, 0)

/-- Every match arm the lowering admits refines its source. -/
theorem everywhereCases {program : Ir.Program} {target : Target.Program}
    (lowered : LoweredProgram program target) (fuel : Nat) :
    ∀ (cases : List (String × Ir.Expr)) (emitted : List (String × Target.Expr)),
      Compile.exprCases program cases = .ok emitted →
      EverywhereCases program target fuel cases emitted
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
        everywhere lowered fuel arm emittedArm armCompiled,
        everywhereCases lowered fuel rest emittedRest restCompiled⟩
termination_by cases => (fuel, sizeOf cases, 0)

end

/-! ## The lowered-program premise, derived -/

/-- Lowering a function declaration yields an emitted function with that name, arity and body. -/
theorem declaration_function {program : Ir.Program} {name : String} {parameters : List Ir.Field}
    {result : Ir.Ty} {recursion : Option Nat} {body : Ir.Expr} {emitted : Option Target.Function}
    (compiled : Compile.declaration program (.function name parameters result recursion body)
      = .ok emitted) :
    ∃ emittedBody, emitted = some ⟨name, parameters.length, emittedBody⟩ ∧
      Compile.body program body = .ok emittedBody := by
  simp only [Compile.declaration] at compiled
  obtain ⟨emittedBody, bodyCompiled, shape⟩ := bind_ok compiled
  simp only [pure, Except.pure] at shape
  injection shape with emittedEq
  exact ⟨emittedBody, emittedEq.symm, bodyCompiled⟩

/--
The lowering of a declaration list carries every declared function through with its name, its arity
and its lowered body, and the first emitted function of a name is the lowering of the first declared
function of that name.
-/
theorem lowered_of_declarations {program : Ir.Program} :
    ∀ (declarations : List Ir.Decl) (functions : List Target.Function),
      Compile.declarations program declarations = .ok functions →
      ∀ (name : String) (parameters : List Ir.Field) (result : Ir.Ty) (recursion : Option Nat)
        (body : Ir.Expr),
        (declarations.find? fun declaration => declaration.name == name)
            = some (.function name parameters result recursion body) →
        ∃ emitted, (functions.find? fun emitted => emitted.name == name) = some emitted ∧
          emitted.parameters = parameters.length ∧ Compile.body program body = .ok emitted.body
  | [], functions, _, name, _, _, _, _, found => by simp at found
  | declaration :: rest, functions, compiled, name, parameters, result, recursion, body, found => by
      simp only [Compile.declarations] at compiled
      obtain ⟨head, headCompiled, more⟩ := bind_ok compiled
      simp only [List.find?_cons] at found
      cases matched : declaration.name == name with
      | true =>
        rw [matched] at found
        dsimp only at found
        injection found with declarationEq
        subst declarationEq
        obtain ⟨emittedBody, headEq, bodyCompiled⟩ := declaration_function headCompiled
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
            exact lowered_of_declarations rest functions more name parameters result recursion body
              found
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
              | record _ _ =>
                  simp only [Compile.declaration, pure, Except.pure] at headCompiled
                  injection headCompiled with headEq
                  exact absurd headEq.symm (by simp)
              | function declaredName _ _ _ _ =>
                  obtain ⟨_, headEq, _⟩ := declaration_function headCompiled
                  injection headEq with headEq
                  subst headEq
                  rfl
            obtain ⟨emitted, emittedFound, arity, bodyCompiled⟩ :=
              lowered_of_declarations rest tail tailCompiled name parameters result recursion body
                found
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
  cases lookup : program.declarations.find? fun declaration => declaration.name == name with
  | none => rw [lookup] at declared; simp at declared
  | some declaration =>
      rw [lookup] at declared
      cases declaration with
      | enum _ _ => simp at declared
      | record _ _ => simp at declared
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
              declaredParameters declaredResult declaredRecursion declaredBody lookup
          exact ⟨emitted, emittedFound, arity, bodyCompiled⟩

/-! ## Entering a declared function, and applying an inline closure -/


/--
The whole-program statement: for a program whose lowering is `target`, entering any declared function
on representing arguments refines entering it in the source, at every fuel.

Every hypothesis the per-operation theorems take is discharged here from `LoweredProgram` alone: the
subexpression obligations by `everywhere`, the readable-scrutinee obligation by
`sourcePure_of_readable` and `targetStable_of_readable`, the key and field refusals by
`Compile.presentableKeys_iff`, and the callee obligation at lower fuel by `everywhereBody`.
-/
theorem entering {program : Ir.Program} {target : Target.Program}
    (lowered : LoweredProgram program target) (fuel : Nat) (name : String)
    (parameters : List Ir.Field) (result : Ir.Ty) (recursion : Option Nat) (body : Ir.Expr)
    (declared : program.function? name = some (parameters, result, recursion, body))
    (arguments : List Source.Value) (targets : List Value) (trace : Source.Trace)
    (state : Target.State) (heapValid : state.heap.WellFormed)
    (closuresValid : state.ClosuresWellFormed)
    (related : Relation.RepresentsList program state arguments targets)
    (traceRefines : Relation.RefinesTrace program state trace state.trace) :
    Relation.Refines program state
      (Source.enter program fuel trace name arguments)
      (Target.enter target fuel state name targets) := by
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
        exact refines_exhausted (Target.State.Extension.refl state heapValid) closuresValid traceRefines
    | succ remaining =>
        dsimp only
        have recorded := Target.State.record_extension state (.function name targets) heapValid
        refine refines_widen recorded ?_
        refine everywhereBody lowered remaining body emitted.body bodyCompiled arguments.reverse
          targets.reverse (trace ++ [.function name arguments])
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
theorem applying {program : Ir.Program} {target : Target.Program}
    (lowered : LoweredProgram program target) (fuel : Nat)
    (parameters : List Ir.Field) (body : Ir.Expr) (emittedBody : Target.Body)
    (compiledBody : Compile.body program body = .ok emittedBody)
    (captured : List Source.Value) (capturedImages : List Value)
    (arguments : List Source.Value) (targets : List Value) (trace : Source.Trace)
    (state : Target.State) (ref : RefId) (heapValid : state.heap.WellFormed)
    (closuresValid : state.ClosuresWellFormed)
    (closureFound : state.lookupClosure ref = some ⟨⟨parameters, body⟩, emittedBody, capturedImages⟩)
    (shape : Relation.HasOwnFields state.heap ref (Ir.closureEntries capturedImages))
    (capturedRelated : Relation.RepresentsList program state captured capturedImages)
    (related : Relation.RepresentsList program state arguments targets)
    (traceRefines : Relation.RefinesTrace program state trace state.trace) :
    Relation.Refines program state
      (Source.applyClosure program fuel trace captured parameters body arguments)
      (Target.invoke target fuel state (.object ref) targets) := by
  simp only [Target.invoke, closureFound, Closure.read_captured_all shape]
  simp only [if_true]
  unfold Source.applyClosure
  by_cases arity : parameters.length = arguments.length
  · rw [if_pos arity]
    have targetArity : parameters.length = targets.length := by
      rw [arity, representsList_length arguments targets related]
    rw [bindArguments_exact targets parameters.length targetArity]
    cases fuel with
    | zero =>
        exact refines_exhausted (Target.State.Extension.refl state heapValid) closuresValid
          traceRefines
    | succ remaining =>
        dsimp only
        have recorded := Target.State.record_extension state
          (.application ⟨parameters, body⟩ targets) heapValid
        refine refines_widen recorded ?_
        refine everywhereBody lowered remaining body emittedBody compiledBody
          (arguments.reverse ++ captured) (targets.reverse ++ capturedImages)
          (trace ++ [.application ⟨parameters, body⟩ arguments])
          (state.record (.application ⟨parameters, body⟩ targets)) ?_
        refine ⟨heapValid, closuresValid, ?_, ?_⟩
        · exact represents_append arguments.reverse targets.reverse captured capturedImages
            (Relation.RepresentsList.stable recorded arguments.reverse targets.reverse
              (represents_reverse arguments targets related))
            (Relation.RepresentsList.stable recorded captured capturedImages capturedRelated)
        · exact refinesTrace_append trace state.trace
            (.application ⟨parameters, body⟩ arguments)
            (.application ⟨parameters, body⟩ targets)
            (Relation.RefinesTrace.stable recorded trace state.trace traceRefines)
            ⟨rfl, Relation.RepresentsList.stable recorded arguments targets related⟩
  · rw [if_neg arity]
    exact refines_fault

end Preservation

end TSLean.LeanToTypeScript.Semantics
