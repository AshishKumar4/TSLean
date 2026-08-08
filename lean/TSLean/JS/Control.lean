import TSLean.JS.Environment

namespace TSLean.JS

namespace Control

/-- Catches only JavaScript throw completion. -/
def tryCatch (action : JSM P α) (handler : Value → JSM P α) : JSM P α := fun machine =>
  match action machine with
  | .done (.thrown value) next => handler value next
  | other => other

/-- Catch composition preserves complete machine validity. -/
theorem tryCatch_preservesWellFormed (action : JSM P α) (handler : Value → JSM P α)
    (actionPreserves : JSM.PreservesWellFormed action)
    (handlerPreserves : ∀ value, JSM.PreservesWellFormed (handler value)) :
    JSM.PreservesWellFormed (tryCatch action handler) := by
  intro machine valid
  unfold tryCatch
  cases result : action machine with
  | done completion next =>
      have first := actionPreserves machine valid
      rw [result] at first
      cases completion with
      | thrown value =>
          have second := handlerPreserves value next first.1
          cases handlerResult : handler value next with
          | done completion final | exhausted final | fault fault final =>
              rw [handlerResult] at second
              simp only [handlerResult]
              exact ⟨second.1, Machine.continuesFrom_trans _ _ _ first.2 second.2⟩
      | normal value | returned value | «break» label | «continue» label => exact first
  | exhausted next | fault fault next => simpa [result] using actionPreserves machine valid

/-- Catch preserves normal-result and abrupt-value validity. The caught value is supplied to the
handler together with the validity established by the action. -/
theorem tryCatch_preservesResults (action : JSM P α) (handler : Value → JSM P α)
    (actionPreserves : JSM.PreservesResults normalValid action)
    (handlerPreserves : ∀ value machine, machine.WellFormed →
      machine.heap.valueValid value = true →
      (handler value machine).MachinePreserved machine ∧
        (handler value machine).CompletionValuesValid normalValid) :
    JSM.PreservesResults normalValid (tryCatch action handler) := by
  constructor
  · intro machine valid
    unfold tryCatch
    cases result : action machine with
    | done completion next =>
        have firstMachine := actionPreserves.1 machine valid
        have firstValue := actionPreserves.2 machine valid
        rw [result] at firstMachine firstValue
        cases completion with
        | thrown value =>
            have second := (handlerPreserves value next firstMachine.1 firstValue).1
            cases handlerResult : handler value next with
            | done completion final | exhausted final | fault fault final =>
                rw [handlerResult] at second
                simp only [handlerResult]
                exact ⟨second.1,
                  Machine.continuesFrom_trans _ _ _ firstMachine.2 second.2⟩
        | normal value | returned value | «break» label | «continue» label => exact firstMachine
    | exhausted next | fault fault next => simpa [result] using actionPreserves.1 machine valid
  · intro machine valid
    unfold tryCatch
    cases result : action machine with
    | done completion next =>
        have machinePreserved := actionPreserves.1 machine valid
        have valuesValid := actionPreserves.2 machine valid
        rw [result] at machinePreserved valuesValid
        cases completion with
        | thrown value =>
            exact (handlerPreserves value next machinePreserved.1 valuesValid).2
        | normal value | returned value | «break» label | «continue» label => exact valuesValid
    | exhausted next | fault fault next => trivial

/-- Runs finalization after any JavaScript completion with exact override semantics. -/
def tryFinally (action : JSM P α) (finalizer : JSM P Unit) : JSM P α := fun machine =>
  match action machine with
  | .done prior next =>
      match finalizer next with
      | .done finalCompletion finalMachine =>
          .done (Completion.finallyOverride prior finalCompletion) finalMachine
      | .exhausted finalMachine => .exhausted finalMachine
      | .fault fault finalMachine => .fault fault finalMachine
  | .exhausted next => .exhausted next
  | .fault fault next => .fault fault next

/-- Finally composition preserves complete machine validity. -/
theorem tryFinally_preservesWellFormed (action : JSM P α) (finalizer : JSM P Unit)
    (actionPreserves : JSM.PreservesWellFormed action)
    (finalizerPreserves : JSM.PreservesWellFormed finalizer) :
    JSM.PreservesWellFormed (tryFinally action finalizer) := by
  intro machine valid
  unfold tryFinally
  cases result : action machine with
  | done completion next =>
      have first := actionPreserves machine valid
      rw [result] at first
      cases finalResult : finalizer next with
      | done finalCompletion finalMachine | exhausted finalMachine | fault fault finalMachine =>
          have second := finalizerPreserves next first.1
          rw [finalResult] at second
          simp only [finalResult]
          exact ⟨second.1, Machine.continuesFrom_trans _ _ _ first.2 second.2⟩
  | exhausted next | fault fault next => simpa [result] using actionPreserves machine valid

/-- Finally preserves completion values when normal-result validity is stable under execution
continuity. Abrupt finalizer values override, while a normal finalizer retains the prior value. -/
theorem tryFinally_preservesResults (action : JSM P α) (finalizer : JSM P Unit)
    (actionPreserves : JSM.PreservesResults normalValid action)
    (finalizerPreserves : JSM.PreservesResults (fun _ _ => True) finalizer)
    (normalValidContinues : ∀ value first final, first.ContinuesFrom final →
      normalValid value first → normalValid value final) :
    JSM.PreservesResults normalValid (tryFinally action finalizer) := by
  refine ⟨tryFinally_preservesWellFormed action finalizer actionPreserves.1
    finalizerPreserves.1, ?_⟩
  intro machine valid
  unfold tryFinally
  cases actionResult : action machine with
  | done prior next =>
      have firstMachine := actionPreserves.1 machine valid
      have firstValue := actionPreserves.2 machine valid
      rw [actionResult] at firstMachine firstValue
      cases finalResult : finalizer next with
      | done finalCompletion final =>
          have secondMachine := finalizerPreserves.1 next firstMachine.1
          have secondValue := finalizerPreserves.2 next firstMachine.1
          rw [finalResult] at secondMachine secondValue
          simp only [finalResult]
          cases finalCompletion with
          | normal unitResult =>
              cases unitResult
              cases prior with
              | normal value => exact normalValidContinues value next final secondMachine.2 firstValue
              | returned value | thrown value =>
                  exact Heap.ContinuesFrom.preserves_valueValid secondMachine.2.1 value firstValue
              | «break» label | «continue» label => trivial
          | returned value | thrown value => exact secondValue
          | «break» label | «continue» label => trivial
      | exhausted final | fault fault final =>
          simp only [actionResult, finalResult, RunResult.CompletionValuesValid]
  | exhausted next | fault fault next => trivial

/-- Catch is evaluated before finally, matching ECMAScript try/catch/finally order. -/
def tryCatchFinally (action : JSM P α) (handler : Value → JSM P α)
    (finalizer : JSM P Unit) : JSM P α :=
  tryFinally (tryCatch action handler) finalizer

/-- Try/catch/finally preserves validity when each participating action does. -/
theorem tryCatchFinally_preservesWellFormed (action : JSM P α) (handler : Value → JSM P α)
    (finalizer : JSM P Unit) (actionPreserves : JSM.PreservesWellFormed action)
    (handlerPreserves : ∀ value, JSM.PreservesWellFormed (handler value))
    (finalizerPreserves : JSM.PreservesWellFormed finalizer) :
    JSM.PreservesWellFormed (tryCatchFinally action handler finalizer) :=
  tryFinally_preservesWellFormed (tryCatch action handler) finalizer
    (tryCatch_preservesWellFormed action handler actionPreserves handlerPreserves)
    finalizerPreserves

/-- Try/catch/finally composes machine, normal-result, and abrupt-value preservation. -/
theorem tryCatchFinally_preservesResults (action : JSM P α) (handler : Value → JSM P α)
    (finalizer : JSM P Unit) (actionPreserves : JSM.PreservesResults normalValid action)
    (handlerPreserves : ∀ value machine, machine.WellFormed →
      machine.heap.valueValid value = true →
      (handler value machine).MachinePreserved machine ∧
        (handler value machine).CompletionValuesValid normalValid)
    (finalizerPreserves : JSM.PreservesResults (fun _ _ => True) finalizer)
    (normalValidContinues : ∀ value first final, first.ContinuesFrom final →
      normalValid value first → normalValid value final) :
    JSM.PreservesResults normalValid (tryCatchFinally action handler finalizer) :=
  tryFinally_preservesResults (tryCatch action handler) finalizer
    (tryCatch_preservesResults action handler actionPreserves handlerPreserves)
    finalizerPreserves normalValidContinues

/-- Consumes only an unlabeled break produced by a switch body. -/
def handleSwitchBreak (action : JSM P Unit) : JSM P Unit := fun machine =>
  match action machine with
  | .done (.break none) next => .done (.normal ()) next
  | other => other

/-- Switch-local break handling preserves the action's final machine and continuity. -/
theorem handleSwitchBreak_preservesWellFormed (action : JSM P Unit)
    (actionPreserves : JSM.PreservesWellFormed action) :
    JSM.PreservesWellFormed (handleSwitchBreak action) := by
  intro machine valid
  unfold handleSwitchBreak
  cases result : action machine with
  | done completion next =>
      have preserved := actionPreserves machine valid
      rw [result] at preserved
      cases completion with
      | «break» actual => cases actual <;> simpa [result] using preserved
      | normal value | returned value | thrown value | «continue» value =>
          simpa [result] using preserved
  | exhausted next | fault fault next => simpa [result] using actionPreserves machine valid

/-- Switch-local break handling preserves all completion values. -/
theorem handleSwitchBreak_preservesResults (action : JSM P Unit)
    (actionPreserves : JSM.PreservesResults (fun _ _ => True) action) :
    JSM.PreservesResults (fun _ _ => True) (handleSwitchBreak action) := by
  refine ⟨handleSwitchBreak_preservesWellFormed action actionPreserves.1, ?_⟩
  intro machine valid
  unfold handleSwitchBreak
  cases result : action machine with
  | done completion next =>
      have valuesValid := actionPreserves.2 machine valid
      rw [result] at valuesValid
      cases completion with
      | returned value | thrown value => simpa [result] using valuesValid
      | «break» actual => cases actual <;> simp [result, RunResult.CompletionValuesValid]
      | normal value | «continue» value => simp [result, RunResult.CompletionValuesValid]
  | exhausted next | fault fault next => trivial

/-- Consumes a break whose label exactly matches the supplied statement label. -/
def handleLabeledBreak (label : JSString) (action : JSM P Unit) : JSM P Unit := fun machine =>
  match action machine with
  | .done (.break (some actual)) next =>
      if actual = label then .done (.normal ()) next else .done (.break (some actual)) next
  | other => other

/-- Labeled break handling preserves the action's final machine and continuity. -/
theorem handleLabeledBreak_preservesWellFormed (label : JSString) (action : JSM P Unit)
    (actionPreserves : JSM.PreservesWellFormed action) :
    JSM.PreservesWellFormed (handleLabeledBreak label action) := by
  intro machine valid
  unfold handleLabeledBreak
  cases result : action machine with
  | done completion next =>
      have preserved := actionPreserves machine valid
      rw [result] at preserved
      cases completion with
      | «break» actual =>
          cases actual with
          | none => simpa [result] using preserved
          | some actual =>
              by_cases same : actual = label <;> simpa [result, same] using preserved
      | normal value | returned value | thrown value | «continue» value =>
          simpa [result] using preserved
  | exhausted next | fault fault next => simpa [result] using actionPreserves machine valid

/-- Labeled break handling preserves all completion values. -/
theorem handleLabeledBreak_preservesResults (label : JSString) (action : JSM P Unit)
    (actionPreserves : JSM.PreservesResults (fun _ _ => True) action) :
    JSM.PreservesResults (fun _ _ => True) (handleLabeledBreak label action) := by
  refine ⟨handleLabeledBreak_preservesWellFormed label action actionPreserves.1, ?_⟩
  intro machine valid
  unfold handleLabeledBreak
  cases result : action machine with
  | done completion next =>
      have valuesValid := actionPreserves.2 machine valid
      rw [result] at valuesValid
      cases completion with
      | «break» actual =>
          cases actual with
          | none => simpa [result] using valuesValid
          | some actual =>
              by_cases same : actual = label <;> simp [result, same, RunResult.CompletionValuesValid]
      | returned value | thrown value => simpa [result] using valuesValid
      | normal value | «continue» value => simp [result, RunResult.CompletionValuesValid]
  | exhausted next | fault fault next => trivial

private inductive LoopDisposition where
  | next
  | stop

private def classifyLoop (label : Option JSString) : Completion Unit → Completion LoopDisposition
  | .normal () => .normal .next
  | .break actual => if actual = none || actual = label then .normal .stop else .break actual
  | .continue actual => if actual = none || actual = label then .normal .next else .continue actual
  | .returned value => .returned value
  | .thrown value => .thrown value

/-- Handles loop-local break and continue, preserving nonmatching labeled transfers. -/
def handleLoopControl (label : Option JSString) (action : JSM P Unit) : JSM P Bool := fun machine =>
  match action machine with
  | .done completion next =>
      match classifyLoop label completion with
      | .normal .next => .done (.normal true) next
      | .normal .stop => .done (.normal false) next
      | .returned value => .done (.returned value) next
      | .thrown value => .done (.thrown value) next
      | .break actual => .done (.break actual) next
      | .continue actual => .done (.continue actual) next
  | .exhausted next => .exhausted next
  | .fault fault next => .fault fault next

/-- Loop-control classification preserves the body's final machine and continuity. -/
theorem handleLoopControl_preservesWellFormed (label : Option JSString) (action : JSM P Unit)
    (actionPreserves : JSM.PreservesWellFormed action) :
    JSM.PreservesWellFormed (handleLoopControl label action) := by
  intro machine valid
  unfold handleLoopControl
  cases result : action machine with
  | done completion next =>
      have preserved := actionPreserves machine valid
      rw [result] at preserved
      cases completion with
      | normal unitResult => cases unitResult; simpa [result, classifyLoop] using preserved
      | returned value | thrown value => simpa [result, classifyLoop] using preserved
      | «break» actual | «continue» actual =>
          simp only [result, classifyLoop]
          split <;> exact preserved
  | exhausted next | fault fault next => simpa [result] using actionPreserves machine valid

/-- Loop-control classification preserves all abrupt values and validates its Boolean result. -/
theorem handleLoopControl_preservesResults (label : Option JSString) (action : JSM P Unit)
    (actionPreserves : JSM.PreservesResults (fun _ _ => True) action) :
    JSM.PreservesResults (fun _ _ => True) (handleLoopControl label action) := by
  refine ⟨handleLoopControl_preservesWellFormed label action actionPreserves.1, ?_⟩
  intro machine valid
  unfold handleLoopControl
  cases result : action machine with
  | done completion next =>
      have valuesValid := actionPreserves.2 machine valid
      rw [result] at valuesValid
      cases completion with
      | returned value | thrown value => simpa [result, classifyLoop] using valuesValid
      | normal unitResult =>
          cases unitResult
          simp [result, classifyLoop, RunResult.CompletionValuesValid]
      | «break» actual | «continue» actual =>
          by_cases handled : actual = none ∨ actual = label <;>
            simp [result, classifyLoop, handled, RunResult.CompletionValuesValid]
  | exhausted next | fault fault next => trivial

private def whileLoopAux (label : Option JSString) (condition : JSM P Bool)
    (body : JSM P Unit) : Nat → JSM P Unit
  | 0 => fun machine => .exhausted machine
  | remaining + 1 => fun machine =>
      match JSM.consumeFuel machine with
      | .done (.normal ()) fueled =>
          match condition fueled with
          | .done (.normal false) next => .done (.normal ()) next
          | .done (.normal true) next =>
              match handleLoopControl label body next with
              | .done (.normal false) afterBody => .done (.normal ()) afterBody
              | .done (.normal true) afterBody => whileLoopAux label condition body remaining afterBody
              | .done (.returned value) afterBody => .done (.returned value) afterBody
              | .done (.thrown value) afterBody => .done (.thrown value) afterBody
              | .done (.break actual) afterBody => .done (.break actual) afterBody
              | .done (.continue actual) afterBody => .done (.continue actual) afterBody
              | .exhausted afterBody => .exhausted afterBody
              | .fault fault afterBody => .fault fault afterBody
          | .done (.returned value) next => .done (.returned value) next
          | .done (.thrown value) next => .done (.thrown value) next
          | .done (.break actual) next => .done (.break actual) next
          | .done (.continue actual) next => .done (.continue actual) next
          | .exhausted next => .exhausted next
          | .fault fault next => .fault fault next
      | .exhausted next => .exhausted next
      | .fault fault next => .fault fault next
      | .done completion next => .done (completion.cast id) next

private theorem whileLoopAux_preservesResults (label : Option JSString) (condition : JSM P Bool)
    (body : JSM P Unit) (conditionPreserves : JSM.PreservesResults (fun _ _ => True) condition)
    (bodyPreserves : JSM.PreservesResults (fun _ _ => True) body) (remaining : Nat) :
    JSM.PreservesResults (fun _ _ => True) (whileLoopAux label condition body remaining) := by
  induction remaining with
  | zero =>
      constructor
      · intro machine valid
        exact ⟨valid, machine.continuesFrom_refl⟩
      · intro machine valid
        trivial
  | succ remaining ih =>
      constructor
      · intro machine valid
        unfold whileLoopAux
        cases fuelResult : JSM.consumeFuel machine with
        | exhausted fueled | fault fault fueled =>
            simpa [fuelResult] using JSM.consumeFuel_preservesWellFormed machine valid
        | done fuelCompletion fueled =>
            have fuelMachine := JSM.consumeFuel_preservesWellFormed machine valid
            rw [fuelResult] at fuelMachine
            cases fuelCompletion with
            | normal unitResult =>
                cases unitResult
                cases conditionResult : condition fueled with
                | exhausted next | fault fault next =>
                    have conditionMachine := conditionPreserves.1 fueled fuelMachine.1
                    rw [conditionResult] at conditionMachine
                    simp only [conditionResult]
                    exact RunResult.MachinePreserved.trans fuelMachine.2 conditionMachine
                | done conditionCompletion next =>
                    have conditionMachine := conditionPreserves.1 fueled fuelMachine.1
                    rw [conditionResult] at conditionMachine
                    simp only [conditionResult]
                    have throughCondition := Machine.continuesFrom_trans _ _ _
                      fuelMachine.2 conditionMachine.2
                    cases conditionCompletion with
                    | normal test =>
                        cases test with
                        | false => exact ⟨conditionMachine.1, throughCondition⟩
                        | true =>
                            cases bodyResult : handleLoopControl label body next with
                            | exhausted afterBody | fault fault afterBody =>
                                have bodyMachine := handleLoopControl_preservesWellFormed label body
                                  bodyPreserves.1 next conditionMachine.1
                                rw [bodyResult] at bodyMachine
                                simp only [bodyResult]
                                exact RunResult.MachinePreserved.trans throughCondition bodyMachine
                            | done bodyCompletion afterBody =>
                                have bodyMachine := handleLoopControl_preservesWellFormed label body
                                  bodyPreserves.1 next conditionMachine.1
                                rw [bodyResult] at bodyMachine
                                simp only [bodyResult]
                                have throughBody := Machine.continuesFrom_trans _ _ _
                                  throughCondition bodyMachine.2
                                cases bodyCompletion with
                                | normal keepGoing =>
                                    cases keepGoing with
                                    | false => exact ⟨bodyMachine.1, throughBody⟩
                                    | true =>
                                        exact RunResult.MachinePreserved.trans throughBody
                                          (ih.1 afterBody bodyMachine.1)
                                | returned value | thrown value | «break» value | «continue» value =>
                                    exact ⟨bodyMachine.1, throughBody⟩
                    | returned value | thrown value | «break» value | «continue» value =>
                        exact ⟨conditionMachine.1, throughCondition⟩
            | returned value | thrown value | «break» value | «continue» value =>
                simpa [fuelResult] using fuelMachine
      · intro machine valid
        unfold whileLoopAux
        cases fuelResult : JSM.consumeFuel machine with
        | exhausted fueled | fault fault fueled => trivial
        | done fuelCompletion fueled =>
            have fuelMachine := JSM.consumeFuel_preservesWellFormed machine valid
            rw [fuelResult] at fuelMachine
            cases fuelCompletion with
            | normal unitResult =>
                cases unitResult
                cases conditionResult : condition fueled with
                | exhausted next | fault fault next =>
                    simp [conditionResult, RunResult.CompletionValuesValid]
                | done conditionCompletion next =>
                    have conditionMachine := conditionPreserves.1 fueled fuelMachine.1
                    have conditionValue := conditionPreserves.2 fueled fuelMachine.1
                    rw [conditionResult] at conditionMachine conditionValue
                    simp only [conditionResult]
                    cases conditionCompletion with
                    | normal test =>
                        cases test with
                        | false => trivial
                        | true =>
                            cases bodyResult : handleLoopControl label body next with
                            | exhausted afterBody | fault fault afterBody =>
                                simp [bodyResult, RunResult.CompletionValuesValid]
                            | done bodyCompletion afterBody =>
                                have bodyMachine := (handleLoopControl_preservesResults label body
                                  bodyPreserves).1 next conditionMachine.1
                                have bodyValue := (handleLoopControl_preservesResults label body
                                  bodyPreserves).2 next conditionMachine.1
                                rw [bodyResult] at bodyMachine bodyValue
                                simp only [bodyResult]
                                cases bodyCompletion with
                                | normal keepGoing =>
                                    cases keepGoing with
                                    | false => trivial
                                    | true => exact ih.2 afterBody bodyMachine.1
                                | returned value | thrown value => exact bodyValue
                                | «break» value | «continue» value => trivial
                    | returned value | thrown value => exact conditionValue
                    | «break» value | «continue» value => trivial
            | returned value | thrown value =>
                have fuelValue := JSM.consumeFuel_preservesResults.2 machine valid
                rw [fuelResult] at fuelValue
                exact fuelValue
            | «break» value | «continue» value => trivial

/-- Fuel-bounded while execution. Each condition check consumes one unit of machine fuel. -/
def whileLoop (condition : JSM P Bool) (body : JSM P Unit)
    (label : Option JSString := none) : JSM P Unit := fun machine =>
  whileLoopAux label condition body machine.fuel machine

/-- A fuel-bounded loop preserves validity and execution continuity on every completion, fault,
and exhaustion outcome. -/
theorem whileLoop_preservesResults (condition : JSM P Bool) (body : JSM P Unit)
    (conditionPreserves : JSM.PreservesResults (fun _ _ => True) condition)
    (bodyPreserves : JSM.PreservesResults (fun _ _ => True) body)
    (label : Option JSString := none) :
    JSM.PreservesResults (fun _ _ => True) (whileLoop condition body label) := by
  constructor
  · intro machine valid
    exact (whileLoopAux_preservesResults label condition body conditionPreserves bodyPreserves
      machine.fuel).1 machine valid
  · intro machine valid
    exact (whileLoopAux_preservesResults label condition body conditionPreserves bodyPreserves
      machine.fuel).2 machine valid

/-- Machine preservation alone is inherited from the full loop result theorem. -/
theorem whileLoop_preservesWellFormed (condition : JSM P Bool) (body : JSM P Unit)
    (conditionPreserves : JSM.PreservesResults (fun _ _ => True) condition)
    (bodyPreserves : JSM.PreservesResults (fun _ _ => True) body)
    (label : Option JSString := none) :
    JSM.PreservesWellFormed (whileLoop condition body label) :=
  (whileLoop_preservesResults condition body conditionPreserves bodyPreserves label).1

private theorem handleLoopControl_fuel_mono (label : Option JSString) (body : JSM P Unit)
    (bodyFuel : ∀ machine, (body machine).AllMachines (fun final => final.fuel ≤ machine.fuel)) :
    ∀ machine, (handleLoopControl label body machine).AllMachines
      (fun final => final.fuel ≤ machine.fuel) := by
  intro machine
  unfold handleLoopControl
  cases result : body machine with
  | done completion final =>
      have fuelBound := bodyFuel machine
      rw [result] at fuelBound
      cases completion with
      | normal unitResult =>
          cases unitResult
          simpa [result, classifyLoop] using fuelBound
      | returned value | thrown value => simpa [result, classifyLoop] using fuelBound
      | «break» actual | «continue» actual =>
          simp only [result, classifyLoop]
          split <;> exact fuelBound
  | exhausted final | fault fault final => simpa [result] using bodyFuel machine

private theorem whileLoopAux_fuel_mono (label : Option JSString) (condition : JSM P Bool)
    (body : JSM P Unit)
    (conditionFuel : ∀ machine,
      (condition machine).AllMachines (fun final => final.fuel ≤ machine.fuel))
    (bodyFuel : ∀ machine, (body machine).AllMachines (fun final => final.fuel ≤ machine.fuel))
    (remaining : Nat) : ∀ machine,
    (whileLoopAux label condition body remaining machine).AllMachines
      (fun final => final.fuel ≤ machine.fuel) := by
  induction remaining with
  | zero =>
      intro machine
      exact Nat.le_refl _
  | succ remaining ih =>
      intro machine
      unfold whileLoopAux JSM.consumeFuel
      cases consumed : machine.consumeFuel with
      | none => exact Nat.le_refl _
      | some fueled =>
          have fuelBound : fueled.fuel ≤ machine.fuel := by
            unfold Machine.consumeFuel at consumed
            cases fuelEq : machine.fuel with
            | zero => simp [fuelEq] at consumed
            | succ fuel =>
                simp [fuelEq] at consumed
                subst fueled
                simp [fuelEq]
          simp only [consumed]
          cases conditionResult : condition fueled with
          | exhausted next | fault fault next =>
              have conditionBound := conditionFuel fueled
              rw [conditionResult] at conditionBound
              simp only [conditionResult]
              exact Nat.le_trans conditionBound fuelBound
          | done conditionCompletion next =>
              have conditionBound := conditionFuel fueled
              rw [conditionResult] at conditionBound
              have throughCondition := Nat.le_trans conditionBound fuelBound
              cases conditionCompletion with
              | normal test =>
                  cases test with
                  | false => exact throughCondition
                  | true =>
                      cases bodyResult : handleLoopControl label body next with
                      | exhausted afterBody | fault fault afterBody =>
                          have bodyBound := handleLoopControl_fuel_mono label body bodyFuel next
                          rw [bodyResult] at bodyBound
                          simp only [bodyResult]
                          exact Nat.le_trans bodyBound throughCondition
                      | done bodyCompletion afterBody =>
                          have bodyBound := handleLoopControl_fuel_mono label body bodyFuel next
                          rw [bodyResult] at bodyBound
                          simp only [bodyResult]
                          have throughBody := Nat.le_trans bodyBound throughCondition
                          cases bodyCompletion with
                          | normal keepGoing =>
                              cases keepGoing with
                              | false => exact throughBody
                              | true =>
                                  cases recursiveResult :
                                      whileLoopAux label condition body remaining afterBody with
                                  | done completion final | exhausted final | fault fault final =>
                                      have recursiveBound := ih afterBody
                                      rw [recursiveResult] at recursiveBound
                                      simp only [recursiveResult]
                                      exact Nat.le_trans recursiveBound throughBody
                          | returned value | thrown value | «break» value | «continue» value =>
                              exact throughBody
              | returned value | thrown value | «break» value | «continue» value =>
                  exact throughCondition

/-- A loop cannot increase fuel when neither its condition nor its body can increase fuel. This
bound covers every iteration and every terminal outcome. -/
theorem whileLoop_fuel_mono (condition : JSM P Bool) (body : JSM P Unit)
    (conditionFuel : ∀ machine,
      (condition machine).AllMachines (fun final => final.fuel ≤ machine.fuel))
    (bodyFuel : ∀ machine, (body machine).AllMachines (fun final => final.fuel ≤ machine.fuel))
    (label : Option JSString := none) : ∀ machine,
    (whileLoop condition body label machine).AllMachines
      (fun final => final.fuel ≤ machine.fuel) := by
  intro machine
  exact whileLoopAux_fuel_mono label condition body conditionFuel bodyFuel machine.fuel machine

end Control
end TSLean.JS
