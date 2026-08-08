import TSLean.JS.Completion
import TSLean.JS.Machine

namespace TSLean.JS

/-- Failures of the executable model, never JavaScript exception values. -/
inductive ModelFault where
  | runtime (fault : RuntimeFault)
  | platform (fault : PlatformFault)
  deriving DecidableEq

/-- A machine run always returns its final committed state. -/
inductive RunResult (P : Platform) (α : Type) where
  | done (completion : Completion α) (machine : Machine P)
  | exhausted (machine : Machine P)
  | fault (fault : ModelFault) (machine : Machine P)

namespace RunResult

/-- Requires a predicate of the committed machine in every terminal result. -/
def AllMachines (predicate : Machine P → Prop) : RunResult P α → Prop
  | .done _ machine | .exhausted machine | .fault _ machine => predicate machine

/-- Final-machine validity and execution identity continuity for every terminal outcome. -/
def MachinePreserved (initial : Machine P) : RunResult P α → Prop
  | .done _ final | .exhausted final | .fault _ final =>
      final.WellFormed ∧ initial.ContinuesFrom final

/-- Prefixing a preserved run with a continuous machine step preserves the original machine. -/
theorem MachinePreserved.trans {initial middle : Machine P} {result : RunResult P α}
    (first : initial.ContinuesFrom middle) (preserved : result.MachinePreserved middle) :
    result.MachinePreserved initial := by
  cases result with
  | done completion final | exhausted final | fault fault final =>
      exact ⟨preserved.1,
        Machine.continuesFrom_trans initial middle final first preserved.2⟩

/-- Validity of every JavaScript value carried by a completion. -/
def CompletionValuesValid (normalValid : α → Machine P → Prop) : RunResult P α → Prop
  | .done (.normal value) machine => normalValid value machine
  | .done (.returned value) machine | .done (.thrown value) machine =>
      machine.heap.valueValid value = true
  | .done (.break _) _ | .done (.continue _) _ | .exhausted _ | .fault _ _ => True

end RunResult

/-- Total JavaScript state computations with explicit non-JavaScript terminal outcomes. -/
def JSM (P : Platform) (α : Type) := Machine P → RunResult P α

namespace JSM

/-- An action preserves complete machine validity through every terminal outcome. -/
def PreservesWellFormed (action : JSM P α) : Prop :=
  ∀ machine, machine.WellFormed → (action machine).MachinePreserved machine

/-- Conditional preservation for operations whose inputs refer to the starting machine. -/
def PreservesWellFormedWhen (precondition : Machine P → Prop) (action : JSM P α) : Prop :=
  ∀ machine, machine.WellFormed → precondition machine →
    (action machine).MachinePreserved machine

/-- An action also validates every value escaping in a completion. -/
def PreservesResults (normalValid : α → Machine P → Prop) (action : JSM P α) : Prop :=
  PreservesWellFormed action ∧ ∀ machine, machine.WellFormed →
    (action machine).CompletionValuesValid normalValid

/-- Conditional machine and completion-result validity from a machine-local precondition. -/
def PreservesResultsWhen (precondition : Machine P → Prop)
    (normalValid : α → Machine P → Prop) (action : JSM P α) : Prop :=
  PreservesWellFormedWhen precondition action ∧ ∀ machine, machine.WellFormed →
    precondition machine → (action machine).CompletionValuesValid normalValid

/-- A continuity-stable precondition can be carried alongside an action's normal result. -/
theorem preservesResults_carryPrecondition (action : JSM P α)
    (actionPreserves : PreservesResults normalValid action)
    (precondition : Machine P → Prop)
    (stable : ∀ initial final, initial.ContinuesFrom final →
      precondition initial → precondition final) :
    PreservesResultsWhen precondition
      (fun value final => normalValid value final ∧ precondition final) action := by
  constructor
  · intro machine valid preconditionValid
    exact actionPreserves.1 machine valid
  · intro machine valid preconditionValid
    have machinePreserved := actionPreserves.1 machine valid
    have resultValid := actionPreserves.2 machine valid
    cases result : action machine with
    | done completion final =>
        rw [result] at machinePreserved resultValid
        cases completion with
        | normal value => exact ⟨resultValid, stable machine final machinePreserved.2 preconditionValid⟩
        | returned value | thrown value | «break» label | «continue» label => exact resultValid
    | exhausted final | fault fault final => trivial

/-- A conditional action can retain its own continuity-stable precondition on normal completion. -/
theorem preservesResultsWhen_carryPrecondition (action : JSM P α)
    (actionPreserves : PreservesResultsWhen precondition normalValid action)
    (stable : ∀ initial final, initial.ContinuesFrom final →
      precondition initial → precondition final) :
    PreservesResultsWhen precondition
      (fun value final => normalValid value final ∧ precondition final) action := by
  constructor
  · exact actionPreserves.1
  · intro machine valid preconditionValid
    have machinePreserved := actionPreserves.1 machine valid preconditionValid
    have resultValid := actionPreserves.2 machine valid preconditionValid
    cases result : action machine with
    | done completion final =>
        rw [result] at machinePreserved resultValid
        cases completion with
        | normal value => exact ⟨resultValid, stable machine final machinePreserved.2 preconditionValid⟩
        | returned value | thrown value | «break» label | «continue» label => exact resultValid
    | exhausted final | fault fault final => trivial

/-- A stronger machine-local premise can discharge an action's narrower premise. -/
theorem preservesResultsWhen_mono (action : JSM P α)
    (actionPreserves : PreservesResultsWhen weaker normalValid action)
    (implies : ∀ machine, stronger machine → weaker machine) :
    PreservesResultsWhen stronger normalValid action :=
  ⟨fun machine valid premise => actionPreserves.1 machine valid (implies machine premise),
    fun machine valid premise => actionPreserves.2 machine valid (implies machine premise)⟩

/-- Executes a computation from a supplied valid machine. -/
def run (action : JSM P α) (machine : Machine P) : RunResult P α := action machine

/-- Produces a normal completion without changing state. -/
protected def pure (value : α) : JSM P α := fun machine => .done (.normal value) machine

/-- Pure computations preserve the complete machine invariant. -/
theorem pure_preservesWellFormed (value : α) :
    PreservesWellFormed (JSM.pure value : JSM P α) := by
  intro machine valid
  exact ⟨valid, machine.continuesFrom_refl⟩

/-- Pure computations validate their normal result when the supplied predicate does. -/
theorem pure_preservesResults (normalValid : α → Machine P → Prop) (value : α)
    (validValue : ∀ machine, machine.WellFormed →
    normalValid value machine) :
    PreservesResults normalValid (JSM.pure (P := P) value) := by
  refine ⟨pure_preservesWellFormed value, ?_⟩
  intro machine valid
  exact validValue machine valid

/-- Sequences normal completion while preserving state for all terminal outcomes. -/
protected def bind (action : JSM P α) (next : α → JSM P β) : JSM P β := fun machine =>
  match action machine with
  | .done (.normal value) nextMachine => next value nextMachine
  | .done (.returned value) nextMachine => .done (.returned value) nextMachine
  | .done (.thrown value) nextMachine => .done (.thrown value) nextMachine
  | .done (.break label) nextMachine => .done (.break label) nextMachine
  | .done (.continue label) nextMachine => .done (.continue label) nextMachine
  | .exhausted nextMachine => .exhausted nextMachine
  | .fault fault nextMachine => .fault fault nextMachine

/-- Preservation composes through normal-result sequencing. -/
theorem bind_preservesWellFormed (action : JSM P α) (next : α → JSM P β)
    (actionPreserves : PreservesWellFormed action)
    (nextPreserves : ∀ value, PreservesWellFormed (next value)) :
    PreservesWellFormed (JSM.bind action next) := by
  intro machine valid
  unfold JSM.bind
  cases result : action machine with
  | done completion nextMachine =>
      have actionResult := actionPreserves machine valid
      rw [result] at actionResult
      have nextValid : nextMachine.WellFormed := actionResult.1
      have firstContinues : machine.ContinuesFrom nextMachine := actionResult.2
      cases completion with
      | normal value =>
          have finalResult := nextPreserves value nextMachine nextValid
          cases nextRun : next value nextMachine with
          | done completion final | exhausted final | fault fault final =>
              rw [nextRun] at finalResult
              simp only [nextRun]
              exact ⟨finalResult.1,
                Machine.continuesFrom_trans _ _ _ firstContinues finalResult.2⟩
      | returned value | thrown value | «break» label | «continue» label =>
          exact ⟨nextValid, firstContinues⟩
  | exhausted nextMachine | fault fault nextMachine =>
      simpa [result] using actionPreserves machine valid

/-- Result validity composes through normal-result sequencing. -/
theorem bind_preservesResults (action : JSM P α) (next : α → JSM P β)
    (actionPreserves : PreservesResults firstValid action)
    (nextPreserves : ∀ value machine, machine.WellFormed → firstValid value machine →
      (next value machine).MachinePreserved machine ∧
        (next value machine).CompletionValuesValid finalValid) :
    PreservesResults finalValid (JSM.bind action next) := by
  constructor
  · intro machine valid
    unfold JSM.bind
    cases result : action machine with
    | done completion nextMachine =>
      have firstMachine := actionPreserves.1 machine valid
      have firstResult := actionPreserves.2 machine valid
      rw [result] at firstMachine firstResult
      cases completion with
        | normal value =>
            have second := (nextPreserves value nextMachine firstMachine.1 firstResult).1
            cases nextResult : next value nextMachine with
            | done finalCompletion final | exhausted final | fault fault final =>
                rw [nextResult] at second
                simp only [nextResult]
                exact ⟨second.1, Machine.continuesFrom_trans _ _ _ firstMachine.2 second.2⟩
        | returned value | thrown value | «break» label | «continue» label => exact firstMachine
    | exhausted nextMachine | fault fault nextMachine =>
        simpa [result] using actionPreserves.1 machine valid
  · intro machine valid
    unfold JSM.bind
    cases result : action machine with
    | done completion nextMachine =>
        have firstMachine := actionPreserves.1 machine valid
        have firstResult := actionPreserves.2 machine valid
        rw [result] at firstMachine firstResult
        cases completion with
        | normal value => exact (nextPreserves value nextMachine firstMachine.1 firstResult).2
        | returned value | thrown value | «break» label | «continue» label => exact firstResult
    | exhausted nextMachine | fault fault nextMachine => trivial

/-- Conditional result preservation composes through normal-result sequencing. -/
theorem bind_preservesResultsWhen (action : JSM P α) (next : α → JSM P β)
    (actionPreserves : PreservesResultsWhen precondition firstValid action)
    (nextPreserves : ∀ value machine, machine.WellFormed → firstValid value machine →
      (next value machine).MachinePreserved machine ∧
        (next value machine).CompletionValuesValid finalValid) :
    PreservesResultsWhen precondition finalValid (JSM.bind action next) := by
  constructor
  · intro machine valid preconditionValid
    unfold JSM.bind
    cases result : action machine with
    | done completion nextMachine =>
        have firstMachine := actionPreserves.1 machine valid preconditionValid
        have firstResult := actionPreserves.2 machine valid preconditionValid
        rw [result] at firstMachine firstResult
        cases completion with
        | normal value =>
            have second := (nextPreserves value nextMachine firstMachine.1 firstResult).1
            cases nextResult : next value nextMachine with
            | done finalCompletion final | exhausted final | fault fault final =>
                rw [nextResult] at second
                simp only [nextResult]
                exact ⟨second.1,
                  Machine.continuesFrom_trans _ _ _ firstMachine.2 second.2⟩
        | returned value | thrown value | «break» label | «continue» label => exact firstMachine
    | exhausted nextMachine | fault fault nextMachine =>
        simpa [result] using actionPreserves.1 machine valid preconditionValid
  · intro machine valid preconditionValid
    unfold JSM.bind
    cases result : action machine with
    | done completion nextMachine =>
        have firstMachine := actionPreserves.1 machine valid preconditionValid
        have firstResult := actionPreserves.2 machine valid preconditionValid
        rw [result] at firstMachine firstResult
        cases completion with
        | normal value => exact (nextPreserves value nextMachine firstMachine.1 firstResult).2
        | returned value | thrown value | «break» label | «continue» label => exact firstResult
    | exhausted nextMachine | fault fault nextMachine => trivial

instance : Monad (JSM P) where
  pure := JSM.pure
  bind := JSM.bind

/-- Reads the complete machine. -/
def get : JSM P (Machine P) := fun machine => .done (.normal machine) machine

/-- Replaces the complete machine. -/
def set (machine : Machine P) : JSM P Unit := fun _ => .done (.normal ()) machine

/-- Applies a pure total machine update. -/
def modify (update : Machine P → Machine P) : JSM P Unit := fun machine =>
  .done (.normal ()) (update machine)

/-- Stops with an explicit model fault. -/
def fail (fault : ModelFault) : JSM P α := fun machine => .fault fault machine

/-- A terminal action that leaves state unchanged preserves complete validity. -/
theorem unchanged_preservesWellFormed (result : Machine P → RunResult P α)
    (unchanged : ∀ machine, (result machine).AllMachines (· = machine)) :
    PreservesWellFormed result := by
  intro machine valid
  cases outcome : result machine with
  | done completion next | exhausted next | fault fault next =>
      have : next = machine := by simpa [outcome] using unchanged machine
      subst next
      exact ⟨valid, machine.continuesFrom_refl⟩

/-- Model faults preserve complete validity because they do not change state. -/
theorem fail_preservesWellFormed (fault : ModelFault) :
    PreservesWellFormed (JSM.fail fault : JSM P α) := by
  intro machine valid
  exact ⟨valid, machine.continuesFrom_refl⟩

/-- Model faults carry no completion result to validate. -/
theorem fail_preservesResults (normalValid : α → Machine P → Prop) (fault : ModelFault) :
    PreservesResults normalValid (JSM.fail fault : JSM P α) := by
  exact ⟨fail_preservesWellFormed fault, by intro machine valid; trivial⟩

/-- Reading the machine preserves execution identity. -/
theorem get_preservesWellFormed : PreservesWellFormed (get : JSM P (Machine P)) := by
  intro machine valid
  exact ⟨valid, machine.continuesFrom_refl⟩

/-- Reading the machine returns the unchanged final machine. -/
theorem get_preservesResults :
    PreservesResults (fun returned final => returned = final) (get : JSM P (Machine P)) := by
  exact ⟨get_preservesWellFormed, by intro machine valid; rfl⟩

/-- Replacing the machine is safe exactly when every valid source continues to the supplied state. -/
theorem set_preservesWellFormed (replacement : Machine P) (replacementValid : replacement.WellFormed)
    (continues : ∀ (machine : Machine P), machine.WellFormed →
      machine.ContinuesFrom replacement) :
    PreservesWellFormed (set replacement) := by
  intro machine valid
  exact ⟨replacementValid, continues machine valid⟩

/-- A pure machine update preserves execution when its contract supplies validity and continuity. -/
theorem modify_preservesWellFormed (update : Machine P → Machine P)
    (preserved : ∀ (machine : Machine P), machine.WellFormed →
      (update machine).WellFormed ∧ machine.ContinuesFrom (update machine)) :
    PreservesWellFormed (modify update) := by
  intro machine valid
  exact preserved machine valid

/-- Reads the committed object heap. -/
def readHeap : JSM P Heap := fun machine => .done (.normal machine.heap) machine

/-- Applies a pure heap update and commits it. -/
def modifyHeap (update : Heap → Heap) : JSM P Unit := fun machine =>
  .done (.normal ()) (machine.setHeap (update machine.heap))

/-- Emits one observable event in constant time. -/
def emit (event : TraceEvent) : JSM P Unit := fun machine =>
  .done (.normal ()) (machine.emit event)

/-- Consumes one unit of meta-level execution fuel. -/
def consumeFuel : JSM P Unit := fun machine =>
  match machine.consumeFuel with
  | some next => .done (.normal ()) next
  | none => .exhausted machine

/-- Reading the heap preserves execution identity. -/
theorem readHeap_preservesWellFormed : PreservesWellFormed (readHeap : JSM P Heap) := by
  intro machine valid
  exact ⟨valid, machine.continuesFrom_refl⟩

/-- Reading the heap returns the final machine's unchanged committed heap. -/
theorem readHeap_preservesResults :
    PreservesResults (fun heap machine => heap = machine.heap) (readHeap : JSM P Heap) := by
  exact ⟨readHeap_preservesWellFormed, by intro machine valid; rfl⟩

/-- A committed heap update preserves the machine under complete heap validity and continuity. -/
theorem modifyHeap_preservesWellFormed (update : Heap → Heap)
    (heapValid : ∀ (machine : Machine P), machine.WellFormed → (update machine.heap).WellFormed)
    (continuous : ∀ (machine : Machine P), machine.WellFormed →
      machine.heap.MachineReferencesPreserved (update machine.heap)) :
    PreservesWellFormed (modifyHeap update : JSM P Unit) := by
  intro machine valid
  have nextHeapValid := heapValid machine valid
  have references := continuous machine valid
  exact ⟨machine.setHeap_preserves_wellFormed (update machine.heap) valid nextHeapValid references,
    machine.setHeap_continuesFrom_machineReferences (update machine.heap) valid nextHeapValid references⟩

/-- Event emission preserves machine validity and execution identity. -/
theorem emit_preservesWellFormed (event : TraceEvent) :
    PreservesWellFormed (emit event : JSM P Unit) := by
  intro machine valid
  exact ⟨Machine.emit_preserves_wellFormed machine event valid,
    machine.emit_continuesFrom event⟩

/-- Event emission validates its unit result. -/
theorem emit_preservesResults (event : TraceEvent) :
    PreservesResults (fun _ _ => True) (emit event : JSM P Unit) := by
  exact ⟨emit_preservesWellFormed event, by intro machine valid; trivial⟩

/-- Fuel consumption preserves machine validity and execution identity on success and exhaustion. -/
theorem consumeFuel_preservesWellFormed : PreservesWellFormed (consumeFuel : JSM P Unit) := by
  intro machine valid
  unfold consumeFuel
  cases consumed : machine.consumeFuel with
  | none => exact ⟨valid, machine.continuesFrom_refl⟩
  | some next =>
      exact ⟨Machine.consumeFuel_preserves_wellFormed machine next valid consumed,
        Machine.consumeFuel_continuesFrom machine next consumed⟩

/-- Fuel consumption validates its unit result on success and has none on exhaustion. -/
theorem consumeFuel_preservesResults :
    PreservesResults (fun _ _ => True) (consumeFuel : JSM P Unit) := by
  refine ⟨consumeFuel_preservesWellFormed, ?_⟩
  intro machine valid
  unfold consumeFuel
  cases machine.consumeFuel <;> trivial

/-- Produces a JavaScript return completion. -/
def returnJS (value : Value) : JSM P α := fun machine => .done (.returned value) machine

/-- Produces a JavaScript throw completion. -/
def throwJS (value : Value) : JSM P α := fun machine => .done (.thrown value) machine

/-- Produces a JavaScript break completion. -/
def breakJS (label : Option JSString := none) : JSM P α := fun machine =>
  .done (.break label) machine

/-- Produces a JavaScript continue completion. -/
def continueJS (label : Option JSString := none) : JSM P α := fun machine =>
  .done (.continue label) machine

/-- JavaScript return completion leaves the machine invariant unchanged. -/
theorem returnJS_preservesWellFormed (value : Value) :
    PreservesWellFormed (JSM.returnJS value : JSM P α) := by
  intro machine valid
  exact ⟨valid, machine.continuesFrom_refl⟩

/-- Return validates its escaping value under the starting heap's validity premise. -/
theorem returnJS_preservesResults (normalValid : α → Machine P → Prop) (value : Value) :
    PreservesResultsWhen (fun machine => machine.heap.valueValid value = true) normalValid
      (JSM.returnJS value : JSM P α) := by
  constructor <;> intro machine valid valueValid
  · exact ⟨valid, machine.continuesFrom_refl⟩
  · exact valueValid

/-- JavaScript throw completion leaves the machine invariant unchanged. -/
theorem throwJS_preservesWellFormed (value : Value) :
    PreservesWellFormed (JSM.throwJS value : JSM P α) := by
  intro machine valid
  exact ⟨valid, machine.continuesFrom_refl⟩

/-- Throw validates its escaping value under the starting heap's validity premise. -/
theorem throwJS_preservesResults (normalValid : α → Machine P → Prop) (value : Value) :
    PreservesResultsWhen (fun machine => machine.heap.valueValid value = true) normalValid
      (JSM.throwJS value : JSM P α) := by
  constructor <;> intro machine valid valueValid
  · exact ⟨valid, machine.continuesFrom_refl⟩
  · exact valueValid

/-- JavaScript break completion leaves the machine invariant unchanged. -/
theorem breakJS_preservesWellFormed (label : Option JSString) :
    PreservesWellFormed (JSM.breakJS label : JSM P α) := by
  intro machine valid
  exact ⟨valid, machine.continuesFrom_refl⟩

/-- Break carries no value requiring validation. -/
theorem breakJS_preservesResults (normalValid : α → Machine P → Prop)
    (label : Option JSString) :
    PreservesResults normalValid (JSM.breakJS label : JSM P α) := by
  exact ⟨breakJS_preservesWellFormed label, by intro machine valid; trivial⟩

/-- JavaScript continue completion leaves the machine invariant unchanged. -/
theorem continueJS_preservesWellFormed (label : Option JSString) :
    PreservesWellFormed (JSM.continueJS label : JSM P α) := by
  intro machine valid
  exact ⟨valid, machine.continuesFrom_refl⟩

/-- Continue carries no value requiring validation. -/
theorem continueJS_preservesResults (normalValid : α → Machine P → Prop)
    (label : Option JSString) :
    PreservesResults normalValid (JSM.continueJS label : JSM P α) := by
  exact ⟨continueJS_preservesWellFormed label, by intro machine valid; trivial⟩

end JSM
end TSLean.JS
