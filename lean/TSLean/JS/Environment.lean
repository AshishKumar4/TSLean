import TSLean.JS.Monad

namespace TSLean.JS

namespace Environment

private def errorValue (kind : String) (name : JSString) : Value :=
  let rendered := name.toLeanString?.getD "<invalid UTF-16>"
  .primitive (.string (JSString.ofLeanString (kind ++ ": " ++ rendered)))

/-- Allocates another parentless global environment without changing `currentEnv`. -/
def allocateGlobal : JSM P EnvId := fun machine =>
  match machine.allocateEnvironment none with
  | .ok (id, next) => .done (.normal id) next
  | .error fault => .fault (.runtime fault) machine

/-- Allocates a child of a stable environment without changing `currentEnv`. -/
def allocateChild (parent : EnvId) : JSM P EnvId := fun machine =>
  match machine.allocateEnvironment (some parent) with
  | .ok (id, next) => .done (.normal id) next
  | .error fault => .fault (.runtime fault) machine

/-- Declares a fresh TDZ cell. Duplicate declarations are explicit model faults. -/
def declare (environment : EnvId) (name : JSString) (mutable : Bool) : JSM P CellId :=
  fun machine =>
    match machine.getEnvironment environment with
    | .error fault => .fault (.runtime fault) machine
    | .ok record =>
        if record.bindings.contains name then
          .fault (.runtime (.duplicateBinding name)) machine
        else
          let (cell, withCell) := machine.allocateCell ⟨.uninitialized, mutable⟩
          let updated := { record with bindings := record.bindings.insert name cell }
          match withCell.setEnvironment environment updated with
          | .ok next => .done (.normal cell) next
          | .error fault => .fault (.runtime fault) withCell

/-- Initializes a TDZ cell exactly once. Invalid or repeated initialization is a model fault. -/
def «initialize» (cell : CellId) (value : Value) : JSM P Unit := fun machine =>
  match machine.getCell cell with
  | .error fault => .fault (.runtime fault) machine
  | .ok ⟨.initialized _, _⟩ => .fault (.runtime (.alreadyInitialized cell)) machine
  | .ok ⟨.uninitialized, mutable⟩ =>
      match machine.setCell cell ⟨.initialized value, mutable⟩ with
      | .ok next => .done (.normal ()) next
      | .error fault => .fault (.runtime fault) machine

/-- Pure bounded lexical lookup used by the executable environment API. -/
def resolveCell (machine : Machine P) (name : JSString) : Nat → EnvId →
    Except RuntimeFault CellId
  | 0, _ => .error (.unresolvableBinding name)
  | fuel + 1, environment =>
      match machine.getEnvironment environment with
      | .error fault => .error fault
      | .ok record =>
          match record.bindings.get? name with
          | some cell => .ok cell
          | none =>
              match record.parent with
              | some parent => resolveCell machine name fuel parent
              | none => .error (.unresolvableBinding name)

/-- Resolves the nearest lexical binding from a stable environment. -/
def resolve (environment : EnvId) (name : JSString) : JSM P CellId := fun machine =>
  match resolveCell machine name (machine.environments.size + 1) environment with
  | .ok cell => .done (.normal cell) machine
  | .error (.unresolvableBinding _) => .done (.thrown (errorValue "ReferenceError" name)) machine
  | .error fault => .fault (.runtime fault) machine

/-- Reads a cell. TDZ access is represented as a JavaScript ReferenceError value. -/
def readCell (cell : CellId) : JSM P Value := fun machine =>
  match machine.getCell cell with
  | .error fault => .fault (.runtime fault) machine
  | .ok ⟨.uninitialized, _⟩ =>
      .done (.thrown (errorValue "ReferenceError" (JSString.ofLeanString "TDZ"))) machine
  | .ok ⟨.initialized value, _⟩ => .done (.normal value) machine

/-- Resolves and reads the nearest binding. -/
def read (environment : EnvId) (name : JSString) : JSM P Value := do
  let cell ← resolve environment name
  readCell cell

/-- Writes an initialized mutable cell. TDZ and immutable writes are JavaScript errors. -/
def writeCell (cell : CellId) (value : Value) : JSM P Unit := fun machine =>
  match machine.getCell cell with
  | .error fault => .fault (.runtime fault) machine
  | .ok ⟨.uninitialized, _⟩ =>
      .done (.thrown (errorValue "ReferenceError" (JSString.ofLeanString "TDZ"))) machine
  | .ok ⟨.initialized _, false⟩ =>
      .done (.thrown (errorValue "TypeError" (JSString.ofLeanString "immutable binding"))) machine
  | .ok ⟨.initialized _, true⟩ =>
      match machine.setCell cell ⟨.initialized value, true⟩ with
      | .ok next => .done (.normal ()) next
      | .error fault => .fault (.runtime fault) machine

/-- Resolves and writes the nearest binding. -/
def write (environment : EnvId) (name : JSString) (value : Value) : JSM P Unit := do
  let cell ← resolve environment name
  writeCell cell value

/-- Runs under a dynamic lexical environment and restores `currentEnv` after every JavaScript
completion. Arena allocations, heap/platform mutation, trace, and fuel remain committed. -/
def withEnvironment (environment : EnvId) (action : JSM P α) : JSM P α := fun machine =>
  match machine.switchEnvironment environment with
  | .error fault => .fault (.runtime fault) machine
  | .ok entered =>
      let restore (next : Machine P) := next.switchEnvironment machine.currentEnv
      match action entered with
      | .done completion next =>
          match restore next with
          | .ok restored => .done completion restored
          | .error fault => .fault (.runtime fault) next
      | .exhausted next =>
          match restore next with
          | .ok restored => .exhausted restored
          | .error fault => .fault (.runtime fault) next
      | .fault modelFault next =>
          match restore next with
          | .ok restored => .fault modelFault restored
          | .error fault => .fault (.runtime fault) next

private theorem errorValue_valid (machine : Machine P) (kind : String) (name : JSString) :
    machine.heap.valueValid (errorValue kind name) = true := by
  simp [errorValue, Heap.valueValid]

/-- Global-environment allocation preserves the machine and returns an allocated identity. -/
theorem allocateGlobal_preservesResults :
    JSM.PreservesResults (fun id machine => machine.ValidEnvId id)
      (allocateGlobal : JSM P EnvId) := by
  constructor <;> intro machine valid
  · unfold allocateGlobal
    cases allocated : machine.allocateEnvironment none with
    | error fault => exact ⟨valid, machine.continuesFrom_refl⟩
    | ok result =>
        obtain ⟨id, next⟩ := result
        exact ⟨Machine.allocateEnvironment_preserves_wellFormed machine next none id valid allocated,
          Machine.allocateEnvironment_continuesFrom machine next none id allocated⟩
  · unfold allocateGlobal
    cases allocated : machine.allocateEnvironment none with
    | error fault => trivial
    | ok result =>
        obtain ⟨id, next⟩ := result
        exact Machine.allocateEnvironment_valid machine next none id allocated

/-- Child-environment allocation preserves the machine and returns an allocated identity. -/
theorem allocateChild_preservesResults (parent : EnvId) :
    JSM.PreservesResults (fun id machine => machine.ValidEnvId id)
      (allocateChild parent : JSM P EnvId) := by
  constructor <;> intro machine valid
  · unfold allocateChild
    cases allocated : machine.allocateEnvironment (some parent) with
    | error fault => exact ⟨valid, machine.continuesFrom_refl⟩
    | ok result =>
        obtain ⟨id, next⟩ := result
        exact ⟨Machine.allocateEnvironment_preserves_wellFormed machine next (some parent) id
            valid allocated,
          Machine.allocateEnvironment_continuesFrom machine next (some parent) id allocated⟩
  · unfold allocateChild
    cases allocated : machine.allocateEnvironment (some parent) with
    | error fault => trivial
    | ok result =>
        obtain ⟨id, next⟩ := result
        exact Machine.allocateEnvironment_valid machine next (some parent) id allocated

/-- Declaration preserves the machine, including its committed-cell fault branch, and returns an
allocated fresh cell identity on success. -/
theorem declare_preservesResults (environment : EnvId) (name : JSString) (mutable : Bool) :
    JSM.PreservesResults (fun cell machine => machine.ValidCellId cell)
      (declare (P := P) environment name mutable) := by
  constructor <;> intro machine machineValid
  · unfold declare
    cases found : machine.getEnvironment environment with
    | error fault => exact ⟨machineValid, machine.continuesFrom_refl⟩
    | ok record =>
        simp only
        split
        next duplicate => exact ⟨machineValid, machine.continuesFrom_refl⟩
        next fresh =>
          let cell := (machine.allocateCell ⟨.uninitialized, mutable⟩).1
          let withCell := (machine.allocateCell ⟨.uninitialized, mutable⟩).2
          let bindings := record.bindings.insert name cell
          have withCellValid := Machine.allocateCell_uninitialized_preserves_wellFormed machine mutable
            machineValid
          have firstContinues := Machine.allocateCell_continuesFrom machine
            ⟨.uninitialized, mutable⟩
          have foundWithCell : withCell.getEnvironment environment = .ok record := by
            simpa [withCell, Machine.allocateCell] using found
          have bindingsValid : ∀ (bindingName : JSString) (bindingCell : CellId),
              bindings[bindingName]? = some bindingCell → withCell.ValidCellId bindingCell := by
            intro bindingName bindingCell bindingFound
            by_cases same : bindingName = name
            · subst bindingName
              simp [bindings] at bindingFound
              subst bindingCell
              simp [cell, withCell, Machine.ValidCellId, Machine.allocateCell]
            · have oldFound : record.bindings[bindingName]? = some bindingCell := by
                simpa [bindings, Std.HashMap.getElem?_insert, same, Ne.symm same] using bindingFound
              have oldValid := Machine.wellFormed_binding_valid machine environment record
                bindingName bindingCell machineValid found oldFound
              unfold Machine.ValidCellId at oldValid ⊢
              simpa [withCell, Machine.allocateCell] using Nat.lt_succ_of_lt oldValid
          cases updated : withCell.setEnvironment environment { record with bindings } with
          | error fault => simpa [updated] using And.intro withCellValid firstContinues
          | ok next =>
              have nextValid := Machine.setEnvironment_bindings_preserves_wellFormed withCell next
                environment record bindings withCellValid foundWithCell bindingsValid updated
              have secondContinues := Machine.setEnvironment_continuesFrom withCell next environment
                { record with bindings } (by
                  intro oldRecord oldFound
                  have sameRecord : oldRecord = record := by
                    unfold Machine.getEnvironment at foundWithCell
                    rw [oldFound] at foundWithCell
                    simpa using foundWithCell
                  subst oldRecord
                  refine ⟨rfl, ?_⟩
                  intro bindingName bindingCell bindingFound
                  by_cases sameName : bindingName = name
                  · subst bindingName
                    have present : record.bindings.contains name = true := by
                      rw [Std.HashMap.contains_eq_isSome_getElem?, bindingFound]
                      rfl
                    contradiction
                  · simpa [bindings, Std.HashMap.getElem?_insert, sameName, Ne.symm sameName]
                      using bindingFound) updated
              simpa [updated] using And.intro nextValid
                (Machine.continuesFrom_trans machine withCell next firstContinues secondContinues)
  · unfold declare
    cases found : machine.getEnvironment environment with
    | error fault => trivial
    | ok record =>
        simp only
        split
        next duplicate => trivial
        next fresh =>
          let cell := (machine.allocateCell ⟨.uninitialized, mutable⟩).1
          let withCell := (machine.allocateCell ⟨.uninitialized, mutable⟩).2
          let bindings := record.bindings.insert name cell
          have cellValid : withCell.ValidCellId cell := by
            simp [cell, withCell, Machine.ValidCellId, Machine.allocateCell]
          cases updated : withCell.setEnvironment environment { record with bindings } with
          | error fault => exact True.intro
          | ok next =>
              simpa [updated] using
                (Machine.setEnvironment_preserves_validCellId withCell next environment
                  { record with bindings } cell updated).mp cellValid

private theorem resolveCell_valid (machine : Machine P) (name : JSString) (fuel : Nat)
    (environment : EnvId) (cell : CellId) (valid : machine.WellFormed)
    (resolved : resolveCell machine name fuel environment = .ok cell) :
    machine.ValidCellId cell := by
  induction fuel generalizing environment with
  | zero => simp [resolveCell] at resolved
  | succ fuel ih =>
      unfold resolveCell at resolved
      cases foundEnvironment : machine.getEnvironment environment with
      | error fault => simp [foundEnvironment] at resolved
      | ok record =>
          simp only [foundEnvironment] at resolved
          cases foundBinding : record.bindings.get? name with
          | some foundCell =>
              rw [foundBinding] at resolved
              simp at resolved
              have same : foundCell = cell := resolved
              subst cell
              exact Machine.wellFormed_binding_valid machine environment record name foundCell valid
                foundEnvironment foundBinding
          | none =>
              simp only [foundBinding] at resolved
              cases parentEq : record.parent with
              | none => simp [parentEq] at resolved
              | some parent =>
                  simp only [parentEq] at resolved
                  exact ih parent resolved

/-- Lexical resolution preserves the machine and returns only an allocated cell identity. -/
theorem resolve_preservesResults (environment : EnvId) (name : JSString) :
    JSM.PreservesResults (fun cell machine => machine.ValidCellId cell)
      (resolve (P := P) environment name) := by
  constructor
  · intro machine valid
    unfold resolve
    cases resolved : resolveCell machine name (machine.environments.size + 1) environment with
    | ok cell => exact ⟨valid, machine.continuesFrom_refl⟩
    | error fault =>
        cases fault <;> exact ⟨valid, machine.continuesFrom_refl⟩
  · intro machine valid
    unfold resolve
    cases resolved : resolveCell machine name (machine.environments.size + 1) environment with
    | ok cell => exact resolveCell_valid machine name _ environment cell valid resolved
    | error fault =>
        cases fault with
        | unresolvableBinding unresolved => exact errorValue_valid machine "ReferenceError" name
        | heap fault => trivial
        | invalidCell id => trivial
        | alreadyInitialized id => trivial
        | invalidEnvironment id => trivial
        | duplicateBinding duplicate => trivial
        | escapingFunctionControl => trivial
        | danglingEscapingValue ref => trivial
        | unsupportedDerivedConstruction constructor => trivial
        | realmNotInitialized => trivial
        | invalidRealmIntrinsics => trivial

/-- Initialization preserves validity when its value is valid in the starting heap. Repeated
initialization follows the unchanged fault branch. -/
theorem initialize_preservesResults (cell : CellId) (value : Value) :
    JSM.PreservesResultsWhen (fun machine => machine.heap.valueValid value = true)
      (fun _ _ => True) («initialize» (P := P) cell value) := by
  constructor <;> intro machine machineValid valueValid
  · unfold «initialize»
    cases found : machine.getCell cell with
    | error fault => simpa [found] using And.intro machineValid machine.continuesFrom_refl
    | ok current =>
        cases current with
        | mk state mutable =>
            cases state with
            | initialized old => simpa [found] using And.intro machineValid machine.continuesFrom_refl
            | uninitialized =>
                cases updated : machine.setCell cell ⟨.initialized value, mutable⟩ with
                | error fault =>
                    simpa [found, updated] using And.intro machineValid machine.continuesFrom_refl
                | ok next =>
                    have result := And.intro
                      (Machine.setCell_initialized_preserves_wellFormed machine next cell value mutable
                        machineValid valueValid updated)
                      (Machine.setCell_continuesFrom machine next cell
                        ⟨.initialized value, mutable⟩ (by
                          intro oldCell oldFound
                          unfold Machine.getCell at found
                          rw [oldFound] at found
                          simp at found
                          subst oldCell
                          rfl) updated)
                    simpa [found, updated] using result
  · unfold «initialize»
    cases found : machine.getCell cell with
    | error fault => exact True.intro
    | ok current =>
        cases current with
        | mk state mutable =>
            cases state with
            | initialized old => exact True.intro
            | uninitialized =>
                cases updated : machine.setCell cell ⟨.initialized value, mutable⟩ with
                | error fault => simp [updated, RunResult.CompletionValuesValid]
                | ok next => simp [updated, RunResult.CompletionValuesValid]

/-- Primitive initialization needs no heap-reference premise. -/
theorem initialize_primitive_preservesResults (cell : CellId) (value : Primitive) :
    JSM.PreservesResults (fun (_ : Unit) (_ : Machine P) => True)
      («initialize» (P := P) cell (.primitive value)) := by
  exact ⟨fun machine valid => (initialize_preservesResults cell (.primitive value)).1 machine valid
      rfl,
    fun machine valid => (initialize_preservesResults cell (.primitive value)).2 machine valid
      rfl⟩

/-- Reading a cell preserves the machine and returns only a valid stored value or primitive error. -/
theorem readCell_preservesResults (cell : CellId) :
    JSM.PreservesResults (fun value machine => machine.heap.valueValid value = true)
      (readCell (P := P) cell) := by
  constructor
  · intro machine valid
    unfold readCell
    cases found : machine.getCell cell with
    | error fault => simpa [found] using And.intro valid machine.continuesFrom_refl
    | ok current =>
        cases current with
        | mk state mutable =>
            cases state <;> simpa [found] using And.intro valid machine.continuesFrom_refl
  · intro machine valid
    unfold readCell
    cases found : machine.getCell cell with
    | error fault => exact True.intro
    | ok current =>
        cases current with
        | mk state mutable =>
            cases state with
            | uninitialized => simpa [found] using errorValue_valid machine "ReferenceError" _
            | initialized value =>
                simpa [found] using
                  Machine.wellFormed_getCell_valueValid machine cell value mutable valid found

/-- Resolve-then-read composition preserves continuity and returns only heap-valid values. -/
theorem read_preservesResults (environment : EnvId) (name : JSString) :
    JSM.PreservesResults (fun value machine => machine.heap.valueValid value = true)
      (read (P := P) environment name) := by
  apply JSM.bind_preservesResults
  · exact resolve_preservesResults environment name
  · intro cell machine valid cellValid
    exact ⟨(readCell_preservesResults cell).1 machine valid,
      (readCell_preservesResults cell).2 machine valid⟩

/-- Writing preserves validity when the replacement value is valid in the starting heap. -/
theorem writeCell_preservesResults (cell : CellId) (value : Value) :
    JSM.PreservesResultsWhen (fun machine => machine.heap.valueValid value = true)
      (fun _ _ => True) (writeCell (P := P) cell value) := by
  constructor <;> intro machine machineValid valueValid
  · unfold writeCell
    cases found : machine.getCell cell with
    | error fault => simpa [found] using And.intro machineValid machine.continuesFrom_refl
    | ok current =>
        cases current with
        | mk state mutable =>
            cases state with
            | uninitialized => simpa [found] using And.intro machineValid machine.continuesFrom_refl
            | initialized old =>
                cases mutable with
                | false => simpa [found] using And.intro machineValid machine.continuesFrom_refl
                | true =>
                    cases updated : machine.setCell cell ⟨.initialized value, true⟩ with
                    | error fault =>
                        simpa [found, updated] using And.intro machineValid machine.continuesFrom_refl
                    | ok next =>
                        have result := And.intro
                          (Machine.setCell_initialized_preserves_wellFormed machine next cell value true
                            machineValid valueValid updated)
                          (Machine.setCell_continuesFrom machine next cell
                            ⟨.initialized value, true⟩ (by
                              intro oldCell oldFound
                              unfold Machine.getCell at found
                              rw [oldFound] at found
                              simp at found
                              subst oldCell
                              rfl) updated)
                        simpa [found, updated] using result
  · unfold writeCell
    cases found : machine.getCell cell with
    | error fault => exact True.intro
    | ok current =>
        cases current with
        | mk state mutable =>
            cases state with
            | uninitialized => simpa [found] using errorValue_valid machine "ReferenceError" _
            | initialized old =>
                cases mutable with
                | false => simpa [found] using errorValue_valid machine "TypeError" _
                | true =>
                    cases updated : machine.setCell cell ⟨.initialized value, true⟩ with
                    | error fault => exact True.intro
                    | ok next => exact True.intro

/-- Resolve-then-write composition preserves continuity under replacement-value validity. -/
theorem write_preservesResults (environment : EnvId) (name : JSString) (value : Value) :
    JSM.PreservesResultsWhen (fun machine => machine.heap.valueValid value = true)
      (fun _ _ => True) (write (P := P) environment name value) := by
  constructor <;> intro machine machineValid valueValid
  · unfold write
    change (JSM.bind (resolve environment name) (fun cell => writeCell cell value) machine).MachinePreserved machine
    unfold JSM.bind resolve
    cases resolved : resolveCell machine name (machine.environments.size + 1) environment with
    | ok cell => exact (writeCell_preservesResults cell value).1 machine machineValid valueValid
    | error fault =>
        cases fault <;> exact ⟨machineValid, machine.continuesFrom_refl⟩
  · unfold write
    change (JSM.bind (resolve environment name) (fun cell => writeCell cell value) machine).CompletionValuesValid
      (fun _ _ => True)
    unfold JSM.bind resolve
    cases resolved : resolveCell machine name (machine.environments.size + 1) environment with
    | ok cell => exact (writeCell_preservesResults cell value).2 machine machineValid valueValid
    | error fault =>
        cases fault with
        | unresolvableBinding unresolved => exact errorValue_valid machine "ReferenceError" name
        | heap fault => trivial
        | invalidCell id => trivial
        | alreadyInitialized id => trivial
        | invalidEnvironment id => trivial
        | duplicateBinding duplicate => trivial
        | escapingFunctionControl => trivial
        | danglingEscapingValue ref => trivial
        | unsupportedDerivedConstruction constructor => trivial
        | realmNotInitialized => trivial
        | invalidRealmIntrinsics => trivial

/-- Resolve-then-write of a primitive needs no heap-reference premise. -/
theorem write_primitive_preservesResults (environment : EnvId) (name : JSString)
    (value : Primitive) :
    JSM.PreservesResults (fun (_ : Unit) (_ : Machine P) => True)
      (write (P := P) environment name (.primitive value)) := by
  exact ⟨fun machine valid => (write_preservesResults environment name (.primitive value)).1
      machine valid rfl,
    fun machine valid => (write_preservesResults environment name (.primitive value)).2
      machine valid rfl⟩

/-- Dynamic environment execution restores `currentEnv` and preserves all committed action state
for normal, return, throw, break, continue, exhaustion, and model-fault outcomes. -/
theorem withEnvironment_preservesWellFormed (environment : EnvId) (action : JSM P α)
    (actionPreserves : JSM.PreservesWellFormed action) :
    JSM.PreservesWellFormed (withEnvironment environment action) := by
  intro machine machineValid
  unfold withEnvironment
  cases enteredBy : machine.switchEnvironment environment with
  | error fault => exact ⟨machineValid, machine.continuesFrom_refl⟩
  | ok entered =>
      have enteredValid := Machine.switchEnvironment_preserves_wellFormed machine entered
        environment machineValid enteredBy
      have oldValidEntered : entered.ValidEnvId machine.currentEnv :=
        (Machine.switchEnvironment_preserves_validEnvId machine entered environment
          machine.currentEnv enteredBy).mp (Machine.wellFormed_currentEnv machine machineValid)
      have restorePreserves : ∀ next, entered.ContinuesFrom next → next.WellFormed →
          ∃ restored, next.switchEnvironment machine.currentEnv = .ok restored ∧
            restored.WellFormed ∧ machine.ContinuesFrom restored := by
        intro next continued nextValid
        have oldValidNext : next.ValidEnvId machine.currentEnv :=
          Nat.lt_of_lt_of_le oldValidEntered continued.2.2.1
        obtain ⟨record, found⟩ := Machine.getEnvironment_of_valid next machine.currentEnv oldValidNext
        cases restoredBy : next.switchEnvironment machine.currentEnv with
        | error fault => simp [Machine.switchEnvironment, found] at restoredBy
        | ok restored =>
            exact ⟨restored, rfl,
              Machine.switchEnvironment_preserves_wellFormed next restored machine.currentEnv
                nextValid restoredBy,
              Machine.restoreEnvironment_continuesFrom machine entered next restored environment
                enteredBy continued restoredBy⟩
      cases actionResult : action entered with
      | done completion next =>
          have preserved := actionPreserves entered enteredValid
          rw [actionResult] at preserved
          obtain ⟨restored, restoredBy, restoredValid, continued⟩ :=
            restorePreserves next preserved.2 preserved.1
          simp [actionResult, restoredBy]
          exact ⟨restoredValid, continued⟩
      | exhausted next =>
          have preserved := actionPreserves entered enteredValid
          rw [actionResult] at preserved
          obtain ⟨restored, restoredBy, restoredValid, continued⟩ :=
            restorePreserves next preserved.2 preserved.1
          simp [actionResult, restoredBy]
          exact ⟨restoredValid, continued⟩
      | fault modelFault next =>
          have preserved := actionPreserves entered enteredValid
          rw [actionResult] at preserved
          obtain ⟨restored, restoredBy, restoredValid, continued⟩ :=
            restorePreserves next preserved.2 preserved.1
          simp [actionResult, restoredBy]
          exact ⟨restoredValid, continued⟩

/-- Dynamic-environment restoration preserves valid normal and abrupt JavaScript values. -/
theorem withEnvironment_preservesResults (environment : EnvId) (action : JSM P Value)
    (actionPreserves : JSM.PreservesResults
      (fun value machine => machine.heap.valueValid value = true) action) :
    JSM.PreservesResults (fun value machine => machine.heap.valueValid value = true)
      (withEnvironment environment action) := by
  refine ⟨withEnvironment_preservesWellFormed environment action actionPreserves.1, ?_⟩
  intro machine machineValid
  unfold withEnvironment
  cases enteredBy : machine.switchEnvironment environment with
  | error fault => trivial
  | ok entered =>
      have enteredValid := Machine.switchEnvironment_preserves_wellFormed machine entered
        environment machineValid enteredBy
      cases actionResult : action entered with
      | done completion next =>
          have valuesValid := actionPreserves.2 entered enteredValid
          rw [actionResult] at valuesValid
          cases restoredBy : next.switchEnvironment machine.currentEnv with
          | error fault =>
              simp [actionResult, restoredBy, RunResult.CompletionValuesValid]
          | ok restored =>
              have restoredEq := restoredBy
              unfold Machine.switchEnvironment at restoredBy
              cases found : next.getEnvironment machine.currentEnv with
              | error fault => simp [found] at restoredBy
              | ok record =>
                  simp [found] at restoredBy
                  subst restored
                  simp only [actionResult, restoredEq]
                  cases completion <;> exact valuesValid
      | exhausted next =>
          cases restoredBy : next.switchEnvironment machine.currentEnv <;>
            simp [actionResult, restoredBy, RunResult.CompletionValuesValid]
      | fault modelFault next =>
          cases restoredBy : next.switchEnvironment machine.currentEnv <;>
            simp [actionResult, restoredBy, RunResult.CompletionValuesValid]

/-- Dynamic-environment restoration preserves a unit action and all abrupt values it carries. -/
theorem withEnvironment_preservesUnitResults (environment : EnvId) (action : JSM P Unit)
    (actionPreserves : JSM.PreservesResults (fun _ _ => True) action) :
    JSM.PreservesResults (fun _ _ => True) (withEnvironment environment action) := by
  refine ⟨withEnvironment_preservesWellFormed environment action actionPreserves.1, ?_⟩
  intro machine machineValid
  unfold withEnvironment
  cases enteredBy : machine.switchEnvironment environment with
  | error fault => trivial
  | ok entered =>
      have enteredValid := Machine.switchEnvironment_preserves_wellFormed machine entered
        environment machineValid enteredBy
      cases actionResult : action entered with
      | done completion next =>
          have valuesValid := actionPreserves.2 entered enteredValid
          rw [actionResult] at valuesValid
          cases restoredBy : next.switchEnvironment machine.currentEnv with
          | error fault => simp [actionResult, restoredBy, RunResult.CompletionValuesValid]
          | ok restored =>
              have restoredEq := restoredBy
              unfold Machine.switchEnvironment at restoredBy
              cases found : next.getEnvironment machine.currentEnv with
              | error fault => simp [found] at restoredBy
              | ok record =>
                  simp [found] at restoredBy
                  subst restored
                  simp only [actionResult, restoredEq]
                  cases completion <;> exact valuesValid
      | exhausted next =>
          cases restoredBy : next.switchEnvironment machine.currentEnv <;>
            simp [actionResult, restoredBy, RunResult.CompletionValuesValid]
      | fault modelFault next =>
          cases restoredBy : next.switchEnvironment machine.currentEnv <;>
            simp [actionResult, restoredBy, RunResult.CompletionValuesValid]

end Environment
end TSLean.JS
