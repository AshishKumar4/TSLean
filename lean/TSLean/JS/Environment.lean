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

end Environment
end TSLean.JS
