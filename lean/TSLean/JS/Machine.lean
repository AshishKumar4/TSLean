import Std.Data.HashMap
import TSLean.JS.Heap
import TSLean.JS.Platform

namespace TSLean.JS

/-- A lexical cell is either in TDZ or initialized with an ECMAScript value. -/
inductive CellState where
  | uninitialized
  | initialized (value : Value)
  deriving DecidableEq

/-- Stable lexical-cell contents and assignment policy. -/
structure Cell where
  state : CellState
  mutable : Bool
  deriving DecidableEq

/-- One lexical environment and its stable parent link. -/
structure EnvironmentRecord where
  parent : Option EnvId
  bindings : Std.HashMap JSString CellId

/-- Observable execution events, stored in reverse order by `Machine`. -/
inductive TraceEvent where
  | emitted (message : JSString)
  | now (value : Nat)
  | random (value : JSNumber)
  | fetch (request : FetchRequest) (result : FetchResult)
  | platformFault (operation : JSString) (fault : PlatformFault)
  deriving DecidableEq

/-- Internal arena and invariant failures, separate from JavaScript exceptions. -/
inductive RuntimeFault where
  | heap (fault : HeapFault)
  | invalidCell (id : CellId)
  | alreadyInitialized (id : CellId)
  | invalidEnvironment (id : EnvId)
  | duplicateBinding (name : JSString)
  | unresolvableBinding (name : JSString)
  deriving DecidableEq

/-- A total machine with append-only identity arenas and newest-first trace storage. -/
structure Machine (P : Platform) where
  private mk ::
  heap : Heap
  cells : Array Cell
  environments : Array EnvironmentRecord
  currentEnv : EnvId
  platform : P.State
  reverseTrace : List TraceEvent
  fuel : Nat

namespace Machine

/-- Creates a machine containing one valid global lexical environment at identity zero. -/
def initial (P : Platform) (fuel : Nat) : Machine P :=
  .mk Heap.empty #[] #[⟨none, Std.HashMap.emptyWithCapacity⟩] ⟨0⟩ P.initialState [] fuel

/-- Returns the root global environment identity. -/
def globalEnv (_machine : Machine P) : EnvId := ⟨0⟩

/-- Returns events in execution order. This reversal is linear in the trace length. -/
def trace (machine : Machine P) : List TraceEvent := machine.reverseTrace.reverse

/-- Replaces the committed heap. -/
def setHeap (machine : Machine P) (heap : Heap) : Machine P := { machine with heap }

/-- Replaces pure platform state. -/
def setPlatform (machine : Machine P) (platform : P.State) : Machine P := { machine with platform }

/-- Prepends one event in constant time. -/
def emit (machine : Machine P) (event : TraceEvent) : Machine P :=
  { machine with reverseTrace := event :: machine.reverseTrace }

/-- Decrements fuel, or reports exhaustion without changing the machine. -/
def consumeFuel (machine : Machine P) : Option (Machine P) :=
  match machine.fuel with
  | 0 => none
  | fuel + 1 => some { machine with fuel }

/-- Reads a stable cell identity. -/
def getCell (machine : Machine P) (id : CellId) : Except RuntimeFault Cell :=
  match machine.cells[id.value]? with
  | some cell => .ok cell
  | none => .error (.invalidCell id)

/-- Replaces an existing stable cell. -/
def setCell (machine : Machine P) (id : CellId) (cell : Cell) : Except RuntimeFault (Machine P) :=
  if inBounds : id.value < machine.cells.size then
    .ok { machine with cells := machine.cells.set id.value cell inBounds }
  else .error (.invalidCell id)

/-- Appends a cell and returns its fresh stable identity. -/
def allocateCell (machine : Machine P) (cell : Cell) : CellId × Machine P :=
  (⟨machine.cells.size⟩, { machine with cells := machine.cells.push cell })

/-- Reads a stable environment identity. -/
def getEnvironment (machine : Machine P) (id : EnvId) : Except RuntimeFault EnvironmentRecord :=
  match machine.environments[id.value]? with
  | some environment => .ok environment
  | none => .error (.invalidEnvironment id)

/-- Replaces an existing stable environment. -/
def setEnvironment (machine : Machine P) (id : EnvId) (environment : EnvironmentRecord) :
    Except RuntimeFault (Machine P) :=
  if inBounds : id.value < machine.environments.size then
    .ok { machine with environments := machine.environments.set id.value environment inBounds }
  else .error (.invalidEnvironment id)

/-- Appends an environment and returns its fresh stable identity. -/
def allocateEnvironment (machine : Machine P) (parent : Option EnvId) :
    Except RuntimeFault (EnvId × Machine P) :=
  match parent with
  | some id =>
      match machine.getEnvironment id with
      | .error fault => .error fault
      | .ok _ =>
          let id := ⟨machine.environments.size⟩
          .ok (id, { machine with environments :=
            machine.environments.push ⟨parent, Std.HashMap.emptyWithCapacity⟩ })
  | none =>
      let id := ⟨machine.environments.size⟩
      .ok (id, { machine with environments :=
        machine.environments.push ⟨none, Std.HashMap.emptyWithCapacity⟩ })

/-- Changes the dynamic environment only when the target identity is valid. -/
def switchEnvironment (machine : Machine P) (id : EnvId) : Except RuntimeFault (Machine P) :=
  match machine.getEnvironment id with
  | .error fault => .error fault
  | .ok _ => .ok { machine with currentEnv := id }

end Machine
end TSLean.JS
