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

/-- Realm-owned prototype identities required by primitive wrapper allocation. -/
structure RealmIntrinsics where
  objectPrototype : RefId
  booleanPrototype : RefId
  numberPrototype : RefId
  stringPrototype : RefId
  bigintPrototype : RefId
  symbolPrototype : RefId
  deriving DecidableEq

namespace RealmIntrinsics

/-- Selects the realm prototype for a boxable primitive. -/
def prototypeFor? (intrinsics : RealmIntrinsics) : Primitive → Option RefId
  | .boolean _ => some intrinsics.booleanPrototype
  | .number _ => some intrinsics.numberPrototype
  | .string _ => some intrinsics.stringPrototype
  | .bigint _ => some intrinsics.bigintPrototype
  | .symbol _ => some intrinsics.symbolPrototype
  | .undefined | .null => none

private def hasPrototype (heap : Heap) (ref : RefId) (prototype : Option RefId) : Bool :=
  match heap.get? ref with
  | .ok object => object.prototype = prototype
  | .error _ => false

private def hasKind (heap : Heap) (ref : RefId) (kind : ObjectKind) : Bool :=
  heap.objectKind? ref = some kind

/-- Validates the stable intrinsic identities and the object kinds/internal slots they denote. -/
def intrinsicsRefsValid (intrinsics : RealmIntrinsics) (heap : Heap) : Bool :=
  let primitivePrototypes := [intrinsics.booleanPrototype, intrinsics.numberPrototype,
    intrinsics.stringPrototype, intrinsics.bigintPrototype, intrinsics.symbolPrototype]
  (intrinsics.objectPrototype :: primitivePrototypes).Nodup &&
  hasKind heap intrinsics.objectPrototype .ordinary &&
  hasKind heap intrinsics.booleanPrototype (.primitiveWrapper ⟨.boolean false⟩) &&
  hasKind heap intrinsics.numberPrototype
    (.primitiveWrapper ⟨.number JSNumber.positiveZero⟩) &&
  hasKind heap intrinsics.stringPrototype
    (.primitiveWrapper ⟨.string (JSString.ofLeanString "")⟩) &&
  hasKind heap intrinsics.bigintPrototype .ordinary &&
  hasKind heap intrinsics.symbolPrototype .ordinary

/-- Validates the exact prototype graph required when a realm is first bootstrapped. -/
def bootstrapTopologyValid (intrinsics : RealmIntrinsics) (heap : Heap) : Bool :=
  intrinsics.intrinsicsRefsValid heap &&
  hasPrototype heap intrinsics.objectPrototype none &&
  [intrinsics.booleanPrototype, intrinsics.numberPrototype, intrinsics.stringPrototype,
    intrinsics.bigintPrototype, intrinsics.symbolPrototype].all
      (hasPrototype heap · (some intrinsics.objectPrototype))

/-- Bootstrap topology includes the complete ongoing intrinsic-reference invariant. -/
theorem bootstrapTopologyValid_implies_intrinsicsRefsValid (intrinsics : RealmIntrinsics)
    (heap : Heap) (valid : intrinsics.bootstrapTopologyValid heap = true) :
    intrinsics.intrinsicsRefsValid heap = true := by
  simp [bootstrapTopologyValid] at valid
  exact valid.1.1

/-- Legal prototype mutation preserves intrinsic identities and their object kinds/internal slots. -/
theorem intrinsicsRefsValid_setPrototypeOf (intrinsics : RealmIntrinsics) (heap next : Heap)
    (target : RefId) (prototype : Option RefId) (success : Bool)
    (valid : intrinsics.intrinsicsRefsValid heap = true)
    (updated : heap.setPrototypeOf target prototype = .ok (success, next)) :
    intrinsics.intrinsicsRefsValid next = true := by
  unfold intrinsicsRefsValid hasKind at valid ⊢
  simp only [Heap.setPrototypeOf_preserves_objectKind heap next target prototype success updated]
  exact valid

end RealmIntrinsics

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
  | escapingFunctionControl
  | danglingEscapingValue (ref : RefId)
  | unsupportedDerivedConstruction (constructor : RefId)
  | realmNotInitialized
  | invalidRealmIntrinsics
  deriving DecidableEq

/-- A total machine with append-only identity arenas and newest-first trace storage. -/
structure Machine (P : Platform) where
  private mk ::
  heap : Heap
  cells : Array Cell
  environments : Array EnvironmentRecord
  currentEnv : EnvId
  intrinsics : Option RealmIntrinsics
  platform : P.State
  reverseTrace : List TraceEvent
  fuel : Nat

namespace Machine

/-- Creates a machine containing one valid global lexical environment at identity zero. -/
def initial (P : Platform) (fuel : Nat) : Machine P :=
  .mk Heap.empty #[] #[⟨none, Std.HashMap.emptyWithCapacity⟩] ⟨0⟩ none P.initialState [] fuel

/-- Returns the root global environment identity. -/
def globalEnv (_machine : Machine P) : EnvId := ⟨0⟩

/-- Returns events in execution order. This reversal is linear in the trace length. -/
def trace (machine : Machine P) : List TraceEvent := machine.reverseTrace.reverse

/-- Replaces the committed heap. -/
def setHeap (machine : Machine P) (heap : Heap) : Machine P := { machine with heap }

/-- Installs validated realm prototype identities without changing heap or execution state. -/
def installRealmIntrinsics (machine : Machine P) (intrinsics : RealmIntrinsics) :
    Except RuntimeFault (Machine P) :=
  if intrinsics.bootstrapTopologyValid machine.heap then
    .ok { machine with intrinsics := some intrinsics }
  else .error .invalidRealmIntrinsics

/-- Successful realm installation certifies the exact one-time bootstrap topology. -/
theorem installRealmIntrinsics_requires_bootstrapTopology (machine next : Machine P)
    (intrinsics : RealmIntrinsics)
    (installed : machine.installRealmIntrinsics intrinsics = .ok next) :
    intrinsics.bootstrapTopologyValid machine.heap = true := by
  unfold installRealmIntrinsics at installed
  split at installed
  · assumption
  · contradiction

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

private def environmentTerminates (machine : Machine P) : Nat → EnvId → Bool
  | 0, _ => false
  | fuel + 1, id =>
      match machine.environments[id.value]? with
      | none => false
      | some environment =>
          match environment.parent with
          | none => true
          | some parent => environmentTerminates machine fuel parent

private def environmentValidAt (machine : Machine P) (entry : EnvironmentRecord × Nat) : Bool :=
  entry.1.parent.all (fun parent => parent.value < machine.environments.size) &&
  entry.1.bindings.toList.all (fun binding => binding.2.value < machine.cells.size) &&
  environmentTerminates machine (machine.environments.size + 1) ⟨entry.2⟩

private def cellValid (machine : Machine P) (cell : Cell) : Bool :=
  match cell.state with
  | .uninitialized => true
  | .initialized value => machine.heap.valueValid value

private def realmValid (machine : Machine P) : Bool :=
  machine.intrinsics.all (·.intrinsicsRefsValid machine.heap)

/-- Executable complete machine invariant, including heap validity, arena references, acyclic
environment parents, binding cells, current environment, and every function's captured environment. -/
def isWellFormed (machine : Machine P) : Bool :=
  machine.heap.isWellFormed &&
  machine.currentEnv.value < machine.environments.size &&
  machine.cells.toList.all (cellValid machine) &&
  machine.environments.toList.zipIdx.all (environmentValidAt machine) &&
  realmValid machine &&
  machine.heap.functionEnvironments.all fun environment =>
    environment.value < machine.environments.size

/-- Complete machine validity represented by its executable checker. -/
def WellFormed (machine : Machine P) : Prop := machine.isWellFormed = true

/-- A fresh machine satisfies heap, arena, and captured-environment validity. -/
theorem initial_wellFormed (P : Platform) (fuel : Nat) :
    (Machine.initial P fuel).WellFormed := by
  have heapValid : Heap.empty.isWellFormed = true := Heap.empty_wellFormed
  simp only [WellFormed, isWellFormed, initial]
  rw [heapValid]
  simp [environmentValidAt, environmentTerminates, Heap.functionEnvironments,
    Heap.functionSlotList, Heap.empty, realmValid]

end Machine
end TSLean.JS
