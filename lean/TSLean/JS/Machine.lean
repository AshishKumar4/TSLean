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

/-- Heap updates that preserve machine references retain every realm intrinsic identity. -/
theorem intrinsicsRefsValid_machineReferences (intrinsics : RealmIntrinsics) (heap next : Heap)
    (valid : intrinsics.intrinsicsRefsValid heap = true)
    (preserved : heap.MachineReferencesPreserved next) :
    intrinsics.intrinsicsRefsValid next = true := by
  unfold intrinsicsRefsValid hasKind at valid ⊢
  simp only [Bool.and_eq_true] at valid ⊢
  let continued := preserved.continuesFrom
  refine ⟨⟨⟨⟨⟨⟨valid.1.1.1.1.1.1, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact decide_eq_true (continued.preserves_stableKind _ .ordinary
      (of_decide_eq_true valid.1.1.1.1.1.2) trivial)
  · exact decide_eq_true (continued.preserves_stableKind _ (.primitiveWrapper ⟨.boolean false⟩)
      (of_decide_eq_true valid.1.1.1.1.2) trivial)
  · exact decide_eq_true (continued.preserves_stableKind _
      (.primitiveWrapper ⟨.number JSNumber.positiveZero⟩)
      (of_decide_eq_true valid.1.1.1.2) trivial)
  · exact decide_eq_true (continued.preserves_stableKind _
      (.primitiveWrapper ⟨.string (JSString.ofLeanString "")⟩)
      (of_decide_eq_true valid.1.1.2) trivial)
  · exact decide_eq_true (continued.preserves_stableKind _ .ordinary
      (of_decide_eq_true valid.1.2) trivial)
  · exact decide_eq_true (continued.preserves_stableKind _ .ordinary
      (of_decide_eq_true valid.2) trivial)

/-- General heap continuity retains every stable realm intrinsic identity and kind. -/
theorem intrinsicsRefsValid_continuesFrom (intrinsics : RealmIntrinsics) (heap next : Heap)
    (valid : intrinsics.intrinsicsRefsValid heap = true)
    (continued : heap.ContinuesFrom next) :
    intrinsics.intrinsicsRefsValid next = true := by
  unfold intrinsicsRefsValid hasKind at valid ⊢
  simp only [Bool.and_eq_true] at valid ⊢
  refine ⟨⟨⟨⟨⟨⟨valid.1.1.1.1.1.1, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact decide_eq_true (continued.preserves_stableKind intrinsics.objectPrototype .ordinary
      (of_decide_eq_true valid.1.1.1.1.1.2) trivial)
  · exact decide_eq_true (continued.preserves_stableKind intrinsics.booleanPrototype
      (.primitiveWrapper ⟨.boolean false⟩) (of_decide_eq_true valid.1.1.1.1.2) trivial)
  · exact decide_eq_true (continued.preserves_stableKind intrinsics.numberPrototype
      (.primitiveWrapper ⟨.number JSNumber.positiveZero⟩)
      (of_decide_eq_true valid.1.1.1.2) trivial)
  · exact decide_eq_true (continued.preserves_stableKind intrinsics.stringPrototype
      (.primitiveWrapper ⟨.string (JSString.ofLeanString "")⟩)
      (of_decide_eq_true valid.1.1.2) trivial)
  · exact decide_eq_true (continued.preserves_stableKind intrinsics.bigintPrototype .ordinary
      (of_decide_eq_true valid.1.2) trivial)
  · exact decide_eq_true (continued.preserves_stableKind intrinsics.symbolPrototype .ordinary
      (of_decide_eq_true valid.2) trivial)

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

/-- Constructs a machine without exposing its private representation. -/
private abbrev Machine.fromFields (P : Platform) (heap : Heap) (cells : Array Cell)
    (environments : Array EnvironmentRecord) (currentEnv : EnvId)
    (intrinsics : Option RealmIntrinsics) (platform : P.State)
    (reverseTrace : List TraceEvent) (fuel : Nat) : Machine P :=
  ⟨heap, cells, environments, currentEnv, intrinsics, platform, reverseTrace, fuel⟩


namespace Machine
private def zipIdxFrom (xs : List α) (start : Nat) : List (α × Nat) :=
  (xs.enumFrom start).map fun p => (p.2, p.1)

@[simp] private theorem zipIdxFrom_length (xs : List α) (start : Nat) :
    (zipIdxFrom xs start).length = xs.length := by
  simp [zipIdxFrom]

@[simp] private theorem zipIdxFrom_nil (start : Nat) :
    zipIdxFrom ([] : List α) start = [] := rfl

@[simp] private theorem zipIdxFrom_cons (x : α) (xs : List α) (start : Nat) :
    zipIdxFrom (x :: xs) start = (x, start) :: zipIdxFrom xs (start + 1) := by
  rfl

private theorem getElem_zipIdxFrom (xs : List α) (start index : Nat)
    (bound : index < (zipIdxFrom xs start).length) :
    (zipIdxFrom xs start)[index] =
      (xs[index]'(by simpa using bound), start + index) := by
  unfold zipIdxFrom
  rw [List.getElem_map]
  rw [List.getElem_enumFrom]

private theorem zipIdxFrom_append (xs ys : List α) (start : Nat) :
    zipIdxFrom (xs ++ ys) start =
      zipIdxFrom xs start ++ zipIdxFrom ys (start + xs.length) := by
  induction xs generalizing start with
  | nil => simp [zipIdxFrom]
  | cons x xs ih =>
      simp only [List.cons_append, zipIdxFrom_cons, ih, List.length_cons, List.append_assoc]
      simp only [Nat.add_assoc, Nat.add_left_comm 1 xs.length, Nat.add_comm 1 xs.length]

private theorem hashMap_mem_toList_iff_getElem?_eq_some
    {α : Type u} {β : Type v} [BEq α] [Hashable α] [LawfulBEq α]
    (map : Std.HashMap α β) (key : α) (value : β) :
    (key, value) ∈ map.toList ↔ map[key]? = some value := by
  have valid : Std.DHashMap.Internal.Raw.WFImp map.inner.1 :=
    Std.DHashMap.Internal.Raw.WF.out map.inner.2
  rw [show map.toList = (Std.DHashMap.Internal.toListModel map.inner.1.buckets).map
      (fun p => (p.1, p.2)) by
    unfold Std.HashMap.toList Std.DHashMap.Const.toList Std.DHashMap.Raw.Const.toList
    simpa using (Std.DHashMap.Internal.Raw.foldRev_cons_apply
      (l := map.inner.1) (acc := []) (fun key value => (key, value)))]
  simp only [List.mem_map, Prod.mk.injEq]
  change (∃ p ∈ Std.DHashMap.Internal.toListModel map.inner.1.buckets,
    p.1 = key ∧ p.2 = value) ↔
    Std.DHashMap.Internal.Raw₀.Const.get? ⟨map.inner.1, map.inner.2.size_buckets_pos⟩ key =
      some value
  rw [Std.DHashMap.Internal.Raw₀.Const.get?_eq_getValue? valid]
  constructor
  · rintro ⟨p, member, keyEq, valueEq⟩
    have entry := (Std.DHashMap.Internal.List.mem_iff_getEntry?_eq_some valid.distinct).mp member
    rw [← keyEq, ← valueEq]
    rw [Std.DHashMap.Internal.List.getValue?_eq_getEntry?, entry]
    rfl
  · intro found
    cases entry : Std.DHashMap.Internal.List.getEntry? key
      (Std.DHashMap.Internal.toListModel map.inner.1.buckets) with
    | none => simp [Std.DHashMap.Internal.List.getValue?_eq_getEntry?, entry] at found
    | some pair =>
      cases pair with
      | mk foundKey foundValue =>
        have keyEq : foundKey = key :=
          LawfulBEq.eq_of_beq (Std.DHashMap.Internal.List.getEntry?_eq_some entry)
        have valueEq : foundValue = value := by
          rw [Std.DHashMap.Internal.List.getValue?_eq_getEntry?, entry] at found
          exact Option.some.inj found
        subst foundKey
        subst foundValue
        exact ⟨⟨key, value⟩,
          (Std.DHashMap.Internal.List.mem_iff_getEntry?_eq_some valid.distinct).mpr entry, rfl, rfl⟩

/-- Creates a machine containing one valid global lexical environment at identity zero. -/
def initial (P : Platform) (fuel : Nat) : Machine P :=
  Machine.fromFields P Heap.empty #[] #[⟨none, Std.HashMap.empty⟩] ⟨0⟩ none P.initialState [] fuel

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
            machine.environments.push ⟨parent, Std.HashMap.empty⟩ })
  | none =>
      let id := ⟨machine.environments.size⟩
      .ok (id, { machine with environments :=
        machine.environments.push ⟨none, Std.HashMap.empty⟩ })

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
  (zipIdxFrom machine.environments.toList 0).all (environmentValidAt machine) &&
  realmValid machine &&
  machine.heap.functionEnvironments.all fun environment =>
    environment.value < machine.environments.size

/-- Complete machine validity represented by its executable checker. -/
def WellFormed (machine : Machine P) : Prop := machine.isWellFormed = true

/-- A cell identity is allocated in this machine. -/
def ValidCellId (machine : Machine P) (id : CellId) : Prop := id.value < machine.cells.size

/-- An environment identity is allocated in this machine. -/
def ValidEnvId (machine : Machine P) (id : EnvId) : Prop :=
  id.value < machine.environments.size

/-- Complete machine validity includes complete validity of its committed heap. -/
theorem wellFormed_heap (machine : Machine P) (valid : machine.WellFormed) :
    machine.heap.WellFormed := by
  unfold WellFormed isWellFormed at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.1.1.1.1.1

/-- Complete machine validity includes validity of the current environment identity. -/
theorem wellFormed_currentEnv (machine : Machine P) (valid : machine.WellFormed) :
    machine.ValidEnvId machine.currentEnv := by
  unfold WellFormed isWellFormed at valid
  simp only [Bool.and_eq_true] at valid
  simpa [ValidEnvId] using valid.1.1.1.1.2

/-- A successfully read cell identity is allocated. -/
theorem getCell_valid (machine : Machine P) (id : CellId) (cell : Cell)
    (found : machine.getCell id = .ok cell) : machine.ValidCellId id := by
  unfold getCell at found
  cases lookup : machine.cells[id.value]? with
  | none => simp [lookup] at found
  | some current => exact (Array.getElem?_eq_some_iff.mp lookup).choose

/-- Every value stored in an initialized cell of a valid machine is heap-valid. -/
theorem wellFormed_getCell_valueValid (machine : Machine P) (id : CellId) (value : Value)
    (mutable : Bool) (valid : machine.WellFormed)
    (found : machine.getCell id = .ok ⟨.initialized value, mutable⟩) :
    machine.heap.valueValid value = true := by
  unfold WellFormed isWellFormed at valid
  simp only [Bool.and_eq_true] at valid
  rw [List.all_eq_true] at valid
  unfold getCell at found
  cases lookup : machine.cells[id.value]? with
  | none => simp [lookup] at found
  | some cell =>
      simp [lookup] at found
      subst cell
      have member : Cell.mk (.initialized value) mutable ∈ machine.cells.toList :=
        (Array.mem_toList_iff (Cell.mk (.initialized value) mutable) machine.cells).mpr
          (Array.mem_of_getElem? lookup)
      simpa [cellValid] using valid.1.1.1.2 _ member

/-- A successfully read environment identity is allocated. -/
theorem getEnvironment_valid (machine : Machine P) (id : EnvId) (record : EnvironmentRecord)
    (found : machine.getEnvironment id = .ok record) : machine.ValidEnvId id := by
  unfold getEnvironment at found
  cases lookup : machine.environments[id.value]? with
  | none => simp [lookup] at found
  | some current => exact (Array.getElem?_eq_some_iff.mp lookup).choose

/-- Every allocated environment identity can be read. -/
theorem getEnvironment_of_valid (machine : Machine P) (id : EnvId)
    (valid : machine.ValidEnvId id) : ∃ record, machine.getEnvironment id = .ok record := by
  unfold ValidEnvId at valid
  unfold getEnvironment
  cases lookup : machine.environments[id.value]? with
  | none =>
      have outOfBounds := Array.getElem?_eq_none_iff.mp lookup
      omega
  | some record => exact ⟨record, by simp⟩

/-- A readable environment in a valid machine satisfies its indexed environment invariant. -/
private theorem wellFormed_environmentValidAt (machine : Machine P) (id : EnvId)
    (record : EnvironmentRecord) (valid : machine.WellFormed)
    (found : machine.getEnvironment id = .ok record) :
    machine.environmentValidAt (record, id.value) = true := by
  have idValid := getEnvironment_valid machine id record found
  unfold getEnvironment at found
  cases lookup : machine.environments[id.value]? with
  | none => simp [lookup] at found
  | some current =>
      simp [lookup] at found
      subst current
      have arrayAt : machine.environments[id.value] = record := by
        have getEq := Array.getElem?_eq_getElem idValid
        rw [lookup] at getEq
        exact (Option.some.inj getEq).symm
      have listAt : machine.environments.toList[id.value] = record := by
        rw [Array.getElem_toList]
        exact arrayAt
      have zipBound : id.value < (zipIdxFrom machine.environments.toList 0).length := by
        simpa [ValidEnvId] using idValid
      have zippedAt : (zipIdxFrom machine.environments.toList 0)[id.value] = (record, id.value) := by
        rw [getElem_zipIdxFrom]
        simp only [Nat.zero_add]
        exact congrArg (fun value => (value, id.value)) listAt
      have member : (record, id.value) ∈ zipIdxFrom machine.environments.toList 0 := by
        rw [← zippedAt]
        exact List.getElem_mem zipBound
      unfold WellFormed isWellFormed at valid
      simp only [Bool.and_eq_true] at valid
      exact List.all_eq_true.mp valid.1.1.2 _ member

/-- Every cell identity stored in a binding of a readable valid environment is allocated. -/
theorem wellFormed_binding_valid (machine : Machine P) (environment : EnvId)
    (record : EnvironmentRecord) (name : JSString) (cell : CellId)
    (valid : machine.WellFormed) (foundEnvironment : machine.getEnvironment environment = .ok record)
    (foundBinding : record.bindings[name]? = some cell) : machine.ValidCellId cell := by
  have invariant := wellFormed_environmentValidAt machine environment record valid foundEnvironment
  unfold environmentValidAt at invariant
  simp only [Bool.and_eq_true] at invariant
  rw [List.all_eq_true] at invariant
  have member := (hashMap_mem_toList_iff_getElem?_eq_some record.bindings name cell).mpr foundBinding
  simpa [ValidCellId] using invariant.1.2 (name, cell) member

private theorem environmentTerminates_succ_of_true (machine : Machine P) (fuel : Nat)
    (id : EnvId) (terminates : machine.environmentTerminates fuel id = true) :
    machine.environmentTerminates (fuel + 1) id = true := by
  induction fuel generalizing id with
  | zero => contradiction
  | succ fuel ih =>
      unfold environmentTerminates at terminates ⊢
      cases found : machine.environments[id.value]? with
      | none => simp [found] at terminates
      | some record =>
          simp only [found] at terminates ⊢
          cases parentEq : record.parent with
          | none => simp
          | some parent =>
              simp only [parentEq] at terminates ⊢
              exact ih parent terminates

private theorem environmentTerminates_push_of_true (machine : Machine P)
    (record : EnvironmentRecord) (fuel : Nat) (id : EnvId)
    (terminates : machine.environmentTerminates fuel id = true) :
    ({ machine with environments := machine.environments.push record }).environmentTerminates
      fuel id = true := by
  induction fuel generalizing id with
  | zero => contradiction
  | succ fuel ih =>
      unfold environmentTerminates at terminates ⊢
      cases found : machine.environments[id.value]? with
      | none => simp [found] at terminates
      | some current =>
          rw [found] at terminates
          have idValid := (Array.getElem?_eq_some_iff.mp found).choose
          rw [Array.getElem?_push, if_neg (Nat.ne_of_lt idValid), found]
          cases parentEq : current.parent with
          | none => simp [parentEq]
          | some parent =>
              simp only [parentEq] at terminates ⊢
              exact ih parent terminates

private theorem pushEnvironment_preserves_wellFormed (machine : Machine P)
    (record : EnvironmentRecord) (valid : machine.WellFormed)
    (parentValid : record.parent.all (fun parent =>
      parent.value < (machine.environments.push record).size) = true)
    (bindingsValid : ∀ (name : JSString) (cell : CellId), record.bindings[name]? = some cell →
      cell.value < machine.cells.size)
    (newTerminates :
      ({ machine with environments := machine.environments.push record }).environmentTerminates
        ((machine.environments.push record).size + 1) ⟨machine.environments.size⟩ = true) :
    ({ machine with environments := machine.environments.push record }).WellFormed := by
  unfold WellFormed isWellFormed at valid ⊢
  simp only [Bool.and_eq_true] at valid ⊢
  refine ⟨⟨⟨⟨⟨valid.1.1.1.1.1, ?_⟩, valid.1.1.1.2⟩, ?_⟩,
    valid.1.2⟩, ?_⟩
  · apply decide_eq_true
    have oldBound := of_decide_eq_true valid.1.1.1.1.2
    simpa using Nat.lt_succ_of_lt oldBound
  · rw [Array.push_toList, zipIdxFrom_append, List.all_append, Bool.and_eq_true]
    constructor
    · rw [List.all_eq_true]
      have environmentsValid := List.all_eq_true.mp valid.1.1.2
      intro entry member
      have oldValid := environmentsValid entry member
      unfold environmentValidAt at oldValid ⊢
      simp only [Bool.and_eq_true] at oldValid ⊢
      refine ⟨⟨?_, oldValid.1.2⟩, ?_⟩
      · cases parentEq : entry.1.parent with
        | none => simp
        | some parent =>
            simp only [parentEq, Option.all_some] at oldValid ⊢
            apply decide_eq_true
            have oldBound := of_decide_eq_true oldValid.1.1
            simpa using Nat.lt_succ_of_lt oldBound
      · have pushed := environmentTerminates_push_of_true machine record
          (machine.environments.size + 1) ⟨entry.2⟩ oldValid.2
        have increased := environmentTerminates_succ_of_true
          ({ machine with environments := machine.environments.push record })
          (machine.environments.size + 1) ⟨entry.2⟩ pushed
        simpa using increased
    · unfold environmentValidAt
      rw [List.all_eq_true]
      intro entry member
      simp at member
      subst entry
      simp only [Bool.and_eq_true]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · simpa using parentValid
      · rw [List.all_eq_true]
        intro binding bindingMember
        have bindingFound :=
          (hashMap_mem_toList_iff_getElem?_eq_some record.bindings binding.1 binding.2).mp
            bindingMember
        exact decide_eq_true (bindingsValid binding.1 binding.2 bindingFound)
      · simpa using newTerminates
  · rw [List.all_eq_true]
    have functionsValid := List.all_eq_true.mp valid.2
    intro environment member
    have oldBound := of_decide_eq_true (functionsValid environment member)
    apply decide_eq_true
    simpa using Nat.lt_succ_of_lt oldBound

/-- Successful environment append preserves the complete machine invariant. -/
theorem allocateEnvironment_preserves_wellFormed (machine next : Machine P)
    (parent : Option EnvId) (fresh : EnvId) (valid : machine.WellFormed)
    (allocated : machine.allocateEnvironment parent = .ok (fresh, next)) : next.WellFormed := by
  cases parent with
  | none =>
      simp [allocateEnvironment] at allocated
      obtain ⟨rfl, rfl⟩ := allocated
      apply pushEnvironment_preserves_wellFormed machine
        ⟨none, Std.HashMap.empty⟩ valid
      · simp
      · intro name cell found
        simp at found
      · simp [environmentTerminates]
  | some parent =>
      cases found : machine.getEnvironment parent with
      | error fault => simp [allocateEnvironment, found] at allocated
      | ok parentRecord =>
          simp [allocateEnvironment, found] at allocated
          obtain ⟨rfl, rfl⟩ := allocated
          have parentInvariant := wellFormed_environmentValidAt machine parent parentRecord valid found
          unfold environmentValidAt at parentInvariant
          simp only [Bool.and_eq_true] at parentInvariant
          apply pushEnvironment_preserves_wellFormed machine
            ⟨some parent, Std.HashMap.empty⟩ valid
          · simp only [Option.all_some]
            apply decide_eq_true
            have oldBound := getEnvironment_valid machine parent parentRecord found
            simpa using Nat.lt_succ_of_lt oldBound
          · intro name cell found
            simp at found
          · have pushed := environmentTerminates_push_of_true machine
              ⟨some parent, Std.HashMap.empty⟩
              (machine.environments.size + 1) parent parentInvariant.2
            simpa [environmentTerminates, Array.getElem?_push] using pushed

/-- Appending a cell preserves every previously allocated cell lookup. -/
theorem allocateCell_preserves_getCell (machine : Machine P) (cell : Cell) (old : CellId)
    (oldValid : machine.ValidCellId old) :
    (machine.allocateCell cell).2.getCell old = machine.getCell old := by
  unfold ValidCellId at oldValid
  unfold allocateCell getCell
  simp [Array.getElem?_push, Nat.ne_of_lt oldValid]

/-- A freshly appended cell is readable at its returned identity. -/
theorem allocateCell_getCell (machine : Machine P) (cell : Cell) :
    (machine.allocateCell cell).2.getCell (machine.allocateCell cell).1 = .ok cell := by
  simp [allocateCell, getCell]

/-- Appending an environment preserves every previously allocated environment lookup. -/
theorem allocateEnvironment_preserves_getEnvironment (machine next : Machine P)
    (parent : Option EnvId) (fresh old : EnvId)
    (oldValid : machine.ValidEnvId old)
    (allocated : machine.allocateEnvironment parent = .ok (fresh, next)) :
    next.getEnvironment old = machine.getEnvironment old := by
  cases parent with
  | none =>
      simp [allocateEnvironment] at allocated
      rcases allocated with ⟨rfl, rfl⟩
      unfold ValidEnvId at oldValid
      unfold getEnvironment
      simp [Array.getElem?_push, Nat.ne_of_lt oldValid]
  | some parent =>
      cases found : machine.getEnvironment parent with
      | error fault => simp [allocateEnvironment, found] at allocated
      | ok record =>
          simp [allocateEnvironment, found] at allocated
          rcases allocated with ⟨rfl, rfl⟩
          unfold ValidEnvId at oldValid
          unfold getEnvironment
          simp [Array.getElem?_push, Nat.ne_of_lt oldValid]

/-- A successful environment append returns a readable fresh identity. -/
theorem allocateEnvironment_getEnvironment (machine next : Machine P)
    (parent : Option EnvId) (fresh : EnvId)
    (allocated : machine.allocateEnvironment parent = .ok (fresh, next)) :
    ∃ record, next.getEnvironment fresh = .ok record := by
  cases parent with
  | none =>
      simp [allocateEnvironment] at allocated
      obtain ⟨rfl, rfl⟩ := allocated
      exact ⟨⟨none, Std.HashMap.empty⟩,
        by simp [getEnvironment]⟩
  | some parent =>
      cases found : machine.getEnvironment parent with
      | error fault => simp [allocateEnvironment, found] at allocated
      | ok record =>
          simp [allocateEnvironment, found] at allocated
          obtain ⟨rfl, rfl⟩ := allocated
          exact ⟨⟨some parent, Std.HashMap.empty⟩,
            by simp [getEnvironment]⟩

private theorem environmentTerminates_setCell (machine : Machine P) (cells : Array Cell)
    (fuel : Nat) (id : EnvId) :
    ({ machine with cells }).environmentTerminates fuel id =
      machine.environmentTerminates fuel id := by
  induction fuel generalizing id with
  | zero => rfl
  | succ fuel ih =>
      unfold environmentTerminates
      cases found : machine.environments[id.value]? with
      | none => rfl
      | some environment =>
          cases parentEq : environment.parent with
          | none => simp [parentEq]
          | some parent => simpa [parentEq] using ih parent

private theorem environmentValidAt_setCell (machine : Machine P) (cells : Array Cell)
    (sameSize : cells.size = machine.cells.size) (entry : EnvironmentRecord × Nat) :
    ({ machine with cells }).environmentValidAt entry = machine.environmentValidAt entry := by
  unfold environmentValidAt
  simp only [sameSize]
  rw [environmentTerminates_setCell]

/-- Replacing an allocated cell with a valid cell preserves the complete machine invariant. -/
theorem setCell_preserves_wellFormed (machine next : Machine P) (id : CellId) (cell : Cell)
    (valid : machine.WellFormed) (cellIsValid : machine.cellValid cell = true)
    (updated : machine.setCell id cell = .ok next) : next.WellFormed := by
  unfold setCell at updated
  split at updated
  next inBounds =>
    simp only [Except.ok.injEq] at updated
    subst next
    unfold WellFormed isWellFormed at valid ⊢
    simp only [Bool.and_eq_true] at valid ⊢
    refine ⟨⟨⟨⟨⟨valid.1.1.1.1.1, valid.1.1.1.1.2⟩, ?_⟩, ?_⟩,
      valid.1.2⟩, valid.2⟩
    · rw [List.all_eq_true] at valid ⊢
      intro candidate member
      rw [Array.mem_toList_iff] at member
      obtain ⟨index, indexValid, candidateEq⟩ := Array.getElem_of_mem member
      by_cases same : index = id.value
      · subst index
        have candidateCell : candidate = cell := by simpa using candidateEq.symm
        subst candidate
        simpa [cellValid] using cellIsValid
      · have oldIndexValid : index < machine.cells.size := by simpa using indexValid
        rw [Array.getElem_set_ne machine.cells id.value inBounds cell indexValid (Ne.symm same)]
          at candidateEq
        have oldLookup : machine.cells[index]? = some candidate := by
          rw [Array.getElem?_eq_getElem oldIndexValid]
          exact congrArg some candidateEq
        have oldMember : candidate ∈ machine.cells.toList := by
          exact (Array.mem_toList_iff candidate machine.cells).mpr (Array.mem_of_getElem? oldLookup)
        exact valid.1.1.1.2 candidate oldMember
    · rw [List.all_eq_true]
      have environmentsValid := List.all_eq_true.mp valid.1.1.2
      intro entry member
      rw [environmentValidAt_setCell machine (machine.cells.set id.value cell inBounds)
        (Array.size_set machine.cells id.value cell inBounds)]
      exact environmentsValid entry (by simpa using member)
  next outOfBounds => contradiction

/-- Replacing a cell with an initialized heap-valid value preserves the machine invariant. -/
theorem setCell_initialized_preserves_wellFormed (machine next : Machine P) (id : CellId)
    (value : Value) (mutable : Bool) (valid : machine.WellFormed)
    (valueValid : machine.heap.valueValid value = true)
    (updated : machine.setCell id ⟨.initialized value, mutable⟩ = .ok next) : next.WellFormed :=
  setCell_preserves_wellFormed machine next id ⟨.initialized value, mutable⟩ valid
    (by simpa [cellValid]) updated

/-- Appending an uninitialized cell preserves the complete machine invariant. -/
theorem allocateCell_uninitialized_preserves_wellFormed (machine : Machine P) (mutable : Bool)
    (valid : machine.WellFormed) :
    (machine.allocateCell ⟨.uninitialized, mutable⟩).2.WellFormed := by
  unfold WellFormed isWellFormed at valid ⊢
  simp only [allocateCell, Bool.and_eq_true] at valid ⊢
  refine ⟨⟨⟨⟨⟨valid.1.1.1.1.1, valid.1.1.1.1.2⟩, ?_⟩, ?_⟩,
    valid.1.2⟩, valid.2⟩
  · simpa [cellValid] using valid.1.1.1.2
  · rw [List.all_eq_true]
    have environmentsValid := List.all_eq_true.mp valid.1.1.2
    intro entry member
    have oldValid := environmentsValid entry (by simpa using member)
    unfold environmentValidAt at oldValid ⊢
    simp only [Bool.and_eq_true] at oldValid ⊢
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simpa using oldValid.1.1
    · rw [List.all_eq_true] at oldValid ⊢
      intro binding bindingMember
      have bound := of_decide_eq_true (oldValid.1.2 binding bindingMember)
      apply decide_eq_true
      simpa using Nat.lt_succ_of_lt bound
    · rw [environmentTerminates_setCell]
      exact oldValid.2

private theorem environmentTerminates_currentEnv (machine : Machine P) (currentEnv : EnvId)
    (fuel : Nat) (id : EnvId) :
    ({ machine with currentEnv }).environmentTerminates fuel id =
      machine.environmentTerminates fuel id := by
  induction fuel generalizing id with
  | zero => rfl
  | succ fuel ih =>
      unfold environmentTerminates
      cases found : machine.environments[id.value]? with
      | none => rfl
      | some environment =>
          cases parentEq : environment.parent with
          | none => simp [parentEq]
          | some parent => simpa [parentEq] using ih parent

private theorem environmentValidAt_currentEnv (machine : Machine P) (currentEnv : EnvId)
    (entry : EnvironmentRecord × Nat) :
    ({ machine with currentEnv }).environmentValidAt entry = machine.environmentValidAt entry := by
  unfold environmentValidAt
  rw [environmentTerminates_currentEnv]

/-- Switching to an allocated environment preserves complete machine validity. -/
theorem switchEnvironment_preserves_wellFormed (machine next : Machine P) (id : EnvId)
    (valid : machine.WellFormed) (switched : machine.switchEnvironment id = .ok next) :
    next.WellFormed := by
  unfold switchEnvironment at switched
  cases found : machine.getEnvironment id with
  | error fault => simp [found] at switched
  | ok record =>
      simp [found] at switched
      subst next
      unfold WellFormed isWellFormed at valid ⊢
      simp only [Bool.and_eq_true] at valid ⊢
      refine ⟨⟨⟨⟨⟨valid.1.1.1.1.1, ?_⟩, valid.1.1.1.2⟩, ?_⟩,
        valid.1.2⟩, valid.2⟩
      · exact decide_eq_true (getEnvironment_valid machine id record found)
      · rw [List.all_eq_true]
        have environmentsValid := List.all_eq_true.mp valid.1.1.2
        intro entry member
        rw [environmentValidAt_currentEnv]
        exact environmentsValid entry member

/-- Switching the current environment leaves every environment identity's allocation unchanged. -/
theorem switchEnvironment_preserves_validEnvId (machine next : Machine P) (target old : EnvId)
    (switched : machine.switchEnvironment target = .ok next) :
    machine.ValidEnvId old ↔ next.ValidEnvId old := by
  unfold switchEnvironment at switched
  cases found : machine.getEnvironment target with
  | error fault => simp [found] at switched
  | ok record =>
      simp [found] at switched
      subst next
      rfl

private theorem environmentTerminates_setParent (machine : Machine P) (target : EnvId)
    (old replacement : EnvironmentRecord)
    (targetValid : target.value < machine.environments.size)
    (found : machine.environments[target.value]? = some old)
    (sameParent : replacement.parent = old.parent) (fuel : Nat) (id : EnvId) :
    ({ machine with environments :=
      (machine.environments.set target.value replacement targetValid) }).environmentTerminates fuel id =
      machine.environmentTerminates fuel id := by
  induction fuel generalizing id with
  | zero => rfl
  | succ fuel ih =>
      unfold environmentTerminates
      rw [Array.getElem?_set]
      by_cases same : target.value = id.value
      · rw [if_pos same, ← same, found]
        simp only
        rw [sameParent]
        cases parentEq : old.parent with
        | none => simp
        | some parent => simpa [parentEq] using ih parent
      · rw [if_neg same]
        cases currentFound : machine.environments[id.value]? with
        | none => rfl
        | some current =>
            cases parentEq : current.parent with
            | none => simp [parentEq]
            | some parent => simpa [parentEq] using ih parent

private theorem environmentValidAt_setParent (machine : Machine P) (target : EnvId)
    (old replacement : EnvironmentRecord)
    (targetValid : target.value < machine.environments.size)
    (found : machine.environments[target.value]? = some old)
    (sameParent : replacement.parent = old.parent)
    (entry : EnvironmentRecord × Nat) :
    ({ machine with environments :=
      (machine.environments.set target.value replacement targetValid) }).environmentValidAt entry =
      machine.environmentValidAt entry := by
  unfold environmentValidAt
  simp only [Array.size_set]
  rw [environmentTerminates_setParent machine target old replacement targetValid found sameParent]

/-- Replacing only one environment's binding map preserves validity when every new binding points
to an allocated cell. -/
theorem setEnvironment_bindings_preserves_wellFormed (machine next : Machine P)
    (environment : EnvId) (record : EnvironmentRecord)
    (bindings : Std.HashMap JSString CellId) (valid : machine.WellFormed)
    (found : machine.getEnvironment environment = .ok record)
    (bindingsValid : ∀ (name : JSString) (cell : CellId), bindings[name]? = some cell →
      machine.ValidCellId cell)
    (updated : machine.setEnvironment environment { record with bindings } = .ok next) :
    next.WellFormed := by
  unfold setEnvironment at updated
  split at updated
  next inBounds =>
    simp only [Except.ok.injEq] at updated
    subst next
    have arrayFound : machine.environments[environment.value]? = some record := by
      unfold getEnvironment at found
      cases lookup : machine.environments[environment.value]? with
      | none => simp [lookup] at found
      | some current => simpa [lookup] using congrArg some found
    have machineValid := valid
    unfold WellFormed isWellFormed at valid ⊢
    simp only [Bool.and_eq_true] at valid ⊢
    refine ⟨⟨⟨⟨⟨valid.1.1.1.1.1, by simpa using valid.1.1.1.1.2⟩,
      valid.1.1.1.2⟩, ?_⟩, valid.1.2⟩, by simpa using valid.2⟩
    rw [List.all_eq_true]
    have oldAll := List.all_eq_true.mp valid.1.1.2
    intro entry member
    obtain ⟨index, indexBound, entryAt⟩ := List.mem_iff_getElem.mp member
    have oldIndexBound : index < (zipIdxFrom machine.environments.toList 0).length := by
      simpa using indexBound
    by_cases same : index = environment.value
    · subst index
      rw [getElem_zipIdxFrom] at entryAt
      have recordAt : machine.environments.toList[environment.value] = record := by
        rw [Array.getElem_toList]
        have getEq := Array.getElem?_eq_getElem inBounds
        rw [arrayFound] at getEq
        exact (Option.some.inj getEq).symm
      simp only [Array.toList_set, List.getElem_set, recordAt] at entryAt
      subst entry
      unfold environmentValidAt
      simp only [Array.size_set, Bool.and_eq_true]
      have oldInvariant := wellFormed_environmentValidAt machine environment record machineValid found
      unfold environmentValidAt at oldInvariant
      simp only [Bool.and_eq_true] at oldInvariant
      refine ⟨⟨oldInvariant.1.1, ?_⟩, ?_⟩
      · rw [List.all_eq_true]
        intro binding bindingMember
        have bindingFound :=
          (hashMap_mem_toList_iff_getElem?_eq_some bindings binding.1 binding.2).mp bindingMember
        exact decide_eq_true (bindingsValid binding.1 binding.2 bindingFound)
      · rw [environmentTerminates_setParent machine environment record
          { record with bindings } inBounds arrayFound rfl]
        simpa using oldInvariant.2
    · rw [getElem_zipIdxFrom] at entryAt
      have arrayIndexBound : index < machine.environments.size := by simpa using indexBound
      rw [Array.getElem_toList] at entryAt
      rw [Array.getElem_set_ne machine.environments environment.value inBounds
        { record with bindings } (by simpa using arrayIndexBound) (Ne.symm same)] at entryAt
      have oldEntryAt : (zipIdxFrom machine.environments.toList 0)[index] = entry := by
        rw [getElem_zipIdxFrom, Array.getElem_toList]
        simpa using entryAt
      have oldMember : entry ∈ zipIdxFrom machine.environments.toList 0 := by
        rw [← oldEntryAt]
        exact List.getElem_mem oldIndexBound
      rw [environmentValidAt_setParent machine environment record { record with bindings }
        inBounds arrayFound rfl]
      exact oldAll entry oldMember
  next outOfBounds => contradiction

/-- A stable cell identity retains assignment policy while its TDZ/value state may evolve. -/
def Cell.ContinuesFrom (old next : Cell) : Prop := old.mutable = next.mutable

/-- A stable environment identity retains ancestry and all existing name-to-cell mappings. -/
def EnvironmentRecord.ContinuesFrom (old next : EnvironmentRecord) : Prop :=
  old.parent = next.parent ∧
  ∀ (name : JSString) (cell : CellId),
    old.bindings[name]? = some cell → next.bindings[name]? = some cell

/-- Execution identity continuity, independent of final machine well-formedness. Platform state,
trace, fuel, cell state, and newly appended bindings remain intentionally unconstrained. -/
def ContinuesFrom (old next : Machine P) : Prop :=
  old.heap.ContinuesFrom next.heap ∧
  old.cells.size ≤ next.cells.size ∧
  old.environments.size ≤ next.environments.size ∧
  old.intrinsics = next.intrinsics ∧
  old.currentEnv = next.currentEnv ∧
  (∀ (index : Nat) (oldCell : Cell), old.cells[index]? = some oldCell →
    ∃ nextCell, next.cells[index]? = some nextCell ∧ Cell.ContinuesFrom oldCell nextCell) ∧
  ∀ (index : Nat) (oldEnvironment : EnvironmentRecord),
    old.environments[index]? = some oldEnvironment →
    ∃ nextEnvironment, next.environments[index]? = some nextEnvironment ∧
      EnvironmentRecord.ContinuesFrom oldEnvironment nextEnvironment

/-- Machine continuity is reflexive. -/
theorem continuesFrom_refl (machine : Machine P) : machine.ContinuesFrom machine :=
  ⟨Heap.continuesFrom_refl _, Nat.le_refl _, Nat.le_refl _, rfl, rfl,
    fun _ cell found => ⟨cell, found, rfl⟩,
    fun _ environment found => ⟨environment, found, rfl, fun _ _ binding => binding⟩⟩

/-- Machine continuity composes. -/
theorem continuesFrom_trans (first second third : Machine P)
    (left : first.ContinuesFrom second) (right : second.ContinuesFrom third) :
    first.ContinuesFrom third := by
  refine ⟨Heap.continuesFrom_trans _ _ _ left.1 right.1,
    Nat.le_trans left.2.1 right.2.1,
    Nat.le_trans left.2.2.1 right.2.2.1,
    left.2.2.2.1.trans right.2.2.2.1,
    left.2.2.2.2.1.trans right.2.2.2.2.1,
    ?_, ?_⟩
  · intro index oldCell found
    obtain ⟨middleCell, middleFound, firstContinued⟩ := left.2.2.2.2.2.1 index oldCell found
    obtain ⟨finalCell, finalFound, secondContinued⟩ :=
      right.2.2.2.2.2.1 index middleCell middleFound
    exact ⟨finalCell, finalFound, firstContinued.trans secondContinued⟩
  · intro index oldEnvironment found
    obtain ⟨middleEnvironment, middleFound, firstParent, firstBindings⟩ :=
      left.2.2.2.2.2.2 index oldEnvironment found
    obtain ⟨finalEnvironment, finalFound, secondParent, secondBindings⟩ :=
      right.2.2.2.2.2.2 index middleEnvironment middleFound
    exact ⟨finalEnvironment, finalFound, firstParent.trans secondParent,
      fun name cell binding => secondBindings name cell (firstBindings name cell binding)⟩

private theorem cellsContinue_refl (machine : Machine P) :
    ∀ (index : Nat) (oldCell : Cell), machine.cells[index]? = some oldCell →
      ∃ nextCell, machine.cells[index]? = some nextCell ∧ Cell.ContinuesFrom oldCell nextCell :=
  fun _ cell found => ⟨cell, found, rfl⟩

private theorem environmentsContinue_refl (machine : Machine P) :
    ∀ (index : Nat) (oldEnvironment : EnvironmentRecord),
      machine.environments[index]? = some oldEnvironment →
      ∃ nextEnvironment, machine.environments[index]? = some nextEnvironment ∧
        EnvironmentRecord.ContinuesFrom oldEnvironment nextEnvironment :=
  fun _ environment found => ⟨environment, found, rfl, fun _ _ binding => binding⟩

private theorem cellsContinue_set (machine : Machine P) (target : CellId) (cell : Cell)
    (inBounds : target.value < machine.cells.size)
    (mutablePreserved : ∀ oldCell, machine.cells[target.value]? = some oldCell →
      oldCell.mutable = cell.mutable) :
    ∀ (index : Nat) (oldCell : Cell), machine.cells[index]? = some oldCell →
      ∃ nextCell, (machine.cells.set target.value cell inBounds)[index]? = some nextCell ∧
        Cell.ContinuesFrom oldCell nextCell := by
  intro index oldCell found
  rw [Array.getElem?_set]
  by_cases same : target.value = index
  · rw [if_pos same]
    subst index
    exact ⟨cell, rfl, mutablePreserved oldCell found⟩
  · rw [if_neg same]
    exact ⟨oldCell, found, rfl⟩

private theorem environmentsContinue_set (machine : Machine P) (target : EnvId)
    (record : EnvironmentRecord) (inBounds : target.value < machine.environments.size)
    (recordPreserved : ∀ oldRecord, machine.environments[target.value]? = some oldRecord →
      EnvironmentRecord.ContinuesFrom oldRecord record) :
    ∀ (index : Nat) (oldRecord : EnvironmentRecord),
      machine.environments[index]? = some oldRecord →
      ∃ nextRecord,
        (machine.environments.set target.value record inBounds)[index]? = some nextRecord ∧
          EnvironmentRecord.ContinuesFrom oldRecord nextRecord := by
  intro index oldRecord found
  rw [Array.getElem?_set]
  by_cases same : target.value = index
  · rw [if_pos same]
    subst index
    exact ⟨record, rfl, recordPreserved oldRecord found⟩
  · rw [if_neg same]
    exact ⟨oldRecord, found, rfl, fun _ _ binding => binding⟩

private theorem cellsContinue_push (machine : Machine P) (cell : Cell) :
    ∀ (index : Nat) (oldCell : Cell), machine.cells[index]? = some oldCell →
      ∃ nextCell, (machine.cells.push cell)[index]? = some nextCell ∧
        Cell.ContinuesFrom oldCell nextCell := by
  intro index oldCell found
  have inBounds := (Array.getElem?_eq_some_iff.mp found).choose
  exact ⟨oldCell, by simpa [Array.getElem?_push, Nat.ne_of_lt inBounds] using found, rfl⟩

private theorem environmentsContinue_push (machine : Machine P) (record : EnvironmentRecord) :
    ∀ (index : Nat) (oldRecord : EnvironmentRecord),
      machine.environments[index]? = some oldRecord →
      ∃ nextRecord, (machine.environments.push record)[index]? = some nextRecord ∧
        EnvironmentRecord.ContinuesFrom oldRecord nextRecord := by
  intro index oldRecord found
  have inBounds := (Array.getElem?_eq_some_iff.mp found).choose
  exact ⟨oldRecord, by simpa [Array.getElem?_push, Nat.ne_of_lt inBounds] using found,
    rfl, fun _ _ binding => binding⟩

/-- Successful cell replacement preserves execution identity continuity. -/
theorem setCell_continuesFrom (machine next : Machine P) (id : CellId) (cell : Cell)
    (mutablePreserved : ∀ oldCell, machine.cells[id.value]? = some oldCell →
      oldCell.mutable = cell.mutable)
    (updated : machine.setCell id cell = .ok next) : machine.ContinuesFrom next := by
  unfold setCell at updated
  split at updated
  next inBounds =>
    simp only [Except.ok.injEq] at updated
    subst next
    exact ⟨Heap.continuesFrom_refl _, by simp, Nat.le_refl _, rfl, rfl,
      cellsContinue_set machine id cell inBounds mutablePreserved,
      environmentsContinue_refl machine⟩
  next outOfBounds => contradiction

/-- Successful environment replacement preserves execution identity continuity. -/
theorem setEnvironment_continuesFrom (machine next : Machine P) (id : EnvId)
    (record : EnvironmentRecord)
    (recordPreserved : ∀ oldRecord, machine.environments[id.value]? = some oldRecord →
      EnvironmentRecord.ContinuesFrom oldRecord record)
    (updated : machine.setEnvironment id record = .ok next) :
    machine.ContinuesFrom next := by
  unfold setEnvironment at updated
  split at updated
  next inBounds =>
    simp only [Except.ok.injEq] at updated
    subst next
    exact ⟨Heap.continuesFrom_refl _, Nat.le_refl _, by simp, rfl, rfl,
      cellsContinue_refl machine,
      environmentsContinue_set machine id record inBounds recordPreserved⟩
  next outOfBounds => contradiction

/-- Environment replacement leaves every allocated cell identity unchanged. -/
theorem setEnvironment_preserves_validCellId (machine next : Machine P) (environment : EnvId)
    (record : EnvironmentRecord) (cell : CellId)
    (updated : machine.setEnvironment environment record = .ok next) :
    machine.ValidCellId cell ↔ next.ValidCellId cell := by
  unfold setEnvironment at updated
  split at updated
  next inBounds =>
    simp only [Except.ok.injEq] at updated
    subst next
    rfl
  next outOfBounds => contradiction

/-- Cell append preserves execution identity continuity. -/
theorem allocateCell_continuesFrom (machine : Machine P) (cell : Cell) :
    machine.ContinuesFrom (machine.allocateCell cell).2 := by
  exact ⟨Heap.continuesFrom_refl _, by simp [allocateCell], Nat.le_refl _, rfl, rfl,
    cellsContinue_push machine cell, environmentsContinue_refl machine⟩

/-- Successful environment append preserves execution identity continuity. -/
theorem allocateEnvironment_continuesFrom (machine next : Machine P)
    (parent : Option EnvId) (fresh : EnvId)
    (allocated : machine.allocateEnvironment parent = .ok (fresh, next)) :
    machine.ContinuesFrom next := by
  cases parent with
  | none =>
      simp [allocateEnvironment] at allocated
      obtain ⟨rfl, rfl⟩ := allocated
      exact ⟨Heap.continuesFrom_refl _, Nat.le_refl _, by simp, rfl, rfl,
        cellsContinue_refl machine,
        environmentsContinue_push machine ⟨none, Std.HashMap.empty⟩⟩
  | some parent =>
      cases found : machine.getEnvironment parent with
      | error fault => simp [allocateEnvironment, found] at allocated
      | ok record =>
          simp [allocateEnvironment, found] at allocated
          obtain ⟨rfl, rfl⟩ := allocated
          exact ⟨Heap.continuesFrom_refl _, Nat.le_refl _, by simp, rfl, rfl,
            cellsContinue_refl machine,
            environmentsContinue_push machine ⟨some parent, Std.HashMap.empty⟩⟩

/-- Successful environment append returns an allocated environment identity. -/
theorem allocateEnvironment_valid (machine next : Machine P) (parent : Option EnvId)
    (fresh : EnvId) (allocated : machine.allocateEnvironment parent = .ok (fresh, next)) :
    next.ValidEnvId fresh := by
  obtain ⟨record, found⟩ := allocateEnvironment_getEnvironment machine next parent fresh allocated
  exact getEnvironment_valid next fresh record found

/-- Entering and then restoring the original current environment exposes the action's continuity
as continuity from the original machine. -/
theorem restoreEnvironment_continuesFrom (initial entered final restored : Machine P)
    (environment : EnvId) (enteredBy : initial.switchEnvironment environment = .ok entered)
    (continued : entered.ContinuesFrom final)
    (restoredBy : final.switchEnvironment initial.currentEnv = .ok restored) :
    initial.ContinuesFrom restored := by
  unfold switchEnvironment at enteredBy restoredBy
  cases enteredFound : initial.getEnvironment environment with
  | error fault => simp [enteredFound] at enteredBy
  | ok record =>
      simp [enteredFound] at enteredBy
      subst entered
      cases restoredFound : final.getEnvironment initial.currentEnv with
      | error fault => simp [restoredFound] at restoredBy
      | ok oldRecord =>
          simp [restoredFound] at restoredBy
          subst restored
          exact ⟨continued.1, continued.2.1, continued.2.2.1, continued.2.2.2.1, rfl,
            continued.2.2.2.2.2.1, continued.2.2.2.2.2.2⟩

/-- A heap commit establishes machine continuity when the heap update does. -/
theorem setHeap_continuesFrom (machine : Machine P) (heap : Heap)
    (preserved : machine.heap.ContinuesFrom heap) :
    machine.ContinuesFrom (machine.setHeap heap) :=
  ⟨preserved, Nat.le_refl _, Nat.le_refl _, rfl, rfl,
    cellsContinue_refl machine, environmentsContinue_refl machine⟩

/-- The stronger no-function-allocation heap relation discharges continuity for valid commits. -/
theorem setHeap_continuesFrom_machineReferences (machine : Machine P) (heap : Heap)
    (machineValid : machine.WellFormed) (heapValid : heap.WellFormed)
    (preserved : machine.heap.MachineReferencesPreserved heap) :
    machine.ContinuesFrom (machine.setHeap heap) :=
  machine.setHeap_continuesFrom heap
    (preserved.continuesFrom_of_wellFormed (wellFormed_heap machine machineValid) heapValid)

private theorem environmentTerminates_executionState (machine : Machine P)
    (platform : P.State) (reverseTrace : List TraceEvent) (remaining fuel : Nat) (id : EnvId) :
    ({ machine with platform, reverseTrace, fuel }).environmentTerminates remaining id =
      machine.environmentTerminates remaining id := by
  induction remaining generalizing id with
  | zero => rfl
  | succ remaining ih =>
      unfold environmentTerminates
      cases found : machine.environments[id.value]? with
      | none => rfl
      | some environment =>
          cases parentEq : environment.parent with
          | none => simp [parentEq]
          | some parent => simpa [parentEq] using ih parent

private theorem executionState_preserves_wellFormed (machine : Machine P)
    (platform : P.State) (reverseTrace : List TraceEvent) (fuel : Nat)
    (valid : machine.WellFormed) :
    ({ machine with platform, reverseTrace, fuel }).WellFormed := by
  unfold WellFormed isWellFormed at valid ⊢
  simp only [Bool.and_eq_true] at valid ⊢
  refine ⟨⟨⟨⟨⟨valid.1.1.1.1.1, valid.1.1.1.1.2⟩, valid.1.1.1.2⟩, ?_⟩,
    valid.1.2⟩, valid.2⟩
  rw [List.all_eq_true]
  have environmentsValid := List.all_eq_true.mp valid.1.1.2
  intro entry member
  unfold environmentValidAt
  rw [environmentTerminates_executionState]
  exact environmentsValid entry member

/-- Event emission changes only trace state. -/
theorem emit_continuesFrom (machine : Machine P) (event : TraceEvent) :
    machine.ContinuesFrom (machine.emit event) :=
  ⟨Heap.continuesFrom_refl _, Nat.le_refl _, Nat.le_refl _, rfl, rfl,
    cellsContinue_refl machine, environmentsContinue_refl machine⟩

/-- Event emission does not affect any machine invariant field. -/
theorem emit_preserves_wellFormed (machine : Machine P) (event : TraceEvent)
    (valid : machine.WellFormed) : (machine.emit event).WellFormed := by
  exact executionState_preserves_wellFormed machine machine.platform
    (event :: machine.reverseTrace) machine.fuel valid

/-- Successful fuel consumption changes only fuel state. -/
theorem consumeFuel_continuesFrom (machine next : Machine P)
    (consumed : machine.consumeFuel = some next) : machine.ContinuesFrom next := by
  unfold consumeFuel at consumed
  cases fuelEq : machine.fuel with
  | zero => simp [fuelEq] at consumed
  | succ fuel =>
      simp only [fuelEq, Option.some.injEq] at consumed
      subst next
      exact ⟨Heap.continuesFrom_refl _, Nat.le_refl _, Nat.le_refl _, rfl, rfl,
        cellsContinue_refl machine, environmentsContinue_refl machine⟩

/-- Successful fuel consumption does not affect any machine invariant field. -/
theorem consumeFuel_preserves_wellFormed (machine next : Machine P)
    (valid : machine.WellFormed) (consumed : machine.consumeFuel = some next) :
    next.WellFormed := by
  unfold consumeFuel at consumed
  cases fuelEq : machine.fuel with
  | zero => simp [fuelEq] at consumed
  | succ fuel =>
      simp only [fuelEq, Option.some.injEq] at consumed
      subst next
      exact executionState_preserves_wellFormed machine machine.platform machine.reverseTrace fuel valid

private theorem environmentTerminates_setHeap (machine : Machine P) (heap : Heap)
    (fuel : Nat) (id : EnvId) :
    ({ machine with heap := heap }).environmentTerminates fuel id =
      machine.environmentTerminates fuel id := by
  induction fuel generalizing id with
  | zero => rfl
  | succ fuel ih =>
      unfold environmentTerminates
      cases found : machine.environments[id.value]? with
      | none => simp
      | some environment =>
          cases parentEq : environment.parent with
          | none => simp [parentEq]
          | some parent => simpa [parentEq] using ih parent

private theorem environmentValidAt_setHeap (machine : Machine P) (heap : Heap)
    (entry : EnvironmentRecord × Nat) :
    ({ machine with heap := heap }).environmentValidAt entry =
      machine.environmentValidAt entry := by
  unfold environmentValidAt
  rw [environmentTerminates_setHeap]

/-- Committing a well-formed, machine-reference-preserving heap retains complete machine validity. -/
theorem setHeap_preserves_wellFormed (machine : Machine P) (heap : Heap)
    (valid : machine.WellFormed) (heapValid : heap.WellFormed)
    (preserved : machine.heap.MachineReferencesPreserved heap) :
    (machine.setHeap heap).WellFormed := by
  unfold WellFormed isWellFormed at valid ⊢
  simp only [setHeap]
  simp only [Bool.and_eq_true] at valid ⊢
  refine ⟨⟨⟨⟨⟨heapValid, valid.1.1.1.1.2⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [List.all_eq_true] at valid ⊢
    intro cell member
    have cellValidOld := valid.1.1.1.2 cell member
    cases cell with
    | mk state mutable =>
        cases state with
        | uninitialized => trivial
        | initialized value =>
            cases value with
            | primitive primitive => trivial
            | object ref =>
                unfold cellValid Heap.valueValid Heap.size at cellValidOld ⊢
                simp only at cellValidOld ⊢
                have sizeMono := preserved.1
                change machine.heap.objects.size ≤ heap.objects.size at sizeMono
                have oldBound := of_decide_eq_true cellValidOld
                exact decide_eq_true (Nat.lt_of_lt_of_le oldBound sizeMono)
  · rw [List.all_eq_true]
    have environmentsValid := List.all_eq_true.mp valid.1.1.2
    intro entry member
    rw [environmentValidAt_setHeap]
    exact environmentsValid entry member
  · unfold realmValid at valid ⊢
    cases intrinsicsEq : machine.intrinsics with
    | none => rfl
    | some intrinsics =>
        simp only [intrinsicsEq, Option.all_some] at valid ⊢
        exact RealmIntrinsics.intrinsicsRefsValid_machineReferences intrinsics machine.heap heap
          valid.1.2 preserved
  · rw [preserved.2.1]
    exact valid.2

/-- A continuous valid heap commit preserves the machine when every final captured environment is
allocated in the unchanged environment arena. -/
theorem setHeap_preserves_wellFormed_continuous (machine : Machine P) (heap : Heap)
    (valid : machine.WellFormed) (heapValid : heap.WellFormed)
    (continued : machine.heap.ContinuesFrom heap)
    (functionsValid : heap.functionEnvironments.all fun environment =>
      environment.value < machine.environments.size) :
    (machine.setHeap heap).WellFormed := by
  unfold WellFormed isWellFormed at valid ⊢
  simp only [setHeap]
  simp only [Bool.and_eq_true] at valid ⊢
  refine ⟨⟨⟨⟨⟨heapValid, valid.1.1.1.1.2⟩, ?_⟩, ?_⟩, ?_⟩, functionsValid⟩
  · rw [List.all_eq_true] at valid ⊢
    intro cell member
    have oldValid := valid.1.1.1.2 cell member
    cases cell with
    | mk state mutable =>
        cases state with
        | uninitialized => trivial
        | initialized value =>
            exact continued.preserves_valueValid value (by simpa [cellValid] using oldValid)
  · rw [List.all_eq_true]
    have environmentsValid := List.all_eq_true.mp valid.1.1.2
    intro entry member
    rw [environmentValidAt_setHeap]
    exact environmentsValid entry member
  · unfold realmValid at valid ⊢
    cases intrinsicsEq : machine.intrinsics with
    | none => rfl
    | some intrinsics =>
        simp only [intrinsicsEq, Option.all_some] at valid ⊢
        exact RealmIntrinsics.intrinsicsRefsValid_continuesFrom intrinsics machine.heap heap
          valid.1.2 continued

/-- Function allocation commits to a valid machine when its captured environment is allocated. -/
theorem allocateFunction_preserves_machine (machine : Machine P) (heap : Heap)
    (environment : EnvId) (kind : FunctionKind) (constructible : Bool)
    (prototype homeObject : Option RefId) (constructorMode : ConstructorMode)
    (lexicalThis : Option Value) (ref : RefId) (valid : machine.WellFormed)
    (environmentValid : machine.ValidEnvId environment)
    (allocated : machine.heap.allocateFunction environment kind constructible prototype homeObject
      constructorMode lexicalThis = .ok (ref, heap)) :
    (machine.setHeap heap).WellFormed ∧ machine.ContinuesFrom (machine.setHeap heap) := by
  unfold ValidEnvId at environmentValid
  have heapValid := Heap.allocateFunction_preserves_wellFormed machine.heap heap environment kind
    constructible prototype homeObject constructorMode lexicalThis ref (wellFormed_heap machine valid)
    allocated
  have continued := Heap.allocateFunction_continuesFrom machine.heap heap environment kind
    constructible prototype homeObject constructorMode lexicalThis ref allocated
  have functionEnvironments := Heap.allocateFunction_functionEnvironments machine.heap heap
    environment kind constructible prototype homeObject constructorMode lexicalThis ref allocated
  have oldFunctions : machine.heap.functionEnvironments.all (fun captured =>
      captured.value < machine.environments.size) = true := by
    unfold WellFormed isWellFormed at valid
    simp only [Bool.and_eq_true] at valid
    exact valid.2
  have finalFunctions : heap.functionEnvironments.all (fun captured =>
      captured.value < machine.environments.size) = true := by
    rw [functionEnvironments, List.all_append]
    rw [Bool.and_eq_true]
    refine ⟨oldFunctions, ?_⟩
    simpa using decide_eq_true environmentValid
  exact ⟨setHeap_preserves_wellFormed_continuous machine heap valid heapValid continued finalFunctions,
    machine.setHeap_continuesFrom heap continued⟩

/-- Constructor-pair allocation commits to a valid machine when its captured environment is
allocated. -/
theorem allocateConstructorPair_preserves_machine (machine : Machine P) (heap : Heap)
    (environment : EnvId) (functionPrototype objectPrototype : Option RefId)
    (classConstructor : Bool) (constructorMode : ConstructorMode) (constructor prototype : RefId)
    (valid : machine.WellFormed) (environmentValid : machine.ValidEnvId environment)
    (allocated : machine.heap.allocateConstructorPair environment functionPrototype objectPrototype
      classConstructor constructorMode = .ok (constructor, prototype, heap)) :
    (machine.setHeap heap).WellFormed ∧ machine.ContinuesFrom (machine.setHeap heap) := by
  unfold ValidEnvId at environmentValid
  have heapValid := Heap.allocateConstructorPair_preserves_wellFormed machine.heap heap environment
    functionPrototype objectPrototype classConstructor constructorMode constructor prototype
    (wellFormed_heap machine valid) allocated
  have continued := Heap.allocateConstructorPair_continuesFrom machine.heap heap environment
    functionPrototype objectPrototype classConstructor constructorMode constructor prototype allocated
  have functionEnvironments := Heap.allocateConstructorPair_functionEnvironments machine.heap heap
    environment functionPrototype objectPrototype classConstructor constructorMode constructor prototype
    allocated
  have oldFunctions : machine.heap.functionEnvironments.all (fun captured =>
      captured.value < machine.environments.size) = true := by
    unfold WellFormed isWellFormed at valid
    simp only [Bool.and_eq_true] at valid
    exact valid.2
  have finalFunctions : heap.functionEnvironments.all (fun captured =>
      captured.value < machine.environments.size) = true := by
    rw [functionEnvironments, List.all_append]
    rw [Bool.and_eq_true]
    refine ⟨oldFunctions, ?_⟩
    simpa using decide_eq_true environmentValid
  exact ⟨setHeap_preserves_wellFormed_continuous machine heap valid heapValid continued finalFunctions,
    machine.setHeap_continuesFrom heap continued⟩

/-- A fresh machine satisfies heap, arena, and captured-environment validity. -/
theorem initial_wellFormed (P : Platform) (fuel : Nat) :
    (Machine.initial P fuel).WellFormed := by
  have heapValid : Heap.empty.isWellFormed = true := Heap.empty_wellFormed
  simp only [WellFormed, isWellFormed, initial]
  rw [heapValid]
  simp [environmentValidAt, environmentTerminates, Heap.functionEnvironments,
    Heap.functionSlotList, Heap.empty, realmValid]
  intro name cell member
  have found :=
    (hashMap_mem_toList_iff_getElem?_eq_some (Std.HashMap.empty : Std.HashMap JSString CellId)
      name cell).mp member
  simp at found

end Machine
end TSLean.JS
