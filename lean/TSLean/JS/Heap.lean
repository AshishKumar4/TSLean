import Std.Data.HashMap
import TSLean.JS.Descriptor
import TSLean.JS.PropertyKey

namespace TSLean.JS

private structure StoredProperty where
  descriptor : PropertyDescriptor
  orderPosition : Option Nat

/-- An ordinary property's descriptor store and bounded key-order metadata.

The constructor is private. Descriptors live only in the hash table; arrays retain non-index
insertion order with tombstones. Lookup, update, and insertion are expected O(1); deletion is
amortized O(1) because compaction occasionally rebuilds one order partition.
`ownKeys` is O(n log n) because integer indices are sorted at enumeration. When an order array has
at least 64 slots and more than half are tombstones, it is compacted and map positions are rebuilt. -/
structure OrderedProps where
  private mk ::
  entries : Std.HashMap PropertyKey StoredProperty
  stringOrder : Array (Option JSString)
  symbolOrder : Array (Option SymbolId)
  stringTombstones : Nat
  symbolTombstones : Nat

namespace OrderedProps

/-- Minimum metadata size at which tombstone-ratio compaction runs. -/
def compactionThreshold : Nat := 64

/-- An empty valid property collection. -/
def empty : OrderedProps := .mk Std.HashMap.emptyWithCapacity #[] #[] 0 0

/-- Number of live own properties. -/
def size (properties : OrderedProps) : Nat := properties.entries.size

/-- Current string and symbol order-array sizes, exposed for invariant diagnostics. -/
def metadataSlots (properties : OrderedProps) : Nat × Nat :=
  (properties.stringOrder.size, properties.symbolOrder.size)

/-- All live complete descriptors, without exposing mutable representation metadata. -/
def descriptors (properties : OrderedProps) : List PropertyDescriptor :=
  properties.entries.toList.map (·.2.descriptor)

/-- Looks up an own property using lawful UTF-16 or symbol-identity hashing. -/
def lookup (properties : OrderedProps) (key : PropertyKey) : Option PropertyDescriptor :=
  (properties.entries.get? key).map (·.descriptor)

private def shouldCompact (slots tombstones : Nat) : Bool :=
  compactionThreshold ≤ slots && slots < tombstones * 2

private def compactStrings
    (entries : Std.HashMap PropertyKey StoredProperty) (order : Array (Option JSString)) :
    Std.HashMap PropertyKey StoredProperty × Array (Option JSString) :=
  order.foldl (fun state slot =>
    match slot with
    | none => state
    | some key =>
        match state.1.get? (.string key) with
        | none => state
        | some stored =>
            let position := state.2.size
            (state.1.insert (.string key) { stored with orderPosition := some position },
              state.2.push (some key))) (entries, #[])

private def compactSymbols
    (entries : Std.HashMap PropertyKey StoredProperty) (order : Array (Option SymbolId)) :
    Std.HashMap PropertyKey StoredProperty × Array (Option SymbolId) :=
  order.foldl (fun state slot =>
    match slot with
    | none => state
    | some key =>
        match state.1.get? (.symbol key) with
        | none => state
        | some stored =>
            let position := state.2.size
            (state.1.insert (.symbol key) { stored with orderPosition := some position },
              state.2.push (some key))) (entries, #[])

/-- Inserts or updates a property. Updates preserve their existing position. -/
private def insert (properties : OrderedProps) (key : PropertyKey)
    (descriptor : PropertyDescriptor) : OrderedProps :=
  match properties.entries.get? key with
  | some stored =>
      .mk (properties.entries.insert key { stored with descriptor })
        properties.stringOrder properties.symbolOrder
        properties.stringTombstones properties.symbolTombstones
  | none =>
      match key with
      | .string stringKey =>
          match PropertyKey.arrayIndex? stringKey with
          | some _ =>
              .mk (properties.entries.insert key ⟨descriptor, none⟩)
                properties.stringOrder properties.symbolOrder
                properties.stringTombstones properties.symbolTombstones
          | none =>
              let position := properties.stringOrder.size
              let entries := properties.entries.insert key ⟨descriptor, some position⟩
              let order := properties.stringOrder.push (some stringKey)
              if shouldCompact order.size properties.stringTombstones then
                let compacted := compactStrings entries order
                .mk compacted.1 compacted.2 properties.symbolOrder 0 properties.symbolTombstones
              else
                .mk entries order properties.symbolOrder
                  properties.stringTombstones properties.symbolTombstones
      | .symbol symbolKey =>
          let position := properties.symbolOrder.size
          let entries := properties.entries.insert key ⟨descriptor, some position⟩
          let order := properties.symbolOrder.push (some symbolKey)
          if shouldCompact order.size properties.symbolTombstones then
            let compacted := compactSymbols entries order
            .mk compacted.1 properties.stringOrder compacted.2 properties.stringTombstones 0
          else
            .mk entries properties.stringOrder order
              properties.stringTombstones properties.symbolTombstones

private def tombstone (order : Array (Option α)) (position : Nat) : Array (Option α) :=
  if inBounds : position < order.size then order.set position none inBounds else order

private def deleteString
    (properties : OrderedProps) (entries : Std.HashMap PropertyKey StoredProperty)
    (position : Nat) : OrderedProps :=
  let order := tombstone properties.stringOrder position
  let tombstones := properties.stringTombstones + 1
  if shouldCompact order.size tombstones then
    let compacted := compactStrings entries order
    .mk compacted.1 compacted.2 properties.symbolOrder 0 properties.symbolTombstones
  else
    .mk entries order properties.symbolOrder tombstones properties.symbolTombstones

private def deleteSymbol
    (properties : OrderedProps) (entries : Std.HashMap PropertyKey StoredProperty)
    (position : Nat) : OrderedProps :=
  let order := tombstone properties.symbolOrder position
  let tombstones := properties.symbolTombstones + 1
  if shouldCompact order.size tombstones then
    let compacted := compactSymbols entries order
    .mk compacted.1 properties.stringOrder compacted.2 properties.stringTombstones 0
  else
    .mk entries properties.stringOrder order properties.stringTombstones tombstones

/-- Deletes a property. Reinserting a non-index key appends after current keys in its class. -/
private def delete (properties : OrderedProps) (key : PropertyKey) : OrderedProps :=
  match properties.entries.get? key with
  | none => properties
  | some stored =>
      let entries := properties.entries.erase key
      match key, stored.orderPosition with
      | .string stringKey, some position =>
          if (PropertyKey.arrayIndex? stringKey).isSome then
            .mk entries properties.stringOrder properties.symbolOrder
              properties.stringTombstones properties.symbolTombstones
          else deleteString properties entries position
      | .symbol _, some position => deleteSymbol properties entries position
      | _, none =>
          .mk entries properties.stringOrder properties.symbolOrder
            properties.stringTombstones properties.symbolTombstones

private def orderedStrings (properties : OrderedProps) : List PropertyKey :=
  properties.stringOrder.foldl (fun keys slot =>
    match slot with
    | some key =>
        if properties.entries.contains (.string key) then .string key :: keys else keys
    | none => keys) [] |>.reverse

private def orderedSymbols (properties : OrderedProps) : List PropertyKey :=
  properties.symbolOrder.foldl (fun keys slot =>
    match slot with
    | some key =>
        if properties.entries.contains (.symbol key) then .symbol key :: keys else keys
    | none => keys) [] |>.reverse

private def sortedIndices (properties : OrderedProps) : List PropertyKey :=
  properties.entries.toList.filterMap (fun entry =>
    match entry.1 with
    | .string key => PropertyKey.arrayIndex? key
    | .symbol _ => none)
  |>.mergeSort (· < ·)
  |>.map (fun index => .string (PropertyKey.arrayIndexString index))

/-- Returns indices ascending, then strings and symbols in insertion order. -/
def ownKeys (properties : OrderedProps) : List PropertyKey :=
  sortedIndices properties ++ orderedStrings properties ++ orderedSymbols properties

private def tombstoneCount (order : Array (Option α)) : Nat :=
  order.foldl (fun count slot => if slot.isNone then count + 1 else count) 0

private def entryMetadataConsistent (properties : OrderedProps)
    (entry : PropertyKey × StoredProperty) : Bool :=
  match entry.1 with
  | .string key =>
      match PropertyKey.arrayIndex? key with
      | some _ => entry.2.orderPosition.isNone
      | none =>
          match entry.2.orderPosition with
          | none => false
          | some position => properties.stringOrder[position]? == some (some key)
  | .symbol key =>
      match entry.2.orderPosition with
      | none => false
      | some position => properties.symbolOrder[position]? == some (some key)

private def stringSlotConsistent (properties : OrderedProps)
    (slot : Option JSString × Nat) : Bool :=
  match slot.1 with
  | none => true
  | some key =>
      match properties.entries.get? (.string key) with
      | none => false
      | some stored =>
          (PropertyKey.arrayIndex? key).isNone && stored.orderPosition == some slot.2

private def symbolSlotConsistent (properties : OrderedProps)
    (slot : Option SymbolId × Nat) : Bool :=
  match slot.1 with
  | none => true
  | some key =>
      match properties.entries.get? (.symbol key) with
      | none => false
      | some stored => stored.orderPosition == some slot.2

private def occupiedStrings (properties : OrderedProps) : List JSString :=
  properties.stringOrder.toList.filterMap id

private def occupiedSymbols (properties : OrderedProps) : List SymbolId :=
  properties.symbolOrder.toList.filterMap id

/-- Exact bidirectional agreement between map entries and occupied order slots. -/
def metadataConsistent (properties : OrderedProps) : Bool :=
  properties.entries.toList.all (entryMetadataConsistent properties) &&
  properties.stringOrder.zipIdx.all (stringSlotConsistent properties) &&
  properties.symbolOrder.zipIdx.all (symbolSlotConsistent properties)

/-- Executable complete observable and metadata consistency check. -/
private def invariantChecks (properties : OrderedProps) : List Bool :=
  [properties.metadataConsistent,
    decide (occupiedStrings properties).Nodup,
    decide (occupiedSymbols properties).Nodup,
    decide properties.ownKeys.Nodup,
    properties.ownKeys.length == properties.size,
    tombstoneCount properties.stringOrder == properties.stringTombstones,
    tombstoneCount properties.symbolOrder == properties.symbolTombstones,
    decide (properties.stringOrder.size < compactionThreshold ∨
      properties.stringTombstones * 2 ≤ properties.stringOrder.size),
    decide (properties.symbolOrder.size < compactionThreshold ∨
      properties.symbolTombstones * 2 ≤ properties.symbolOrder.size)]

/-- Executable complete observable and metadata consistency check. -/
def isWellFormed (properties : OrderedProps) : Bool := properties.invariantChecks.all id

/-- Complete observable and metadata consistency for an ordered property collection. -/
def WellFormed (properties : OrderedProps) : Prop := properties.isWellFormed = true

/-- The empty property collection is well formed. -/
theorem empty_wellFormed : WellFormed empty := by
  simp [WellFormed, isWellFormed, invariantChecks, metadataConsistent, stringSlotConsistent,
    symbolSlotConsistent, occupiedStrings, occupiedSymbols, ownKeys, sortedIndices,
    orderedStrings, orderedSymbols, empty, size, tombstoneCount, compactionThreshold]

private def adversarialDescriptor : PropertyDescriptor :=
  .data ⟨.primitive .undefined, true, true, true⟩

private def swappedMetadata : OrderedProps :=
  let first := JSString.ofLeanString "first"
  let second := JSString.ofLeanString "second"
  .mk (Std.HashMap.emptyWithCapacity
      |>.insert (.string first) ⟨adversarialDescriptor, some 0⟩
      |>.insert (.string second) ⟨adversarialDescriptor, some 1⟩)
    #[some second, some first] #[] 0 0

private def staleMetadata : OrderedProps :=
  let live := JSString.ofLeanString "live"
  let stale := JSString.ofLeanString "stale"
  .mk (Std.HashMap.emptyWithCapacity.insert (.string live) ⟨adversarialDescriptor, some 0⟩)
    #[some live, some stale] #[] 0 0

/-- Internal adversarial check for swapped positions and stale occupied slots. -/
def adversarialMetadataRejected : Bool :=
  !swappedMetadata.isWellFormed && !staleMetadata.isWellFormed

/-- The proposition and executable ordered-property validity check coincide definitionally. -/
theorem wellFormed_iff_isWellFormed (properties : OrderedProps) :
    WellFormed properties ↔ properties.isWellFormed = true := Iff.rfl

-- TODO(theorem): prove private `insert` and `delete`, including every compaction branch, preserve
-- the exact bidirectional `WellFormed` correspondence.

end OrderedProps

/-- ECMAScript function invocation categories. -/
inductive FunctionKind where
  | ordinary
  | arrow
  | classConstructor
  deriving DecidableEq

/-- Constructor receiver initialization mode. Derived bodies require `super()` semantics. -/
inductive ConstructorMode where
  | base
  | derived
  deriving DecidableEq

/-- Data-only function metadata. Source evaluation remains outside the heap. -/
structure FunctionSlots where
  functionId : FunctionId
  environment : EnvId
  kind : FunctionKind
  constructible : Bool
  constructorMode : ConstructorMode
  homeObject : Option RefId
  lexicalThis : Option Value
  deriving DecidableEq

/-- Object categories represented by the heap. -/
inductive ObjectKind where
  | ordinary
  | function (slots : FunctionSlots)
  deriving DecidableEq

/-- Read-only heap payload for an ECMAScript object. -/
structure ObjectRecord where
  private mk ::
  properties : OrderedProps
  prototype : Option RefId
  extensible : Bool
  kind : ObjectKind

/-- A stable append-only table whose constructor is unavailable outside this module. -/
structure Heap where
  private mk ::
  objects : Array ObjectRecord
  nextFunctionId : Nat

/-- Heap validation and access failures. -/
inductive HeapFault where
  | invalidRef (ref : RefId)
  | invalidPrototype (ref : RefId)
  | cycleOrFuelExhausted
  | invalidFunctionMetadata
  deriving DecidableEq

/-- Abrupt/model errors from property definition, distinct from invariant rejection. -/
inductive DefinePropertyFault where
  | heap (fault : HeapFault)
  | syntax (fault : DescriptorSyntaxFault)
  | invalidValueRef (ref : RefId)
  | invalidAccessor (ref : RefId)
  | nonCallableAccessor (ref : RefId)
  deriving DecidableEq

namespace Heap

/-- The empty valid heap. -/
def empty : Heap := .mk #[] 0

/-- Number of stable allocated references. -/
def size (heap : Heap) : Nat := heap.objects.size

/-- Number of function metadata identities issued by this heap. -/
def functionCount (heap : Heap) : Nat := heap.nextFunctionId

/-- Reads an object or returns a typed invalid-reference fault. -/
def get? (heap : Heap) (ref : RefId) : Except HeapFault ObjectRecord :=
  match heap.objects[ref.value]? with
  | some object => .ok object
  | none => .error (.invalidRef ref)

private def validPrototype (heap : Heap) : Option RefId → Bool
  | none => true
  | some ref => ref.value < heap.size

/-- Allocates an ordinary object after validating its prototype reference. -/
def allocate (heap : Heap) (prototype : Option RefId := none) (extensible : Bool := true) :
    Except HeapFault (RefId × Heap) :=
  if validPrototype heap prototype then
    let ref := ⟨heap.objects.size⟩
    .ok (ref, .mk (heap.objects.push (.mk OrderedProps.empty prototype extensible .ordinary))
      heap.nextFunctionId)
  else
    match prototype with
    | some ref => .error (.invalidPrototype ref)
    | none => .error .cycleOrFuelExhausted

private def replace (heap : Heap) (ref : RefId) (object : ObjectRecord) : Except HeapFault Heap :=
  if inBounds : ref.value < heap.objects.size then
    .ok (.mk (heap.objects.set ref.value object inBounds) heap.nextFunctionId)
  else .error (.invalidRef ref)

private def validateValue (heap : Heap) : Value → Except DefinePropertyFault Unit
  | .object ref =>
      match heap.get? ref with
      | .ok _ => .ok ()
      | .error _ => .error (.invalidValueRef ref)
  | .primitive _ => .ok ()

private def validateAccessor (heap : Heap) : Option RefId → Except DefinePropertyFault Unit
  | none => .ok ()
  | some ref =>
      match heap.get? ref with
      | .error _ => .error (.invalidAccessor ref)
      | .ok object =>
          match object.kind with
          | .function _ => .ok ()
          | .ordinary => .error (.nonCallableAccessor ref)

/-- Returns function metadata only for a valid function object. -/
def functionSlots? (heap : Heap) (ref : RefId) : Except HeapFault (Option FunctionSlots) := do
  let object ← heap.get? ref
  match object.kind with
  | .ordinary => pure none
  | .function slots => pure (some slots)

/-- Reports whether a valid reference has the ECMAScript `[[Call]]` internal method. -/
def isCallable (heap : Heap) (ref : RefId) : Except HeapFault Bool := do
  let slots ← heap.functionSlots? ref
  pure slots.isSome

/-- Reports whether a valid reference has a construct operation. -/
def isConstructor (heap : Heap) (ref : RefId) : Except HeapFault Bool := do
  let slots ← heap.functionSlots? ref
  pure (slots.any (·.constructible))

private def validateRef (heap : Heap) (ref : RefId) : Except HeapFault Unit :=
  match heap.get? ref with
  | .ok _ => .ok ()
  | .error fault => .error fault

private def validateOptionalRef (heap : Heap) : Option RefId → Except HeapFault Unit
  | none => .ok ()
  | some ref => validateRef heap ref

/-- Reports whether a value contains no dangling heap reference. -/
def valueValid (heap : Heap) : Value → Bool
  | .object ref => ref.value < heap.size
  | .primitive _ => true

private def appendFunction (heap : Heap) (environment : EnvId) (kind : FunctionKind)
    (constructible : Bool) (prototype homeObject : Option RefId)
    (constructorMode : ConstructorMode := .base)
    (lexicalThis : Option Value := none)
    (properties : OrderedProps := OrderedProps.empty) : RefId × Heap :=
  let ref := ⟨heap.objects.size⟩
  let slots : FunctionSlots :=
    ⟨⟨heap.nextFunctionId⟩, environment, kind, constructible, constructorMode, homeObject, lexicalThis⟩
  (ref, .mk (heap.objects.push (.mk properties prototype true (.function slots)))
    (heap.nextFunctionId + 1))

/-- Allocates one validated function object. Environment validity is checked by the machine layer. -/
def allocateFunction (heap : Heap) (environment : EnvId) (kind : FunctionKind)
    (constructible : Bool) (prototype : Option RefId) (homeObject : Option RefId := none)
    (constructorMode : ConstructorMode := .base) (lexicalThis : Option Value := none) :
    Except HeapFault (RefId × Heap) :=
  match validateOptionalRef heap prototype with
  | .error fault => .error fault
  | .ok () =>
      match validateOptionalRef heap homeObject with
      | .error fault => .error fault
      | .ok () =>
          if constructorMode = .derived && (kind != .classConstructor || !constructible) then
            .error .invalidFunctionMetadata
          else
            match lexicalThis with
            | some value =>
                if !heap.valueValid value then
                  match value with
                  | .object ref => .error (.invalidRef ref)
                  | .primitive _ => .error .invalidFunctionMetadata
                else if kind != .arrow then .error .invalidFunctionMetadata
                else if constructible then .error .invalidFunctionMetadata
                else .ok (appendFunction heap environment kind constructible prototype homeObject
                  constructorMode lexicalThis)
            | none =>
                if kind = .arrow then .error .invalidFunctionMetadata
                else if kind = .classConstructor && !constructible then .error .invalidFunctionMetadata
                else .ok (appendFunction heap environment kind constructible prototype homeObject
                  constructorMode)

private def dataProperty (value : Value) (writable enumerable configurable : Bool) :
    PropertyDescriptor := .data ⟨value, writable, enumerable, configurable⟩

/-- Atomically allocates a constructible function and its fresh instance prototype. -/
def allocateConstructorPair (heap : Heap) (environment : EnvId)
    (functionPrototype objectPrototype : Option RefId) (classConstructor : Bool := false)
    (constructorMode : ConstructorMode := .base) :
    Except HeapFault (RefId × RefId × Heap) :=
  match validateOptionalRef heap functionPrototype with
  | .error fault => .error fault
  | .ok () =>
      match validateOptionalRef heap objectPrototype with
      | .error fault => .error fault
      | .ok () =>
          if constructorMode = .derived && !classConstructor then
            .error .invalidFunctionMetadata
          else
          let constructorRef : RefId := ⟨heap.objects.size⟩
          let prototypeRef : RefId := ⟨heap.objects.size + 1⟩
          let constructorProperties := OrderedProps.empty.insert
            (.string (JSString.ofLeanString "prototype"))
            (dataProperty (.object prototypeRef) (!classConstructor) false false)
          let prototypeProperties := OrderedProps.empty.insert
            (.string (JSString.ofLeanString "constructor"))
            (dataProperty (.object constructorRef) true false true)
          let kind := if classConstructor then FunctionKind.classConstructor else FunctionKind.ordinary
          let slots : FunctionSlots :=
            ⟨⟨heap.nextFunctionId⟩, environment, kind, true, constructorMode, none, none⟩
          let objects := heap.objects
            |>.push (.mk constructorProperties functionPrototype true (.function slots))
            |>.push (.mk prototypeProperties objectPrototype true .ordinary)
          .ok (constructorRef, prototypeRef, .mk objects (heap.nextFunctionId + 1))

private def validateDescriptorReferences (heap : Heap) (update : DescriptorUpdate) :
    Except DefinePropertyFault Unit := do
  match update.value with
  | .present value => validateValue heap value
  | .absent => pure ()
  match update.get with
  | .present getter => validateAccessor heap getter
  | .absent => pure ()
  match update.set with
  | .present setter => validateAccessor heap setter
  | .absent => pure ()

/-- Defines an own property through the heap's complete validation boundary. -/
def defineOwnProperty (heap : Heap) (ref : RefId) (key : PropertyKey)
    (update : DescriptorUpdate) : Except DefinePropertyFault (Bool × Heap) :=
  match heap.get? ref with
  | .error fault => .error (.heap fault)
  | .ok object =>
      match update.validateSyntax with
      | .error fault => .error (.syntax fault)
      | .ok kind =>
          match validateDescriptorReferences heap update with
          | .error fault => .error fault
          | .ok () =>
              match update.applyValidatedDescriptor
                  (object.properties.lookup key) object.extensible kind with
              | .error _ => .ok (false, heap)
              | .ok descriptor =>
                  heap.replace ref { object with properties := object.properties.insert key descriptor }
                    |>.mapError DefinePropertyFault.heap
                    |>.map fun next => (true, next)

/-- Creates a writable, enumerable, configurable own data property. -/
def createDataProperty (heap : Heap) (ref : RefId) (key : PropertyKey) (value : Value) :
    Except DefinePropertyFault (Bool × Heap) :=
  defineOwnProperty heap ref key {
    value := .present value
    writable := .present true
    enumerable := .present true
    configurable := .present true
  }

/-- Deletes a configurable own property through the validated heap boundary. -/
def deleteProperty (heap : Heap) (ref : RefId) (key : PropertyKey) :
    Except HeapFault (Bool × Heap) :=
  match heap.get? ref with
  | .error fault => .error fault
  | .ok object =>
      match object.properties.lookup key with
      | none => .ok (true, heap)
      | some (.data descriptor) =>
          if descriptor.configurable then
            heap.replace ref { object with properties := object.properties.delete key }
              |>.map fun next => (true, next)
          else .ok (false, heap)
      | some (.accessor descriptor) =>
          if descriptor.configurable then
            heap.replace ref { object with properties := object.properties.delete key }
              |>.map fun next => (true, next)
          else .ok (false, heap)

/-- Irreversibly makes an existing object nonextensible. -/
def preventExtensions (heap : Heap) (ref : RefId) : Except HeapFault Heap :=
  match heap.get? ref with
  | .error fault => .error fault
  | .ok object =>
      if object.extensible then heap.replace ref { object with extensible := false }
      else .ok heap

private def reachesWithFuel (heap : Heap) (target : RefId) : Nat → RefId → Except HeapFault Bool
  | 0, _ => .error .cycleOrFuelExhausted
  | fuel + 1, ref =>
      if ref = target then .ok true
      else
        match heap.get? ref with
        | .error _ => .error (.invalidPrototype ref)
        | .ok object =>
            match object.prototype with
            | none => .ok false
            | some parent => reachesWithFuel heap target fuel parent

/-- Implements validated `SetPrototypeOf` ordering and cycle prevention. -/
def setPrototypeOf (heap : Heap) (ref : RefId) (prototype : Option RefId) :
    Except HeapFault (Bool × Heap) :=
  match heap.get? ref with
  | .error fault => .error fault
  | .ok object =>
      if object.prototype = prototype then .ok (true, heap)
      else if !object.extensible then .ok (false, heap)
      else
        match prototype with
        | none => heap.replace ref { object with prototype := none } |>.map fun next => (true, next)
        | some parent =>
            match reachesWithFuel heap ref (heap.size + 1) parent with
            | .error fault => .error fault
            | .ok true => .ok (false, heap)
            | .ok false =>
                heap.replace ref { object with prototype := some parent } |>.map fun next => (true, next)

private def callableReferenceValid (heap : Heap) (ref : RefId) : Bool :=
  match heap.isCallable ref with
  | .ok callable => callable
  | .error _ => false

private def descriptorReferencesValid (heap : Heap) : PropertyDescriptor → Bool
  | .data descriptor => heap.valueValid descriptor.value
  | .accessor descriptor =>
      descriptor.get.all (callableReferenceValid heap) &&
      descriptor.set.all (callableReferenceValid heap)

private def functionSlotsValid (heap : Heap) (slots : FunctionSlots) : Bool :=
  slots.functionId.value < heap.functionCount &&
  slots.homeObject.all (fun home => home.value < heap.size) &&
  slots.lexicalThis.all heap.valueValid &&
  !(slots.kind = .arrow && slots.constructible) &&
  !(slots.kind = .classConstructor && !slots.constructible) &&
  !(slots.constructorMode = .derived && slots.kind != .classConstructor) &&
  (if slots.kind = .arrow then slots.lexicalThis.isSome else slots.lexicalThis.isNone)

private def objectReferencesValid (heap : Heap) (object : ObjectRecord) : Bool :=
  object.properties.isWellFormed &&
  object.properties.descriptors.all (descriptorReferencesValid heap) &&
  object.prototype.all (fun prototype => prototype.value < heap.size) &&
  match object.kind with
  | .ordinary => true
  | .function slots => functionSlotsValid heap slots

/-- Function slots in object allocation order. -/
def functionSlotList (heap : Heap) : List FunctionSlots :=
  heap.objects.toList.filterMap fun object =>
    match object.kind with
    | .ordinary => none
    | .function slots => some slots

/-- Captured environments referenced by all function objects. -/
def functionEnvironments (heap : Heap) : List EnvId :=
  heap.functionSlotList.map (·.environment)

private inductive PrototypeColor where
  | unseen
  | visiting
  | done
  deriving DecidableEq

private def finishPrototypePath (colors : Array PrototypeColor) (path : List RefId) :
    Array PrototypeColor :=
  path.foldl (fun current ref => current.setIfInBounds ref.value .done) colors

private def visitPrototype (heap : Heap) : Nat → Array PrototypeColor → List RefId → RefId →
    Option (Array PrototypeColor)
  | 0, _, _, _ => none
  | fuel + 1, colors, path, ref =>
      match colors[ref.value]?, heap.objects[ref.value]? with
      | some .done, some _ => some (finishPrototypePath colors path)
      | some .visiting, some _ => none
      | some .unseen, some object =>
          let nextColors := colors.setIfInBounds ref.value .visiting
          let nextPath := ref :: path
          match object.prototype with
          | none => some (finishPrototypePath nextColors nextPath)
          | some parent => visitPrototype heap fuel nextColors nextPath parent
      | _, _ => none

private def validatePrototypeGraphAux (heap : Heap) : Nat → Nat → Array PrototypeColor → Bool
  | 0, index, _ => index == heap.size
  | remaining + 1, index, colors =>
      match colors[index]? with
      | none => index == heap.size
      | some .done => validatePrototypeGraphAux heap remaining (index + 1) colors
      | some _ =>
          match visitPrototype heap (heap.size + 1) colors [] ⟨index⟩ with
          | none => false
          | some next => validatePrototypeGraphAux heap remaining (index + 1) next

/-- Stack-safe linear prototype graph validation. Each object changes color at most twice. -/
def prototypeGraphAcyclic (heap : Heap) : Bool :=
  validatePrototypeGraphAux heap heap.size 0 (Array.replicate heap.size .unseen)

private def functionIdsSequential : Nat → List FunctionSlots → Bool
  | _, [] => true
  | expected, slots :: rest =>
      slots.functionId.value == expected && functionIdsSequential (expected + 1) rest

/-- Executable complete heap invariant with linear function-identity and prototype-graph passes.
Captured environments are checked by `Machine.isWellFormed`. -/
def isWellFormed (heap : Heap) : Bool :=
  let slots := heap.functionSlotList
  heap.objects.toList.all (objectReferencesValid heap) &&
  functionIdsSequential 0 slots &&
  slots.length == heap.functionCount &&
  heap.prototypeGraphAcyclic

/-- Complete heap validity represented by its executable checker. -/
def WellFormed (heap : Heap) : Prop := heap.isWellFormed = true

/-- The empty heap satisfies the complete executable invariant. -/
theorem empty_wellFormed : WellFormed empty := by
  rfl

/-- Empty-heap ordinary allocation preserves the complete executable heap invariant. -/
theorem empty_allocate_wellFormed :
    match Heap.empty.allocate none true with
    | .ok (_, next) => next.WellFormed
    | .error _ => False := by
  simp [allocate, validPrototype, empty, WellFormed, isWellFormed, functionSlotList,
    objectReferencesValid, prototypeGraphAcyclic, validatePrototypeGraphAux, visitPrototype,
    finishPrototypePath, functionIdsSequential, OrderedProps.empty,
    OrderedProps.isWellFormed, OrderedProps.invariantChecks, OrderedProps.metadataConsistent,
    OrderedProps.ownKeys, OrderedProps.occupiedStrings, OrderedProps.occupiedSymbols,
    OrderedProps.sortedIndices, OrderedProps.orderedStrings, OrderedProps.orderedSymbols,
    OrderedProps.descriptors, OrderedProps.size, OrderedProps.tombstoneCount, size,
    functionCount]

/-- Empty-heap arrow allocation preserves the complete executable heap invariant. -/
theorem empty_arrow_allocate_wellFormed :
    match Heap.empty.allocateFunction ⟨0⟩ .arrow false none none .base
        (some (.primitive .undefined)) with
    | .ok (_, next) => next.WellFormed
    | .error _ => False := by
  simp [allocateFunction, validateOptionalRef, appendFunction, empty, WellFormed, isWellFormed,
    functionSlotList, objectReferencesValid, functionSlotsValid, valueValid,
    prototypeGraphAcyclic, validatePrototypeGraphAux, visitPrototype, finishPrototypePath,
    functionIdsSequential, OrderedProps.empty, OrderedProps.isWellFormed,
    OrderedProps.invariantChecks, OrderedProps.metadataConsistent, OrderedProps.ownKeys,
    OrderedProps.occupiedStrings, OrderedProps.occupiedSymbols, OrderedProps.sortedIndices,
    OrderedProps.orderedStrings, OrderedProps.orderedSymbols, OrderedProps.descriptors,
    OrderedProps.size, OrderedProps.tombstoneCount, size, functionCount]

-- TODO(theorem): prove `allocate`, successful `defineOwnProperty`, `createDataProperty`,
-- `deleteProperty`, `preventExtensions`, and `setPrototypeOf` preserve `WellFormed`.

end Heap
end TSLean.JS
