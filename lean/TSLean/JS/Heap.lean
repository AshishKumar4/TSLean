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

/-- Object categories represented by the heap. `function` is reserved for the next slice. -/
inductive ObjectKind where
  | ordinary
  | function
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

/-- Heap validation and access failures. -/
inductive HeapFault where
  | invalidRef (ref : RefId)
  | invalidPrototype (ref : RefId)
  | cycleOrFuelExhausted
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
def empty : Heap := .mk #[]

/-- Number of stable allocated references. -/
def size (heap : Heap) : Nat := heap.objects.size

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
    .ok (ref, .mk (heap.objects.push (.mk OrderedProps.empty prototype extensible .ordinary)))
  else
    match prototype with
    | some ref => .error (.invalidPrototype ref)
    | none => .error .cycleOrFuelExhausted

private def replace (heap : Heap) (ref : RefId) (object : ObjectRecord) : Except HeapFault Heap :=
  if inBounds : ref.value < heap.objects.size then
    .ok (.mk (heap.objects.set ref.value object inBounds))
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
          if object.kind = .function then .ok () else .error (.nonCallableAccessor ref)

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

private def terminatesWithFuel (heap : Heap) : Nat → RefId → Bool
  | 0, _ => false
  | fuel + 1, ref =>
      match heap.get? ref with
      | .error _ => false
      | .ok object =>
          match object.prototype with
          | none => true
          | some parent => terminatesWithFuel heap fuel parent

private def valueReferenceValid (heap : Heap) : Value → Prop
  | .object ref => ref.value < heap.size
  | .primitive _ => True

private def callableReferenceValid (heap : Heap) (ref : RefId) : Prop :=
  ∃ object, heap.get? ref = .ok object ∧ object.kind = .function

private def descriptorReferencesValid (heap : Heap) : PropertyDescriptor → Prop
  | .data descriptor => valueReferenceValid heap descriptor.value
  | .accessor descriptor =>
      (∀ ref, descriptor.get = some ref → callableReferenceValid heap ref) ∧
      (∀ ref, descriptor.set = some ref → callableReferenceValid heap ref)

private def objectReferencesValid (heap : Heap) (object : ObjectRecord) : Prop :=
  object.properties.WellFormed ∧
  (∀ descriptor ∈ object.properties.descriptors, descriptorReferencesValid heap descriptor) ∧
  object.kind = .ordinary ∧
  (∀ prototype, object.prototype = some prototype → prototype.value < heap.size)

/-- Complete ordinary-heap validity: property metadata, descriptor references, object-kind
constraints, allocated prototypes, and acyclic prototype chains. -/
def WellFormed (heap : Heap) : Prop :=
  (∀ ref object, heap.get? ref = .ok object → objectReferencesValid heap object) ∧
  (∀ ref : RefId, ref.value < heap.size → terminatesWithFuel heap (heap.size + 1) ref = true)

-- TODO(theorem): prove `allocate`, successful `defineOwnProperty`, `createDataProperty`,
-- `deleteProperty`, `preventExtensions`, and `setPrototypeOf` preserve `WellFormed`.

end Heap
end TSLean.JS
