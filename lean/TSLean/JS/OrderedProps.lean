import Std.Data.HashMap
import TSLean.JS.Descriptor
import TSLean.JS.PropertyKey

namespace TSLean.JS

private structure StoredProperty where
  descriptor : PropertyDescriptor
  orderPosition : Option Nat

private structure OrderedPropsRep where
  entries : Std.HashMap PropertyKey StoredProperty
  stringOrder : Array (Option JSString)
  symbolOrder : Array (Option SymbolId)
  stringTombstones : Nat
  symbolTombstones : Nat

/-- An ordinary property's descriptor store and bounded key-order metadata. -/
structure OrderedProps where
  private mk ::
  private rep : OrderedPropsRep

namespace OrderedProps

/-- Minimum metadata size at which tombstone-ratio compaction runs. -/
def compactionThreshold : Nat := 64

private def emptyRep : OrderedPropsRep :=
  ⟨Std.HashMap.emptyWithCapacity, #[], #[], 0, 0⟩

/-- An empty property collection. -/
def empty : OrderedProps := .mk emptyRep

/-- Number of live own properties. -/
def size (properties : OrderedProps) : Nat := properties.rep.entries.size

/-- Current string and symbol order-array sizes, exposed for invariant diagnostics. -/
def metadataSlots (properties : OrderedProps) : Nat × Nat :=
  (properties.rep.stringOrder.size, properties.rep.symbolOrder.size)

/-- All live complete descriptors, without exposing mutable representation metadata. -/
def descriptors (properties : OrderedProps) : List PropertyDescriptor :=
  properties.rep.entries.toList.map (·.2.descriptor)

/-- Reports whether every stored key satisfies a predicate. -/
def keysAll (properties : OrderedProps) (predicate : PropertyKey → Bool) : Bool :=
  properties.rep.entries.toList.all fun entry => predicate entry.1

/-- Looks up an own property using lawful UTF-16 or symbol-identity hashing. -/
def lookup (properties : OrderedProps) (key : PropertyKey) : Option PropertyDescriptor :=
  (properties.rep.entries.get? key).map (·.descriptor)

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

private def insertRep (properties : OrderedPropsRep) (key : PropertyKey)
    (descriptor : PropertyDescriptor) : OrderedPropsRep :=
  match properties.entries.get? key with
  | some stored =>
      { properties with entries := properties.entries.insert key { stored with descriptor } }
  | none =>
      match key with
      | .string stringKey =>
          match PropertyKey.arrayIndex? stringKey with
          | some _ =>
              { properties with entries := properties.entries.insert key ⟨descriptor, none⟩ }
          | none =>
              let position := properties.stringOrder.size
              let entries := properties.entries.insert key ⟨descriptor, some position⟩
              let order := properties.stringOrder.push (some stringKey)
              if shouldCompact order.size properties.stringTombstones then
                let compacted := compactStrings entries order
                ⟨compacted.1, compacted.2, properties.symbolOrder, 0,
                  properties.symbolTombstones⟩
              else
                ⟨entries, order, properties.symbolOrder, properties.stringTombstones,
                  properties.symbolTombstones⟩
      | .symbol symbolKey =>
          let position := properties.symbolOrder.size
          let entries := properties.entries.insert key ⟨descriptor, some position⟩
          let order := properties.symbolOrder.push (some symbolKey)
          if shouldCompact order.size properties.symbolTombstones then
            let compacted := compactSymbols entries order
            ⟨compacted.1, properties.stringOrder, compacted.2, properties.stringTombstones, 0⟩
          else
            ⟨entries, properties.stringOrder, order, properties.stringTombstones,
              properties.symbolTombstones⟩

/-- Inserts or updates a property. Updates preserve their existing position. -/
def insert (properties : OrderedProps) (key : PropertyKey)
    (descriptor : PropertyDescriptor) : OrderedProps :=
  .mk (insertRep properties.rep key descriptor)

private def tombstone (order : Array (Option α)) (position : Nat) : Array (Option α) :=
  if inBounds : position < order.size then order.set position none inBounds else order

private def deleteString (properties : OrderedPropsRep)
    (entries : Std.HashMap PropertyKey StoredProperty) (position : Nat) : OrderedPropsRep :=
  let order := tombstone properties.stringOrder position
  let tombstones := properties.stringTombstones + 1
  if shouldCompact order.size tombstones then
    let compacted := compactStrings entries order
    ⟨compacted.1, compacted.2, properties.symbolOrder, 0, properties.symbolTombstones⟩
  else
    ⟨entries, order, properties.symbolOrder, tombstones, properties.symbolTombstones⟩

private def deleteSymbol (properties : OrderedPropsRep)
    (entries : Std.HashMap PropertyKey StoredProperty) (position : Nat) : OrderedPropsRep :=
  let order := tombstone properties.symbolOrder position
  let tombstones := properties.symbolTombstones + 1
  if shouldCompact order.size tombstones then
    let compacted := compactSymbols entries order
    ⟨compacted.1, properties.stringOrder, compacted.2, properties.stringTombstones, 0⟩
  else
    ⟨entries, properties.stringOrder, order, properties.stringTombstones, tombstones⟩

private def deleteRep (properties : OrderedPropsRep) (key : PropertyKey) : OrderedPropsRep :=
  match properties.entries.get? key with
  | none => properties
  | some stored =>
      let entries := properties.entries.erase key
      match key, stored.orderPosition with
      | .string stringKey, some position =>
          if (PropertyKey.arrayIndex? stringKey).isSome then
            { properties with entries }
          else deleteString properties entries position
      | .symbol _, some position => deleteSymbol properties entries position
      | _, none => { properties with entries }

/-- Deletes a property. Reinserting a non-index key appends after current keys in its class. -/
def delete (properties : OrderedProps) (key : PropertyKey) : OrderedProps :=
  .mk (deleteRep properties.rep key)

private def orderedStrings (properties : OrderedPropsRep) : List PropertyKey :=
  properties.stringOrder.foldl (fun keys slot =>
    match slot with
    | some key =>
        if properties.entries.contains (.string key) then .string key :: keys else keys
    | none => keys) [] |>.reverse

private def orderedSymbols (properties : OrderedPropsRep) : List PropertyKey :=
  properties.symbolOrder.foldl (fun keys slot =>
    match slot with
    | some key =>
        if properties.entries.contains (.symbol key) then .symbol key :: keys else keys
    | none => keys) [] |>.reverse

private def indexEntry? (entry : PropertyKey × StoredProperty) : Option (Nat × PropertyKey) :=
  match entry.1 with
  | .string key => (PropertyKey.arrayIndex? key).map (·, entry.1)
  | .symbol _ => none

private def indexEntryLE (left right : Nat × PropertyKey) : Bool := left.1 ≤ right.1

private def sortedIndices (properties : OrderedPropsRep) : List PropertyKey :=
  properties.entries.toList.filterMap indexEntry?
  |>.mergeSort indexEntryLE
  |>.map (·.2)

/-- Returns indices ascending, then strings and symbols in insertion order. -/
def ownKeys (properties : OrderedProps) : List PropertyKey :=
  sortedIndices properties.rep ++ orderedStrings properties.rep ++ orderedSymbols properties.rep

private def tombstoneCount (order : Array (Option α)) : Nat :=
  order.foldl (fun count slot => if slot.isNone then count + 1 else count) 0

private def entryMetadataConsistent (properties : OrderedPropsRep)
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

private def stringSlotConsistent (properties : OrderedPropsRep)
    (slot : Option JSString × Nat) : Bool :=
  match slot.1 with
  | none => true
  | some key =>
      match properties.entries.get? (.string key) with
      | none => false
      | some stored =>
          (PropertyKey.arrayIndex? key).isNone && stored.orderPosition == some slot.2

private def symbolSlotConsistent (properties : OrderedPropsRep)
    (slot : Option SymbolId × Nat) : Bool :=
  match slot.1 with
  | none => true
  | some key =>
      match properties.entries.get? (.symbol key) with
      | none => false
      | some stored => stored.orderPosition == some slot.2

private def metadataConsistentRep (properties : OrderedPropsRep) : Bool :=
  properties.entries.toList.all (entryMetadataConsistent properties) &&
  properties.stringOrder.zipIdx.all (stringSlotConsistent properties) &&
  properties.symbolOrder.zipIdx.all (symbolSlotConsistent properties)

/-- Exact bidirectional agreement between map entries and occupied order slots. -/
def metadataConsistent (properties : OrderedProps) : Bool :=
  metadataConsistentRep properties.rep

private def invariantChecks (properties : OrderedPropsRep) : List Bool :=
  [metadataConsistentRep properties,
    tombstoneCount properties.stringOrder == properties.stringTombstones,
    tombstoneCount properties.symbolOrder == properties.symbolTombstones,
    decide (properties.stringOrder.size < compactionThreshold ∨
      properties.stringTombstones * 2 ≤ properties.stringOrder.size),
    decide (properties.symbolOrder.size < compactionThreshold ∨
      properties.symbolTombstones * 2 ≤ properties.symbolOrder.size)]

/-- Executable representation diagnostic. -/
def isWellFormed (properties : OrderedProps) : Bool := invariantChecks properties.rep |>.all id

/-- Complete observable and metadata consistency for an ordered property collection. -/
def WellFormed (properties : OrderedProps) : Prop := properties.isWellFormed = true

/-- The empty property collection is well formed. -/
theorem empty_wellFormed : WellFormed empty := by
  simp [WellFormed, isWellFormed, invariantChecks, metadataConsistentRep,
    stringSlotConsistent, symbolSlotConsistent, empty, emptyRep, tombstoneCount,
    compactionThreshold]

@[simp] theorem empty_isWellFormed : empty.isWellFormed = true := empty_wellFormed

@[simp] theorem empty_descriptors : empty.descriptors = [] := by
  simp [descriptors, empty, emptyRep]

@[simp] theorem empty_keysAll (predicate : PropertyKey → Bool) : empty.keysAll predicate = true := by
  simp [keysAll, empty, emptyRep]

private def adversarialDescriptor : PropertyDescriptor :=
  .data ⟨.primitive .undefined, true, true, true⟩

private def swappedMetadataRep : OrderedPropsRep :=
  let first := JSString.ofLeanString "first"
  let second := JSString.ofLeanString "second"
  ⟨Std.HashMap.emptyWithCapacity
      |>.insert (.string first) ⟨adversarialDescriptor, some 0⟩
      |>.insert (.string second) ⟨adversarialDescriptor, some 1⟩,
    #[some second, some first], #[], 0, 0⟩

private def staleMetadataRep : OrderedPropsRep :=
  let live := JSString.ofLeanString "live"
  let stale := JSString.ofLeanString "stale"
  ⟨Std.HashMap.emptyWithCapacity.insert (.string live) ⟨adversarialDescriptor, some 0⟩,
    #[some live, some stale], #[], 0, 0⟩

/-- Internal adversarial check for swapped positions and stale occupied slots. -/
def adversarialMetadataRejected : Bool :=
  !(invariantChecks swappedMetadataRep).all id && !(invariantChecks staleMetadataRep).all id

/-- The proposition and executable ordered-property validity check coincide definitionally. -/
theorem wellFormed_iff_isWellFormed (properties : OrderedProps) :
    WellFormed properties ↔ properties.isWellFormed = true := Iff.rfl

end OrderedProps
end TSLean.JS
