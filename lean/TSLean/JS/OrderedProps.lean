import Std.Data.HashMap.Lemmas
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

private def liveOrder (wrap : α → PropertyKey)
    (entries : Std.HashMap PropertyKey StoredProperty) (order : Array (Option α)) : List α :=
  order.toList.filterMap fun slot => do
    let key ← slot
    if entries.contains (wrap key) then some key else none

private def rebuildEntry (wrap : α → PropertyKey)
    (source : Std.HashMap PropertyKey StoredProperty)
    (entries : Std.HashMap PropertyKey StoredProperty) (entry : α × Nat) :
    Std.HashMap PropertyKey StoredProperty :=
  match source.get? (wrap entry.1) with
  | none => entries
  | some stored => entries.insert (wrap entry.1) { stored with orderPosition := some entry.2 }

private def compactOrder (wrap : α → PropertyKey)
    (entries : Std.HashMap PropertyKey StoredProperty) (order : Array (Option α)) :
    Std.HashMap PropertyKey StoredProperty × Array (Option α) :=
  let live := liveOrder wrap entries order
  let rebuilt := live.zipIdx.foldl (rebuildEntry wrap entries) entries
  (rebuilt, (live.map some).toArray)

private def compactStrings
    (entries : Std.HashMap PropertyKey StoredProperty) (order : Array (Option JSString)) :
    Std.HashMap PropertyKey StoredProperty × Array (Option JSString) :=
  compactOrder .string entries order

private def compactSymbols
    (entries : Std.HashMap PropertyKey StoredProperty) (order : Array (Option SymbolId)) :
    Std.HashMap PropertyKey StoredProperty × Array (Option SymbolId) :=
  compactOrder .symbol entries order

private theorem liveOrder_eq_filterMap (wrap : α → PropertyKey)
    (entries : Std.HashMap PropertyKey StoredProperty) (order : Array (Option α))
    (covered : ∀ key, some key ∈ order → ∃ stored, entries.get? (wrap key) = some stored) :
    liveOrder wrap entries order = order.toList.filterMap id := by
  unfold liveOrder
  have go : ∀ slots : List (Option α),
      (∀ key, some key ∈ slots → ∃ stored, entries.get? (wrap key) = some stored) →
      slots.filterMap (fun slot => do
        let key ← slot
        if entries.contains (wrap key) then some key else none) = slots.filterMap id := by
    intro slots coverage
    induction slots with
    | nil => simp
    | cons slot slots ih =>
        cases slot with
        | none =>
            have tail := ih fun key member => coverage key (by simp [member])
            simpa [List.filterMap_cons] using tail
        | some key =>
            obtain ⟨stored, found⟩ := coverage key (by simp)
            have contains : entries.contains (wrap key) = true := by
              rw [← Std.HashMap.isSome_getElem?_eq_contains]
              simpa using congrArg Option.isSome found
            have present : wrap key ∈ entries := Std.HashMap.mem_iff_contains.mpr contains
            have tail := ih fun tailKey member => coverage tailKey (by simp [member])
            simpa [List.filterMap_cons, present] using congrArg (key :: ·) tail
  apply go
  intro key member
  exact covered key (Array.mem_toList_iff.mp member)

private theorem liveOrder_insert_existing (wrap : α → PropertyKey)
    (entries : Std.HashMap PropertyKey StoredProperty) (order : Array (Option α))
    (key : PropertyKey) (stored replacement : StoredProperty)
    (found : entries.get? key = some stored) :
    liveOrder wrap (entries.insert key replacement) order = liveOrder wrap entries order := by
  unfold liveOrder
  congr 1
  funext slot
  cases slot with
  | none => rfl
  | some orderKey =>
      change (if (entries.insert key replacement).contains (wrap orderKey) then some orderKey else none) =
        (if entries.contains (wrap orderKey) then some orderKey else none)
      rw [Std.HashMap.contains_insert]
      by_cases equal : key = wrap orderKey
      · subst key
        have present : entries.contains (wrap orderKey) = true := by
          rw [← Std.HashMap.isSome_getElem?_eq_contains]
          simpa using congrArg Option.isSome found
        simp [present]
      · simp [equal]

private theorem liveOrder_push_fresh (wrap : α → PropertyKey) (injective : Function.Injective wrap)
    (entries : Std.HashMap PropertyKey StoredProperty) (order : Array (Option α))
    (key : α) (replacement : StoredProperty) (absent : entries.get? (wrap key) = none)
    (covered : ∀ orderKey, some orderKey ∈ order →
      ∃ stored, entries.get? (wrap orderKey) = some stored) :
    liveOrder wrap (entries.insert (wrap key) replacement) (order.push (some key)) =
      liveOrder wrap entries order ++ [key] := by
  have nextCovered : ∀ orderKey, some orderKey ∈ order.push (some key) →
      ∃ stored, (entries.insert (wrap key) replacement).get? (wrap orderKey) = some stored := by
    intro orderKey member
    rw [← Array.mem_toList_iff, Array.toList_push, List.mem_append, List.mem_singleton] at member
    rcases member with oldMember | equal
    · obtain ⟨stored, found⟩ := covered orderKey (Array.mem_toList_iff.mp oldMember)
      refine ⟨stored, ?_⟩
      change (entries.insert (wrap key) replacement)[wrap orderKey]? = some stored
      rw [Std.HashMap.getElem?_insert]
      by_cases keysEqual : key = orderKey
      · subst orderKey
        rw [absent] at found
        contradiction
      · have wrappedNe : wrap key ≠ wrap orderKey := fun wrappedEqual =>
          keysEqual (injective wrappedEqual)
        have beqFalse : (wrap key == wrap orderKey) = false := by simp [wrappedNe]
        rw [beqFalse]
        exact found
    · have keysEqual := Option.some.inj equal
      subst orderKey
      exact ⟨replacement, by simp⟩
  rw [liveOrder_eq_filterMap wrap _ _ nextCovered,
    liveOrder_eq_filterMap wrap entries order covered]
  simp [Array.toList_push, List.filterMap_append]

private theorem liveOrder_entries_ext (wrap : α → PropertyKey)
    (left right : Std.HashMap PropertyKey StoredProperty) (order : Array (Option α))
    (support : ∀ key, left.contains (wrap key) = right.contains (wrap key)) :
    liveOrder wrap left order = liveOrder wrap right order := by
  unfold liveOrder
  congr 1
  funext slot
  cases slot with
  | none => rfl
  | some key =>
      change (if left.contains (wrap key) then some key else none) =
        (if right.contains (wrap key) then some key else none)
      rw [support]

private theorem liveOrder_erase (wrap : α → PropertyKey)
    (entries : Std.HashMap PropertyKey StoredProperty) (order : Array (Option α))
    (deleted : PropertyKey) :
    liveOrder wrap (entries.erase deleted) order =
      (liveOrder wrap entries order).filter fun key => wrap key != deleted := by
  unfold liveOrder
  rw [List.filter_filterMap]
  congr 1
  funext slot
  cases slot with
  | none => rfl
  | some key =>
      change (if (entries.erase deleted).contains (wrap key) then some key else none) =
        (if entries.contains (wrap key) then some key else none).filter
          (fun key => wrap key != deleted)
      rw [Std.HashMap.contains_erase]
      by_cases equal : wrap key = deleted
      · subst deleted
        by_cases present : entries.contains (wrap key) = true <;>
          simp [Option.filter, present]
      · by_cases present : entries.contains (wrap key) = true <;>
          simp [Option.filter, equal, Ne.symm equal, present]

private theorem rebuildEntry_descriptor (wrap : α → PropertyKey)
    (source current : Std.HashMap PropertyKey StoredProperty) (entry : α × Nat)
    (preserved : ∀ key, (current.get? key).map (·.descriptor) =
      (source.get? key).map (·.descriptor)) :
    ∀ key, ((rebuildEntry wrap source current entry).get? key).map (·.descriptor) =
      (source.get? key).map (·.descriptor) := by
  intro key
  cases found : source.get? (wrap entry.1) with
  | none =>
      simp only [rebuildEntry]
      rw [found]
      exact preserved key
  | some stored =>
      simp only [rebuildEntry, found]
      change Option.map _ ((current.insert (wrap entry.1)
        { stored with orderPosition := some entry.2 })[key]?) = _
      rw [Std.HashMap.getElem?_insert]
      split
      · simp_all
      · exact preserved key

private theorem rebuildEntries_descriptor (wrap : α → PropertyKey)
    (source : Std.HashMap PropertyKey StoredProperty) (entries : List (α × Nat))
    (current : Std.HashMap PropertyKey StoredProperty)
    (preserved : ∀ key, (current.get? key).map (·.descriptor) =
      (source.get? key).map (·.descriptor)) :
    ∀ key, ((entries.foldl (rebuildEntry wrap source) current).get? key).map (·.descriptor) =
      (source.get? key).map (·.descriptor) := by
  induction entries generalizing current with
  | nil => exact preserved
  | cons entry entries ih =>
      exact ih _ (rebuildEntry_descriptor wrap source current entry preserved)

private theorem compactOrder_descriptor (wrap : α → PropertyKey)
    (entries : Std.HashMap PropertyKey StoredProperty) (order : Array (Option α)) (key) :
    (((compactOrder wrap entries order).1.get? key).map (·.descriptor)) =
      (entries.get? key).map (·.descriptor) := by
  unfold compactOrder
  dsimp
  exact rebuildEntries_descriptor wrap entries _ entries (fun _ => rfl) key

private theorem compactOrder_contains (wrap : α → PropertyKey)
    (entries : Std.HashMap PropertyKey StoredProperty) (order : Array (Option α)) (key) :
    (compactOrder wrap entries order).1.contains key = entries.contains key := by
  rw [Std.HashMap.contains_eq_isSome_getElem?, Std.HashMap.contains_eq_isSome_getElem?]
  have descriptors := congrArg Option.isSome (compactOrder_descriptor wrap entries order key)
  simpa only [Option.isSome_map] using descriptors

private theorem compactOrder_output (wrap : α → PropertyKey)
    (entries : Std.HashMap PropertyKey StoredProperty) (order : Array (Option α))
    (covered : ∀ key, some key ∈ order → ∃ stored, entries.get? (wrap key) = some stored) :
    (compactOrder wrap entries order).2 = ((order.toList.filterMap id).map some).toArray := by
  simp [compactOrder, liveOrder_eq_filterMap wrap entries order covered]

private theorem rebuildZip_get?_not_mem (wrap : α → PropertyKey) (injective : Function.Injective wrap)
    (source current : Std.HashMap PropertyKey StoredProperty) (keys : List α) (start : Nat)
    (target : α) (absent : target ∉ keys) :
    ((keys.zipIdx start).foldl (rebuildEntry wrap source) current).get? (wrap target) =
      current.get? (wrap target) := by
  induction keys generalizing start current with
  | nil => rfl
  | cons key keys ih =>
      have keyNe : key ≠ target := by
        intro equal
        apply absent
        simp [equal]
      have wrappedNe : wrap key ≠ wrap target := fun equal => keyNe (injective equal)
      have tailAbsent : target ∉ keys := by
        intro member
        exact absent (by simp [member])
      simp only [List.zipIdx_cons, List.foldl_cons, rebuildEntry]
      cases found : source.get? (wrap key) with
      | none =>
          rw [ih _ _ tailAbsent]
      | some stored =>
          rw [ih _ _ tailAbsent]
          change (current.insert (wrap key)
            { stored with orderPosition := some start })[wrap target]? = _
          rw [Std.HashMap.getElem?_insert]
          simp [wrappedNe]

private theorem rebuildZip_get?_outside (wrap : α → PropertyKey)
    (source current : Std.HashMap PropertyKey StoredProperty) (keys : List α) (start : Nat)
    (target : PropertyKey) (outside : ∀ key ∈ keys, wrap key ≠ target) :
    ((keys.zipIdx start).foldl (rebuildEntry wrap source) current).get? target = current.get? target := by
  induction keys generalizing start current with
  | nil => rfl
  | cons key keys ih =>
      have keyOutside := outside key (by simp)
      have tailOutside : ∀ key ∈ keys, wrap key ≠ target := fun key member =>
        outside key (by simp [member])
      simp only [List.zipIdx_cons, List.foldl_cons, rebuildEntry]
      cases found : source.get? (wrap key) with
      | none => rw [ih _ _ tailOutside]
      | some stored =>
          rw [ih _ _ tailOutside]
          change (current.insert (wrap key)
            { stored with orderPosition := some start })[target]? = _
          rw [Std.HashMap.getElem?_insert]
          simp [keyOutside]

private theorem rebuildZip_get?_at (wrap : α → PropertyKey) (injective : Function.Injective wrap)
    (source current : Std.HashMap PropertyKey StoredProperty) (keys : List α) (start position : Nat)
    (key : α) (stored : StoredProperty) (nodup : keys.Nodup)
    (atPosition : keys[position]? = some key) (found : source.get? (wrap key) = some stored) :
    ((keys.zipIdx start).foldl (rebuildEntry wrap source) current).get? (wrap key) =
      some { stored with orderPosition := some (start + position) } := by
  induction keys generalizing start position current with
  | nil => simp at atPosition
  | cons first keys ih =>
      have nodupParts := List.nodup_cons.mp nodup
      have firstAbsent := nodupParts.1
      have tailNodup := nodupParts.2
      cases position with
      | zero =>
          simp at atPosition
          subst first
          simp only [List.zipIdx_cons, List.foldl_cons, rebuildEntry]
          rw [found, rebuildZip_get?_not_mem wrap injective source _ keys (start + 1) key firstAbsent]
          change (current.insert (wrap key)
            { stored with orderPosition := some start })[wrap key]? = _
          simp
      | succ position =>
          simp only [List.getElem?_cons_succ] at atPosition
          simp only [List.zipIdx_cons, List.foldl_cons]
          rw [ih (start := start + 1) (position := position)
            (current := rebuildEntry wrap source current (first, start)) tailNodup atPosition]
          congr 3
          omega

private theorem compactOrder_get?_not_mem (wrap : α → PropertyKey)
    (injective : Function.Injective wrap) (entries : Std.HashMap PropertyKey StoredProperty)
    (order : Array (Option α)) (target : α) (absent : target ∉ liveOrder wrap entries order) :
    (compactOrder wrap entries order).1.get? (wrap target) = entries.get? (wrap target) := by
  unfold compactOrder
  dsimp
  exact rebuildZip_get?_not_mem wrap injective entries entries _ 0 target absent

private theorem compactOrder_get?_outside (wrap : α → PropertyKey)
    (entries : Std.HashMap PropertyKey StoredProperty) (order : Array (Option α))
    (target : PropertyKey) (outside : ∀ key ∈ liveOrder wrap entries order, wrap key ≠ target) :
    (compactOrder wrap entries order).1.get? target = entries.get? target := by
  unfold compactOrder
  dsimp
  exact rebuildZip_get?_outside wrap entries entries _ 0 target outside

private theorem compactOrder_get?_at (wrap : α → PropertyKey)
    (injective : Function.Injective wrap) (entries : Std.HashMap PropertyKey StoredProperty)
    (order : Array (Option α)) (position : Nat) (key : α) (stored : StoredProperty)
    (nodup : (liveOrder wrap entries order).Nodup)
    (atPosition : (liveOrder wrap entries order)[position]? = some key)
    (found : entries.get? (wrap key) = some stored) :
    (compactOrder wrap entries order).1.get? (wrap key) =
      some { stored with orderPosition := some position } := by
  unfold compactOrder
  dsimp
  simpa using rebuildZip_get?_at wrap injective entries entries _ 0 position key stored nodup
    atPosition found

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

private theorem tombstone_size (order : Array (Option α)) (position : Nat) :
    (tombstone order position).size = order.size := by
  unfold tombstone
  split <;> simp

private theorem liveOrder_tombstone_deleted (wrap : α → PropertyKey)
    (entries : Std.HashMap PropertyKey StoredProperty) (order : Array (Option α))
    (key : α) (position : Nat) (slot : order[position]? = some (some key)) :
    liveOrder wrap (entries.erase (wrap key)) (tombstone order position) =
      liveOrder wrap (entries.erase (wrap key)) order := by
  have positionBound : position < order.size := (Array.getElem?_eq_some_iff.mp slot).choose
  unfold tombstone
  simp only [positionBound, ↓reduceDIte]
  unfold liveOrder
  rw [Array.toList_set]
  have deletedAbsent : (entries.erase (wrap key)).contains (wrap key) = false := by simp
  have go : ∀ (slots : List (Option α)) (position : Nat),
      slots[position]? = some (some key) →
      (slots.set position none).filterMap (fun slot => do
        let orderKey ← slot
        if (entries.erase (wrap key)).contains (wrap orderKey) then some orderKey else none) =
      slots.filterMap (fun slot => do
        let orderKey ← slot
        if (entries.erase (wrap key)).contains (wrap orderKey) then some orderKey else none) := by
    intro slots position atPosition
    induction slots generalizing position with
    | nil => simp at atPosition
    | cons head tail ih =>
        cases position with
        | zero =>
            simp at atPosition
            subst head
            simp
        | succ position =>
            simp only [List.getElem?_cons_succ] at atPosition
            simp only [List.set, List.filterMap_cons]
            rw [ih position atPosition]
  exact go order.toList position (by simpa using slot)

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
  (liveOrder .string properties.entries properties.stringOrder).map .string

private def orderedSymbols (properties : OrderedPropsRep) : List PropertyKey :=
  (liveOrder .symbol properties.entries properties.symbolOrder).map .symbol

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

/-- Numeric array indices from `ownKeys`, retaining their ascending order. -/
def arrayIndices (properties : OrderedProps) : List Nat :=
  properties.ownKeys.filterMap fun key => match key with
    | .string stringKey => PropertyKey.arrayIndex? stringKey
    | .symbol _ => none

/-- Ordinary string keys from `ownKeys`, retaining insertion order. -/
def stringKeys (properties : OrderedProps) : List PropertyKey :=
  properties.ownKeys.filter fun key => match key with
    | .string stringKey => (PropertyKey.arrayIndex? stringKey).isNone
    | .symbol _ => false

/-- Symbol keys from `ownKeys`, retaining insertion order. -/
def symbolKeys (properties : OrderedProps) : List PropertyKey :=
  properties.ownKeys.filter fun key => match key with
    | .string _ => false
    | .symbol _ => true

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

private def EntryValid (properties : OrderedPropsRep)
    (entry : PropertyKey × StoredProperty) : Prop :=
  match entry.1 with
  | .string key =>
      match PropertyKey.arrayIndex? key with
      | some _ => entry.2.orderPosition = none
      | none => ∃ position, entry.2.orderPosition = some position ∧
          properties.stringOrder[position]? = some (some key)
  | .symbol key => ∃ position, entry.2.orderPosition = some position ∧
      properties.symbolOrder[position]? = some (some key)

private def StringSlotValid (properties : OrderedPropsRep)
    (slot : Option JSString × Nat) : Prop :=
  match slot.1 with
  | none => True
  | some key => ∃ stored, properties.entries.get? (.string key) = some stored ∧
      PropertyKey.arrayIndex? key = none ∧ stored.orderPosition = some slot.2

private def SymbolSlotValid (properties : OrderedPropsRep)
    (slot : Option SymbolId × Nat) : Prop :=
  match slot.1 with
  | none => True
  | some key => ∃ stored, properties.entries.get? (.symbol key) = some stored ∧
      stored.orderPosition = some slot.2

private def MetadataValidRep (properties : OrderedPropsRep) : Prop :=
  (∀ key stored, properties.entries.get? key = some stored →
    EntryValid properties (key, stored)) ∧
  (∀ position (inBounds : position < properties.stringOrder.zipIdx.size),
    StringSlotValid properties properties.stringOrder.zipIdx[position]) ∧
  (∀ position (inBounds : position < properties.symbolOrder.zipIdx.size),
    SymbolSlotValid properties properties.symbolOrder.zipIdx[position])

private def ValidRep (properties : OrderedPropsRep) : Prop :=
  MetadataValidRep properties ∧
  tombstoneCount properties.stringOrder = properties.stringTombstones ∧
  tombstoneCount properties.symbolOrder = properties.symbolTombstones ∧
  (properties.stringOrder.size < compactionThreshold ∨
    properties.stringTombstones * 2 ≤ properties.stringOrder.size) ∧
  (properties.symbolOrder.size < compactionThreshold ∨
    properties.symbolTombstones * 2 ≤ properties.symbolOrder.size)

private theorem entryMetadataConsistent_iff (properties : OrderedPropsRep)
    (entry : PropertyKey × StoredProperty) :
    entryMetadataConsistent properties entry = true ↔ EntryValid properties entry := by
  rcases entry with ⟨key, stored⟩
  cases key with
  | string key =>
      cases parsed : PropertyKey.arrayIndex? key with
      | none =>
          cases position : stored.orderPosition <;>
            simp [entryMetadataConsistent, EntryValid, parsed, position]
      | some index => simp [entryMetadataConsistent, EntryValid, parsed]
  | symbol key =>
      cases position : stored.orderPosition <;>
        simp [entryMetadataConsistent, EntryValid, position]

private theorem stringSlotConsistent_iff (properties : OrderedPropsRep)
    (slot : Option JSString × Nat) :
    stringSlotConsistent properties slot = true ↔ StringSlotValid properties slot := by
  rcases slot with ⟨slot, position⟩
  cases slot with
  | none => simp [stringSlotConsistent, StringSlotValid]
  | some key =>
      cases found : properties.entries.get? (.string key) with
      | none =>
          simp only [stringSlotConsistent, StringSlotValid]
          rw [found]
          simp
      | some stored =>
          simp only [stringSlotConsistent, StringSlotValid]
          rw [found]
          simp

private theorem symbolSlotConsistent_iff (properties : OrderedPropsRep)
    (slot : Option SymbolId × Nat) :
    symbolSlotConsistent properties slot = true ↔ SymbolSlotValid properties slot := by
  rcases slot with ⟨slot, position⟩
  cases slot with
  | none => simp [symbolSlotConsistent, SymbolSlotValid]
  | some key =>
      cases found : properties.entries.get? (.symbol key) with
      | none =>
          simp only [symbolSlotConsistent, SymbolSlotValid]
          rw [found]
          simp
      | some stored =>
          simp only [symbolSlotConsistent, SymbolSlotValid]
          rw [found]
          simp

private theorem metadataConsistentRep_iff (properties : OrderedPropsRep) :
    metadataConsistentRep properties = true ↔ MetadataValidRep properties := by
  simp only [metadataConsistentRep, Bool.and_eq_true, Array.all_eq_true,
    List.all_eq_true, entryMetadataConsistent_iff,
    stringSlotConsistent_iff, symbolSlotConsistent_iff, MetadataValidRep]
  simp [and_assoc]

private theorem stringSlot_covered {properties : OrderedPropsRep}
    (valid : MetadataValidRep properties) {key : JSString}
    (member : some key ∈ properties.stringOrder) :
    ∃ stored, properties.entries.get? (.string key) = some stored := by
  obtain ⟨position, inBounds, atPosition⟩ := Array.getElem_of_mem member
  have slotValid := valid.2.1 position (by simpa using inBounds)
  simp [Array.getElem_zipIdx, atPosition, StringSlotValid] at slotValid
  exact ⟨slotValid.choose, slotValid.choose_spec.1⟩

private theorem symbolSlot_covered {properties : OrderedPropsRep}
    (valid : MetadataValidRep properties) {key : SymbolId}
    (member : some key ∈ properties.symbolOrder) :
    ∃ stored, properties.entries.get? (.symbol key) = some stored := by
  obtain ⟨position, inBounds, atPosition⟩ := Array.getElem_of_mem member
  have slotValid := valid.2.2 position (by simpa using inBounds)
  simp [Array.getElem_zipIdx, atPosition, SymbolSlotValid] at slotValid
  exact ⟨slotValid.choose, slotValid.choose_spec.1⟩

private theorem entryValid_of_get? {properties : OrderedPropsRep}
    (valid : MetadataValidRep properties) {key : PropertyKey} {stored : StoredProperty}
    (found : properties.entries.get? key = some stored) : EntryValid properties (key, stored) := by
  exact valid.1 key stored found

private theorem stringSlot_nonIndex {properties : OrderedPropsRep}
    (valid : MetadataValidRep properties) {key : JSString}
    (member : some key ∈ properties.stringOrder) : PropertyKey.arrayIndex? key = none := by
  obtain ⟨position, inBounds, atPosition⟩ := Array.getElem_of_mem member
  have slotValid := valid.2.1 position (by simpa using inBounds)
  simp [Array.getElem_zipIdx, atPosition, StringSlotValid] at slotValid
  exact slotValid.choose_spec.2.1

private theorem stringSlot_unique {properties : OrderedPropsRep}
    (valid : MetadataValidRep properties) {left right : Nat} {key : JSString}
    (leftBound : left < properties.stringOrder.size)
    (rightBound : right < properties.stringOrder.size)
    (leftKey : properties.stringOrder[left] = some key)
    (rightKey : properties.stringOrder[right] = some key) : left = right := by
  have leftValid := valid.2.1 left (by simpa using leftBound)
  have rightValid := valid.2.1 right (by simpa using rightBound)
  simp [Array.getElem_zipIdx, leftKey, StringSlotValid] at leftValid
  simp [Array.getElem_zipIdx, rightKey, StringSlotValid] at rightValid
  rcases leftValid with ⟨leftStored, leftFound, _, leftPosition⟩
  rcases rightValid with ⟨rightStored, rightFound, _, rightPosition⟩
  have storedEqual : leftStored = rightStored := by
    rw [leftFound] at rightFound
    exact Option.some.inj rightFound
  subst rightStored
  rw [leftPosition] at rightPosition
  exact Option.some.inj rightPosition

private theorem symbolSlot_unique {properties : OrderedPropsRep}
    (valid : MetadataValidRep properties) {left right : Nat} {key : SymbolId}
    (leftBound : left < properties.symbolOrder.size)
    (rightBound : right < properties.symbolOrder.size)
    (leftKey : properties.symbolOrder[left] = some key)
    (rightKey : properties.symbolOrder[right] = some key) : left = right := by
  have leftValid := valid.2.2 left (by simpa using leftBound)
  have rightValid := valid.2.2 right (by simpa using rightBound)
  simp [Array.getElem_zipIdx, leftKey, SymbolSlotValid] at leftValid
  simp [Array.getElem_zipIdx, rightKey, SymbolSlotValid] at rightValid
  rcases leftValid with ⟨leftStored, leftFound, leftPosition⟩
  rcases rightValid with ⟨rightStored, rightFound, rightPosition⟩
  have storedEqual : leftStored = rightStored := by
    rw [leftFound] at rightFound
    exact Option.some.inj rightFound
  subst rightStored
  rw [leftPosition] at rightPosition
  exact Option.some.inj rightPosition

private theorem liveOrder_nodup_of_unique (order : Array (Option α))
    (unique : ∀ (left right) (key : α) (leftBound : left < order.size)
      (rightBound : right < order.size), order[left] = some key →
      order[right] = some key → left = right) :
    (order.toList.filterMap id).Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_filterMap, List.pairwise_iff_getElem]
  intro left right leftBound rightBound before leftSlot leftValue rightSlot rightValue
  simp only [id_eq] at leftValue rightValue
  intro keysEqual
  subst rightSlot
  have leftArrayBound : left < order.size := by simpa using leftBound
  have rightArrayBound : right < order.size := by simpa using rightBound
  have positionsEqual := unique left right leftSlot leftArrayBound rightArrayBound
    (by simpa using leftValue) (by simpa using rightValue)
  omega

private theorem stringLiveOrder_nodup {properties : OrderedPropsRep}
    (valid : MetadataValidRep properties) :
    (properties.stringOrder.toList.filterMap id).Nodup := by
  apply liveOrder_nodup_of_unique
  intro left right key leftBound rightBound leftKey rightKey
  exact stringSlot_unique valid leftBound rightBound leftKey rightKey

private theorem symbolLiveOrder_nodup {properties : OrderedPropsRep}
    (valid : MetadataValidRep properties) :
    (properties.symbolOrder.toList.filterMap id).Nodup := by
  apply liveOrder_nodup_of_unique
  intro left right key leftBound rightBound leftKey rightKey
  exact symbolSlot_unique valid leftBound rightBound leftKey rightKey

private theorem compactStrings_metadata (properties : OrderedPropsRep)
    (valid : MetadataValidRep properties) :
    let compacted := compactStrings properties.entries properties.stringOrder
    MetadataValidRep ⟨compacted.1, compacted.2, properties.symbolOrder,
      0, properties.symbolTombstones⟩ := by
  let covered : ∀ key, some key ∈ properties.stringOrder →
      ∃ stored, properties.entries.get? (.string key) = some stored := fun _ member =>
    stringSlot_covered valid member
  have liveEq : liveOrder PropertyKey.string properties.entries properties.stringOrder =
      properties.stringOrder.toList.filterMap id :=
    liveOrder_eq_filterMap .string properties.entries properties.stringOrder covered
  have liveNodup : (liveOrder PropertyKey.string properties.entries
      properties.stringOrder).Nodup := by
    rw [liveEq]
    exact stringLiveOrder_nodup valid
  have outputEq : (compactStrings properties.entries properties.stringOrder).2 =
      ((properties.stringOrder.toList.filterMap id).map some).toArray :=
    compactOrder_output .string properties.entries properties.stringOrder covered
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro entryKey finalStored finalFound
    cases entryKey with
    | string key =>
        change (compactOrder PropertyKey.string properties.entries properties.stringOrder).1.get?
          (.string key) = some finalStored at finalFound
        cases sourceFound : properties.entries.get? (.string key) with
        | none =>
            have descriptors := compactOrder_descriptor PropertyKey.string properties.entries
              properties.stringOrder (.string key)
            rw [sourceFound, finalFound] at descriptors
            simp at descriptors
        | some sourceStored =>
            have sourceValid := entryValid_of_get? valid sourceFound
            cases parsed : PropertyKey.arrayIndex? key with
            | some index =>
                have outside : ∀ liveKey ∈ liveOrder PropertyKey.string properties.entries
                    properties.stringOrder, PropertyKey.string liveKey ≠ .string key := by
                  intro liveKey liveMember equal
                  cases equal
                  rw [liveEq] at liveMember
                  obtain ⟨slot, slotMember, slotValue⟩ := List.mem_filterMap.mp liveMember
                  simp only [id_eq] at slotValue
                  subst slot
                  have nonIndex := stringSlot_nonIndex valid
                    (Array.mem_toList_iff.mp slotMember)
                  rw [parsed] at nonIndex
                  contradiction
                have unchanged := compactOrder_get?_outside PropertyKey.string properties.entries
                  properties.stringOrder (.string key) outside
                rw [unchanged, sourceFound] at finalFound
                have storedEqual := Option.some.inj finalFound
                subst finalStored
                simpa [EntryValid, parsed] using sourceValid
            | none =>
                simp [EntryValid, parsed] at sourceValid
                rcases sourceValid with ⟨oldPosition, sourcePosition, sourceSlot⟩
                have slotMember : some key ∈ properties.stringOrder :=
                  Array.mem_of_getElem? sourceSlot
                have liveMember : key ∈ liveOrder PropertyKey.string properties.entries
                    properties.stringOrder := by
                  rw [liveEq]
                  exact List.mem_filterMap.mpr ⟨some key,
                    Array.mem_toList_iff.mpr slotMember, rfl⟩
                obtain ⟨position, positionBound, atPosition⟩ := List.getElem_of_mem liveMember
                have atPosition? : (liveOrder PropertyKey.string properties.entries
                    properties.stringOrder)[position]? = some key := by
                  rw [List.getElem?_eq_getElem positionBound]
                  exact congrArg some atPosition
                have rebuilt := compactOrder_get?_at PropertyKey.string (by
                    intro left right equal
                    exact PropertyKey.string.inj equal)
                  properties.entries properties.stringOrder position key sourceStored liveNodup
                  atPosition? sourceFound
                rw [rebuilt] at finalFound
                have storedEqual := Option.some.inj finalFound
                subst finalStored
                simp only [EntryValid, parsed]
                refine ⟨position, rfl, ?_⟩
                rw [outputEq]
                simpa [liveEq] using congrArg (Option.map some) atPosition?
    | symbol key =>
        change (compactOrder PropertyKey.string properties.entries properties.stringOrder).1.get?
          (.symbol key) = some finalStored at finalFound
        cases sourceFound : properties.entries.get? (.symbol key) with
        | none =>
            have descriptors := compactOrder_descriptor PropertyKey.string properties.entries
              properties.stringOrder (.symbol key)
            rw [sourceFound, finalFound] at descriptors
            simp at descriptors
        | some sourceStored =>
            have unchanged := compactOrder_get?_outside PropertyKey.string properties.entries
              properties.stringOrder (.symbol key) (by simp)
            rw [unchanged, sourceFound] at finalFound
            have storedEqual := Option.some.inj finalFound
            subst finalStored
            exact entryValid_of_get? valid sourceFound
  · intro position inBounds
    have positionBound : position < (properties.stringOrder.toList.filterMap id).length := by
      simpa [outputEq] using inBounds
    let key := (properties.stringOrder.toList.filterMap id)[position]
    have atPosition? : (properties.stringOrder.toList.filterMap id)[position]? = some key :=
      List.getElem?_eq_getElem positionBound
    have liveAtPosition : (liveOrder PropertyKey.string properties.entries
        properties.stringOrder)[position]? = some key := by simpa [liveEq] using atPosition?
    have liveMember : key ∈ liveOrder PropertyKey.string properties.entries
        properties.stringOrder := List.mem_of_getElem? liveAtPosition
    rw [liveEq] at liveMember
    obtain ⟨slot, slotMember, slotValue⟩ := List.mem_filterMap.mp liveMember
    simp only [id_eq] at slotValue
    subst slot
    obtain ⟨stored, found⟩ := stringSlot_covered valid (Array.mem_toList_iff.mp slotMember)
    have rebuilt := compactOrder_get?_at PropertyKey.string (by
        intro left right equal
        exact PropertyKey.string.inj equal)
      properties.entries properties.stringOrder position key stored liveNodup
      liveAtPosition found
    have nonIndex := stringSlot_nonIndex valid (Array.mem_toList_iff.mp slotMember)
    have outputBound : position < (compactStrings properties.entries
        properties.stringOrder).2.size := by simpa [outputEq] using positionBound
    have outputAt : (compactStrings properties.entries properties.stringOrder).2[position] =
        some key := by simp [outputEq, key]
    simp [Array.getElem_zipIdx, outputAt, StringSlotValid]
    exact ⟨{ stored with orderPosition := some position }, rebuilt, nonIndex, rfl⟩
  · intro position inBounds
    have oldBound : position < properties.symbolOrder.size := by simpa using inBounds
    have oldValid := valid.2.2 position (by simpa using oldBound)
    cases slot : properties.symbolOrder[position] with
    | none =>
        simp [Array.getElem_zipIdx, slot, SymbolSlotValid] at oldValid ⊢
    | some key =>
        simp [Array.getElem_zipIdx, slot, SymbolSlotValid] at oldValid
        rcases oldValid with ⟨stored, found, storedPosition⟩
        have unchanged := compactOrder_get?_outside PropertyKey.string properties.entries
          properties.stringOrder (.symbol key) (by simp)
        simp [Array.getElem_zipIdx, slot, SymbolSlotValid]
        exact ⟨stored, unchanged.trans found, storedPosition⟩

private theorem compactSymbols_metadata (properties : OrderedPropsRep)
    (valid : MetadataValidRep properties) :
    let compacted := compactSymbols properties.entries properties.symbolOrder
    MetadataValidRep ⟨compacted.1, properties.stringOrder, compacted.2,
      properties.stringTombstones, 0⟩ := by
  let covered : ∀ key, some key ∈ properties.symbolOrder →
      ∃ stored, properties.entries.get? (.symbol key) = some stored := fun _ member =>
    symbolSlot_covered valid member
  have liveEq : liveOrder PropertyKey.symbol properties.entries properties.symbolOrder =
      properties.symbolOrder.toList.filterMap id :=
    liveOrder_eq_filterMap .symbol properties.entries properties.symbolOrder covered
  have liveNodup : (liveOrder PropertyKey.symbol properties.entries
      properties.symbolOrder).Nodup := by
    rw [liveEq]
    exact symbolLiveOrder_nodup valid
  have outputEq : (compactSymbols properties.entries properties.symbolOrder).2 =
      ((properties.symbolOrder.toList.filterMap id).map some).toArray :=
    compactOrder_output .symbol properties.entries properties.symbolOrder covered
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro entryKey finalStored finalFound
    cases entryKey with
    | string key =>
        change (compactOrder PropertyKey.symbol properties.entries properties.symbolOrder).1.get?
          (.string key) = some finalStored at finalFound
        cases sourceFound : properties.entries.get? (.string key) with
        | none =>
            have descriptors := compactOrder_descriptor PropertyKey.symbol properties.entries
              properties.symbolOrder (.string key)
            rw [sourceFound, finalFound] at descriptors
            simp at descriptors
        | some sourceStored =>
            have unchanged := compactOrder_get?_outside PropertyKey.symbol properties.entries
              properties.symbolOrder (.string key) (by simp)
            rw [unchanged, sourceFound] at finalFound
            have storedEqual := Option.some.inj finalFound
            subst finalStored
            exact entryValid_of_get? valid sourceFound
    | symbol key =>
        change (compactOrder PropertyKey.symbol properties.entries properties.symbolOrder).1.get?
          (.symbol key) = some finalStored at finalFound
        cases sourceFound : properties.entries.get? (.symbol key) with
        | none =>
            have descriptors := compactOrder_descriptor PropertyKey.symbol properties.entries
              properties.symbolOrder (.symbol key)
            rw [sourceFound, finalFound] at descriptors
            simp at descriptors
        | some sourceStored =>
            have sourceValid := entryValid_of_get? valid sourceFound
            simp [EntryValid] at sourceValid
            rcases sourceValid with ⟨oldPosition, sourcePosition, sourceSlot⟩
            have slotMember : some key ∈ properties.symbolOrder :=
              Array.mem_of_getElem? sourceSlot
            have liveMember : key ∈ liveOrder PropertyKey.symbol properties.entries
                properties.symbolOrder := by
              rw [liveEq]
              exact List.mem_filterMap.mpr ⟨some key,
                Array.mem_toList_iff.mpr slotMember, rfl⟩
            obtain ⟨position, positionBound, atPosition⟩ := List.getElem_of_mem liveMember
            have atPosition? : (liveOrder PropertyKey.symbol properties.entries
                properties.symbolOrder)[position]? = some key := by
              rw [List.getElem?_eq_getElem positionBound]
              exact congrArg some atPosition
            have rebuilt := compactOrder_get?_at PropertyKey.symbol (by
                intro left right equal
                exact PropertyKey.symbol.inj equal)
              properties.entries properties.symbolOrder position key sourceStored liveNodup
              atPosition? sourceFound
            rw [rebuilt] at finalFound
            have storedEqual := Option.some.inj finalFound
            subst finalStored
            simp only [EntryValid]
            refine ⟨position, rfl, ?_⟩
            rw [outputEq]
            simpa [liveEq] using congrArg (Option.map some) atPosition?
  · intro position inBounds
    have oldBound : position < properties.stringOrder.size := by simpa using inBounds
    have oldValid := valid.2.1 position (by simpa using oldBound)
    cases slot : properties.stringOrder[position] with
    | none =>
        simp [Array.getElem_zipIdx, slot, StringSlotValid] at oldValid ⊢
    | some key =>
        simp [Array.getElem_zipIdx, slot, StringSlotValid] at oldValid
        rcases oldValid with ⟨stored, found, nonIndex, storedPosition⟩
        have unchanged := compactOrder_get?_outside PropertyKey.symbol properties.entries
          properties.symbolOrder (.string key) (by simp)
        simp [Array.getElem_zipIdx, slot, StringSlotValid]
        exact ⟨stored, unchanged.trans found, nonIndex, storedPosition⟩
  · intro position inBounds
    have positionBound : position < (properties.symbolOrder.toList.filterMap id).length := by
      simpa [outputEq] using inBounds
    let key := (properties.symbolOrder.toList.filterMap id)[position]
    have atPosition? : (properties.symbolOrder.toList.filterMap id)[position]? = some key :=
      List.getElem?_eq_getElem positionBound
    have liveAtPosition : (liveOrder PropertyKey.symbol properties.entries
        properties.symbolOrder)[position]? = some key := by simpa [liveEq] using atPosition?
    have liveMember : key ∈ liveOrder PropertyKey.symbol properties.entries
        properties.symbolOrder := List.mem_of_getElem? liveAtPosition
    rw [liveEq] at liveMember
    obtain ⟨slot, slotMember, slotValue⟩ := List.mem_filterMap.mp liveMember
    simp only [id_eq] at slotValue
    subst slot
    obtain ⟨stored, found⟩ := symbolSlot_covered valid (Array.mem_toList_iff.mp slotMember)
    have rebuilt := compactOrder_get?_at PropertyKey.symbol (by
        intro left right equal
        exact PropertyKey.symbol.inj equal)
      properties.entries properties.symbolOrder position key stored liveNodup
      liveAtPosition found
    have outputBound : position < (compactSymbols properties.entries
        properties.symbolOrder).2.size := by simpa [outputEq] using positionBound
    have outputAt : (compactSymbols properties.entries properties.symbolOrder).2[position] =
        some key := by simp [outputEq, key]
    simp [Array.getElem_zipIdx, outputAt, SymbolSlotValid]
    exact ⟨{ stored with orderPosition := some position }, rebuilt, rfl⟩

private theorem tombstoneCount_map_some (keys : List α) :
    tombstoneCount (keys.map some).toArray = 0 := by
  unfold tombstoneCount
  rw [← Array.foldl_toList]
  induction keys <;> simp_all

private theorem compactStrings_valid (properties : OrderedPropsRep)
    (metadata : MetadataValidRep properties)
    (symbolCount : tombstoneCount properties.symbolOrder = properties.symbolTombstones)
    (symbolRatio : properties.symbolOrder.size < compactionThreshold ∨
      properties.symbolTombstones * 2 ≤ properties.symbolOrder.size) :
    let compacted := compactStrings properties.entries properties.stringOrder
    ValidRep ⟨compacted.1, compacted.2, properties.symbolOrder, 0,
      properties.symbolTombstones⟩ := by
  have covered : ∀ key, some key ∈ properties.stringOrder →
      ∃ stored, properties.entries.get? (.string key) = some stored := fun _ member =>
    stringSlot_covered metadata member
  have outputEq := compactOrder_output PropertyKey.string properties.entries
    properties.stringOrder covered
  dsimp only
  refine ⟨compactStrings_metadata properties metadata, ?_, symbolCount, ?_, symbolRatio⟩
  · change tombstoneCount (compactOrder PropertyKey.string properties.entries
      properties.stringOrder).2 = 0
    rw [outputEq]
    exact tombstoneCount_map_some _
  · right
    simp

private theorem compactSymbols_valid (properties : OrderedPropsRep)
    (metadata : MetadataValidRep properties)
    (stringCount : tombstoneCount properties.stringOrder = properties.stringTombstones)
    (stringRatio : properties.stringOrder.size < compactionThreshold ∨
      properties.stringTombstones * 2 ≤ properties.stringOrder.size) :
    let compacted := compactSymbols properties.entries properties.symbolOrder
    ValidRep ⟨compacted.1, properties.stringOrder, compacted.2,
      properties.stringTombstones, 0⟩ := by
  have covered : ∀ key, some key ∈ properties.symbolOrder →
      ∃ stored, properties.entries.get? (.symbol key) = some stored := fun _ member =>
    symbolSlot_covered metadata member
  have outputEq := compactOrder_output PropertyKey.symbol properties.entries
    properties.symbolOrder covered
  dsimp only
  refine ⟨compactSymbols_metadata properties metadata, stringCount, ?_, stringRatio, ?_⟩
  · change tombstoneCount (compactOrder PropertyKey.symbol properties.entries
      properties.symbolOrder).2 = 0
    rw [outputEq]
    exact tombstoneCount_map_some _
  · right
    simp

private theorem compactStrings_orderedStrings (properties : OrderedPropsRep)
    (valid : MetadataValidRep properties) :
    let compacted := compactStrings properties.entries properties.stringOrder
    orderedStrings ⟨compacted.1, compacted.2, properties.symbolOrder, 0,
      properties.symbolTombstones⟩ = orderedStrings properties := by
  have covered : ∀ key, some key ∈ properties.stringOrder →
      ∃ stored, properties.entries.get? (.string key) = some stored := fun _ member =>
    stringSlot_covered valid member
  have nextValid := compactStrings_metadata properties valid
  dsimp only
  unfold orderedStrings
  rw [liveOrder_eq_filterMap .string _ _ (fun key member => stringSlot_covered nextValid member)]
  change List.map PropertyKey.string
    (List.filterMap id (compactOrder PropertyKey.string properties.entries properties.stringOrder).2.toList) = _
  rw [compactOrder_output .string properties.entries properties.stringOrder covered,
    liveOrder_eq_filterMap .string properties.entries properties.stringOrder covered]
  simp

private theorem compactStrings_orderedSymbols (properties : OrderedPropsRep) :
    let compacted := compactStrings properties.entries properties.stringOrder
    orderedSymbols ⟨compacted.1, compacted.2, properties.symbolOrder, 0,
      properties.symbolTombstones⟩ = orderedSymbols properties := by
  dsimp only
  unfold orderedSymbols compactStrings
  rw [liveOrder_entries_ext .symbol _ properties.entries properties.symbolOrder
    (fun key => compactOrder_contains .string properties.entries properties.stringOrder (.symbol key))]

private theorem compactSymbols_orderedStrings (properties : OrderedPropsRep) :
    let compacted := compactSymbols properties.entries properties.symbolOrder
    orderedStrings ⟨compacted.1, properties.stringOrder, compacted.2,
      properties.stringTombstones, 0⟩ = orderedStrings properties := by
  dsimp only
  unfold orderedStrings compactSymbols
  rw [liveOrder_entries_ext .string _ properties.entries properties.stringOrder
    (fun key => compactOrder_contains .symbol properties.entries properties.symbolOrder (.string key))]

private theorem compactSymbols_orderedSymbols (properties : OrderedPropsRep)
    (valid : MetadataValidRep properties) :
    let compacted := compactSymbols properties.entries properties.symbolOrder
    orderedSymbols ⟨compacted.1, properties.stringOrder, compacted.2,
      properties.stringTombstones, 0⟩ = orderedSymbols properties := by
  have covered : ∀ key, some key ∈ properties.symbolOrder →
      ∃ stored, properties.entries.get? (.symbol key) = some stored := fun _ member =>
    symbolSlot_covered valid member
  have nextValid := compactSymbols_metadata properties valid
  dsimp only
  unfold orderedSymbols
  rw [liveOrder_eq_filterMap .symbol _ _ (fun key member => symbolSlot_covered nextValid member)]
  change List.map PropertyKey.symbol
    (List.filterMap id (compactOrder PropertyKey.symbol properties.entries properties.symbolOrder).2.toList) = _
  rw [compactOrder_output .symbol properties.entries properties.symbolOrder covered,
    liveOrder_eq_filterMap .symbol properties.entries properties.symbolOrder covered]
  simp

private theorem updateMetadata_valid (properties : OrderedPropsRep)
    (valid : MetadataValidRep properties) (key : PropertyKey) (stored : StoredProperty)
    (found : properties.entries.get? key = some stored) (descriptor : PropertyDescriptor) :
    MetadataValidRep { properties with entries := (properties.entries.insert key
      ⟨descriptor, stored.orderPosition⟩) } := by
  refine ⟨?_, ?_, ?_⟩
  · intro query result queryFound
    change (properties.entries.insert key { stored with descriptor })[query]? = some result at queryFound
    rw [Std.HashMap.getElem?_insert] at queryFound
    split at queryFound
    · rename_i equal
      have keyEqual : key = query := LawfulBEq.eq_of_beq equal
      subst query
      have resultEqual := Option.some.inj queryFound
      subst result
      simpa [EntryValid] using valid.1 key stored found
    · exact valid.1 query result queryFound
  · intro position inBounds
    have oldBound : position < properties.stringOrder.size := by simpa using inBounds
    have oldValid := valid.2.1 position (by simpa using oldBound)
    cases slot : properties.stringOrder[position] with
    | none =>
        simp [Array.getElem_zipIdx, slot, StringSlotValid] at oldValid ⊢
    | some stringKey =>
        simp [Array.getElem_zipIdx, slot, StringSlotValid] at oldValid
        rcases oldValid with ⟨oldStored, oldFound, nonIndex, oldPosition⟩
        by_cases equal : key = .string stringKey
        · subst key
          change properties.entries[PropertyKey.string stringKey]? = some stored at found
          rw [found] at oldFound
          have storedEqual := Option.some.inj oldFound
          subst oldStored
          simp [Array.getElem_zipIdx, slot, StringSlotValid, nonIndex, oldPosition]
        · simp [Array.getElem_zipIdx, slot, StringSlotValid]
          have newFound : (properties.entries.insert key
              { stored with descriptor })[PropertyKey.string stringKey]? = some oldStored := by
            rw [Std.HashMap.getElem?_insert]
            simp [equal, oldFound]
          exact ⟨oldStored, newFound, nonIndex, oldPosition⟩
  · intro position inBounds
    have oldBound : position < properties.symbolOrder.size := by simpa using inBounds
    have oldValid := valid.2.2 position (by simpa using oldBound)
    cases slot : properties.symbolOrder[position] with
    | none =>
        simp [Array.getElem_zipIdx, slot, SymbolSlotValid] at oldValid ⊢
    | some symbolKey =>
        simp [Array.getElem_zipIdx, slot, SymbolSlotValid] at oldValid
        rcases oldValid with ⟨oldStored, oldFound, oldPosition⟩
        by_cases equal : key = .symbol symbolKey
        · subst key
          change properties.entries[PropertyKey.symbol symbolKey]? = some stored at found
          rw [found] at oldFound
          have storedEqual := Option.some.inj oldFound
          subst oldStored
          simp [Array.getElem_zipIdx, slot, SymbolSlotValid, oldPosition]
        · simp [Array.getElem_zipIdx, slot, SymbolSlotValid]
          have newFound : (properties.entries.insert key
              { stored with descriptor })[PropertyKey.symbol symbolKey]? = some oldStored := by
            rw [Std.HashMap.getElem?_insert]
            simp [equal, oldFound]
          exact ⟨oldStored, newFound, oldPosition⟩

private theorem update_valid (properties : OrderedPropsRep) (valid : ValidRep properties)
    (key : PropertyKey) (stored : StoredProperty) (found : properties.entries.get? key = some stored)
    (descriptor : PropertyDescriptor) :
    ValidRep { properties with entries := (properties.entries.insert key
      ⟨descriptor, stored.orderPosition⟩) } :=
  ⟨updateMetadata_valid properties valid.1 key stored found descriptor, valid.2⟩

private theorem insertIndexMetadata_valid (properties : OrderedPropsRep)
    (valid : MetadataValidRep properties) (key : JSString) (index : Nat)
    (parsed : PropertyKey.arrayIndex? key = some index)
    (absent : properties.entries.get? (.string key) = none) (descriptor : PropertyDescriptor) :
    MetadataValidRep { properties with entries := (properties.entries.insert (.string key)
      ⟨descriptor, none⟩) } := by
  refine ⟨?_, ?_, ?_⟩
  · intro query result queryFound
    change (properties.entries.insert (.string key) ⟨descriptor, none⟩)[query]? = some result at queryFound
    rw [Std.HashMap.getElem?_insert] at queryFound
    split at queryFound
    · rename_i equal
      have keyEqual : PropertyKey.string key = query := LawfulBEq.eq_of_beq equal
      subst query
      have resultEqual := Option.some.inj queryFound
      subst result
      simp [EntryValid, parsed]
    · exact valid.1 query result queryFound
  · intro position inBounds
    have oldBound : position < properties.stringOrder.size := by simpa using inBounds
    have oldValid := valid.2.1 position (by simpa using oldBound)
    cases slot : properties.stringOrder[position] with
    | none =>
        simp [Array.getElem_zipIdx, slot, StringSlotValid] at oldValid ⊢
    | some oldKey =>
        simp [Array.getElem_zipIdx, slot, StringSlotValid] at oldValid
        rcases oldValid with ⟨oldStored, oldFound, nonIndex, oldPosition⟩
        have keyNe : PropertyKey.string key ≠ .string oldKey := by
          intro equal
          cases equal
          change properties.entries[PropertyKey.string key]? = some oldStored at oldFound
          change properties.entries[PropertyKey.string key]? = none at absent
          rw [absent] at oldFound
          contradiction
        simp [Array.getElem_zipIdx, slot, StringSlotValid]
        refine ⟨oldStored, ?_, nonIndex, oldPosition⟩
        rw [Std.HashMap.getElem?_insert]
        simp [keyNe, oldFound]
  · intro position inBounds
    have oldBound : position < properties.symbolOrder.size := by simpa using inBounds
    have oldValid := valid.2.2 position (by simpa using oldBound)
    cases slot : properties.symbolOrder[position] with
    | none =>
        simp [Array.getElem_zipIdx, slot, SymbolSlotValid] at oldValid ⊢
    | some oldKey =>
        simp [Array.getElem_zipIdx, slot, SymbolSlotValid] at oldValid
        rcases oldValid with ⟨oldStored, oldFound, oldPosition⟩
        simp [Array.getElem_zipIdx, slot, SymbolSlotValid]
        refine ⟨oldStored, ?_, oldPosition⟩
        rw [Std.HashMap.getElem?_insert]
        simpa using oldFound

private theorem insertIndex_valid (properties : OrderedPropsRep) (valid : ValidRep properties)
    (key : JSString) (index : Nat) (parsed : PropertyKey.arrayIndex? key = some index)
    (absent : properties.entries.get? (.string key) = none) (descriptor : PropertyDescriptor) :
    ValidRep { properties with entries := (properties.entries.insert (.string key)
      ⟨descriptor, none⟩) } :=
  ⟨insertIndexMetadata_valid properties valid.1 key index parsed absent descriptor, valid.2⟩

private theorem appendStringMetadata_valid (properties : OrderedPropsRep)
    (valid : MetadataValidRep properties) (key : JSString)
    (nonIndex : PropertyKey.arrayIndex? key = none)
    (absent : properties.entries.get? (.string key) = none) (descriptor : PropertyDescriptor) :
    MetadataValidRep
      ⟨properties.entries.insert (.string key) ⟨descriptor, some properties.stringOrder.size⟩,
        properties.stringOrder.push (some key), properties.symbolOrder,
        properties.stringTombstones, properties.symbolTombstones⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · intro query result queryFound
    change (properties.entries.insert (.string key)
      ⟨descriptor, some properties.stringOrder.size⟩)[query]? = some result at queryFound
    rw [Std.HashMap.getElem?_insert] at queryFound
    split at queryFound
    · rename_i equal
      have keyEqual : PropertyKey.string key = query := LawfulBEq.eq_of_beq equal
      subst query
      have resultEqual := Option.some.inj queryFound
      subst result
      simp [EntryValid, nonIndex, Array.getElem?_push]
    · rename_i different
      have oldValid := valid.1 query result queryFound
      cases query with
      | string oldKey =>
          cases parsed : PropertyKey.arrayIndex? oldKey with
          | some index => simpa [EntryValid, parsed] using oldValid
          | none =>
              simp [EntryValid, parsed] at oldValid ⊢
              rcases oldValid with ⟨position, storedPosition, slot⟩
              have before : position < properties.stringOrder.size :=
                (Array.getElem?_eq_some_iff.mp slot).choose
              exact ⟨position, storedPosition, by
                rw [Array.getElem?_push]
                simp [Nat.ne_of_lt before, slot]⟩
      | symbol oldKey => simpa [EntryValid] using oldValid
  · intro position inBounds
    have pushedBound : position < properties.stringOrder.size + 1 := by simpa using inBounds
    have positionLe : position ≤ properties.stringOrder.size := by omega
    rcases Nat.eq_or_lt_of_le positionLe with equal | before
    · subst position
      simp [Array.getElem_zipIdx, StringSlotValid, nonIndex]
    · have oldValid := valid.2.1 position (by simpa using before)
      cases slot : properties.stringOrder[position] with
      | none =>
          have pushedArrayBound : position < (properties.stringOrder.push (some key)).size := by
            simp; omega
          have pushedSlot : (properties.stringOrder.push (some key))[position]'pushedArrayBound = none := by
            simp [Array.getElem_push_lt before, slot]
          simp [Array.getElem_zipIdx, pushedSlot, StringSlotValid]
      | some oldKey =>
          simp [Array.getElem_zipIdx, slot, StringSlotValid] at oldValid
          rcases oldValid with ⟨oldStored, oldFound, oldNonIndex, oldPosition⟩
          have keyNe : PropertyKey.string key ≠ .string oldKey := by
            intro equal
            cases equal
            change properties.entries[PropertyKey.string key]? = some oldStored at oldFound
            change properties.entries[PropertyKey.string key]? = none at absent
            rw [absent] at oldFound
            contradiction
          have pushedArrayBound : position < (properties.stringOrder.push (some key)).size := by
            simp; omega
          have pushedSlot : (properties.stringOrder.push (some key))[position]'pushedArrayBound =
              some oldKey := by
            simp [Array.getElem_push_lt before, slot]
          simp [Array.getElem_zipIdx, pushedSlot, StringSlotValid]
          refine ⟨oldStored, ?_, oldNonIndex, oldPosition⟩
          rw [Std.HashMap.getElem?_insert]
          simp [keyNe, oldFound]
  · intro position inBounds
    have oldBound : position < properties.symbolOrder.size := by simpa using inBounds
    have oldValid := valid.2.2 position (by simpa using oldBound)
    cases slot : properties.symbolOrder[position] with
    | none =>
        simp [Array.getElem_zipIdx, slot, SymbolSlotValid] at oldValid ⊢
    | some oldKey =>
        simp [Array.getElem_zipIdx, slot, SymbolSlotValid] at oldValid
        rcases oldValid with ⟨oldStored, oldFound, oldPosition⟩
        simp [Array.getElem_zipIdx, slot, SymbolSlotValid]
        refine ⟨oldStored, ?_, oldPosition⟩
        rw [Std.HashMap.getElem?_insert]
        simpa using oldFound

private theorem appendSymbolMetadata_valid (properties : OrderedPropsRep)
    (valid : MetadataValidRep properties) (key : SymbolId)
    (absent : properties.entries.get? (.symbol key) = none) (descriptor : PropertyDescriptor) :
    MetadataValidRep
      ⟨properties.entries.insert (.symbol key) ⟨descriptor, some properties.symbolOrder.size⟩,
        properties.stringOrder, properties.symbolOrder.push (some key),
        properties.stringTombstones, properties.symbolTombstones⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · intro query result queryFound
    change (properties.entries.insert (.symbol key)
      ⟨descriptor, some properties.symbolOrder.size⟩)[query]? = some result at queryFound
    rw [Std.HashMap.getElem?_insert] at queryFound
    split at queryFound
    · rename_i equal
      have keyEqual : PropertyKey.symbol key = query := LawfulBEq.eq_of_beq equal
      subst query
      have resultEqual := Option.some.inj queryFound
      subst result
      simp [EntryValid, Array.getElem?_push]
    · have oldValid := valid.1 query result queryFound
      cases query with
      | string oldKey => simpa [EntryValid] using oldValid
      | symbol oldKey =>
          simp [EntryValid] at oldValid ⊢
          rcases oldValid with ⟨position, storedPosition, slot⟩
          have before : position < properties.symbolOrder.size :=
            (Array.getElem?_eq_some_iff.mp slot).choose
          exact ⟨position, storedPosition, by
            rw [Array.getElem?_push]
            simp [Nat.ne_of_lt before, slot]⟩
  · intro position inBounds
    have oldBound : position < properties.stringOrder.size := by simpa using inBounds
    have oldValid := valid.2.1 position (by simpa using oldBound)
    cases slot : properties.stringOrder[position] with
    | none =>
        simp [Array.getElem_zipIdx, slot, StringSlotValid] at oldValid ⊢
    | some oldKey =>
        simp [Array.getElem_zipIdx, slot, StringSlotValid] at oldValid
        rcases oldValid with ⟨oldStored, oldFound, oldNonIndex, oldPosition⟩
        simp [Array.getElem_zipIdx, slot, StringSlotValid]
        refine ⟨oldStored, ?_, oldNonIndex, oldPosition⟩
        rw [Std.HashMap.getElem?_insert]
        simpa using oldFound
  · intro position inBounds
    have pushedBound : position < properties.symbolOrder.size + 1 := by simpa using inBounds
    have positionLe : position ≤ properties.symbolOrder.size := by omega
    rcases Nat.eq_or_lt_of_le positionLe with equal | before
    · subst position
      simp [Array.getElem_zipIdx, SymbolSlotValid]
    · have oldValid := valid.2.2 position (by simpa using before)
      cases slot : properties.symbolOrder[position] with
      | none =>
          have pushedArrayBound : position < (properties.symbolOrder.push (some key)).size := by
            simp; omega
          have pushedSlot : (properties.symbolOrder.push (some key))[position]'pushedArrayBound = none := by
            simp [Array.getElem_push_lt before, slot]
          simp [Array.getElem_zipIdx, pushedSlot, SymbolSlotValid]
      | some oldKey =>
          simp [Array.getElem_zipIdx, slot, SymbolSlotValid] at oldValid
          rcases oldValid with ⟨oldStored, oldFound, oldPosition⟩
          have keyNe : PropertyKey.symbol key ≠ .symbol oldKey := by
            intro equal
            cases equal
            change properties.entries[PropertyKey.symbol key]? = some oldStored at oldFound
            change properties.entries[PropertyKey.symbol key]? = none at absent
            rw [absent] at oldFound
            contradiction
          have pushedArrayBound : position < (properties.symbolOrder.push (some key)).size := by
            simp; omega
          have pushedSlot : (properties.symbolOrder.push (some key))[position]'pushedArrayBound =
              some oldKey := by
            simp [Array.getElem_push_lt before, slot]
          simp [Array.getElem_zipIdx, pushedSlot, SymbolSlotValid]
          refine ⟨oldStored, ?_, oldPosition⟩
          rw [Std.HashMap.getElem?_insert]
          simp [keyNe, oldFound]

private theorem tombstoneCount_push_some (order : Array (Option α)) (key : α) :
    tombstoneCount (order.push (some key)) = tombstoneCount order := by
  unfold tombstoneCount
  rw [← Array.foldl_toList, Array.toList_push, List.foldl_append]
  simp

private theorem tombstoneCount_eq_listCountP (order : Array (Option α)) :
    tombstoneCount order = order.toList.countP Option.isNone := by
  unfold tombstoneCount
  rw [← Array.foldl_toList]
  have go : ∀ (slots : List (Option α)) (count : Nat),
      slots.foldl (fun count slot => if slot.isNone then count + 1 else count) count =
        count + slots.countP Option.isNone := by
    intro slots count
    induction slots generalizing count with
    | nil => simp
    | cons slot slots ih =>
        simp only [List.foldl_cons, List.countP_cons]
        cases slot with
        | none =>
            simp only [Option.isNone_none, ↓reduceIte]
            rw [ih]
            omega
        | some value =>
            simp only [Option.isNone_some]
            exact ih count
  simpa using go order.toList 0

private theorem tombstoneCount_tombstone_some (order : Array (Option α)) (position : Nat)
    (key : α) (slot : order[position]? = some (some key)) :
    tombstoneCount (tombstone order position) = tombstoneCount order + 1 := by
  have positionBound : position < order.size := (Array.getElem?_eq_some_iff.mp slot).choose
  have slotValue : order[position] = some key := by
    rw [Array.getElem?_eq_getElem positionBound] at slot
    exact Option.some.inj slot
  rw [tombstoneCount_eq_listCountP, tombstoneCount_eq_listCountP]
  simp [tombstone, positionBound, List.countP_set, slotValue]

private theorem insertRep_valid (properties : OrderedPropsRep) (key : PropertyKey)
    (descriptor : PropertyDescriptor) (valid : ValidRep properties) :
    ValidRep (insertRep properties key descriptor) := by
  unfold insertRep
  cases found : properties.entries.get? key with
  | some stored => exact update_valid properties valid key stored found descriptor
  | none =>
      cases key with
      | string stringKey =>
          cases parsed : PropertyKey.arrayIndex? stringKey with
          | some index =>
              simpa [found, parsed] using
                insertIndex_valid properties valid stringKey index parsed found descriptor
          | none =>
              simp only [parsed]
              let next : OrderedPropsRep :=
                ⟨properties.entries.insert (.string stringKey)
                    ⟨descriptor, some properties.stringOrder.size⟩,
                  properties.stringOrder.push (some stringKey), properties.symbolOrder,
                  properties.stringTombstones, properties.symbolTombstones⟩
              have metadata : MetadataValidRep next :=
                appendStringMetadata_valid properties valid.1 stringKey parsed found descriptor
              have stringCount : tombstoneCount next.stringOrder = next.stringTombstones := by
                change tombstoneCount (properties.stringOrder.push (some stringKey)) =
                  properties.stringTombstones
                rw [tombstoneCount_push_some, valid.2.1]
              have symbolCount : tombstoneCount next.symbolOrder = next.symbolTombstones := valid.2.2.1
              split
              · exact compactStrings_valid next metadata symbolCount valid.2.2.2.2
              · rename_i notCompact
                have ratio : next.stringOrder.size < compactionThreshold ∨
                    next.stringTombstones * 2 ≤ next.stringOrder.size := by
                  simp [shouldCompact] at notCompact
                  simp [next]
                  omega
                exact ⟨metadata, stringCount, symbolCount, ratio, valid.2.2.2.2⟩
      | symbol symbolKey =>
          simp only
          let next : OrderedPropsRep :=
            ⟨properties.entries.insert (.symbol symbolKey)
                ⟨descriptor, some properties.symbolOrder.size⟩,
              properties.stringOrder, properties.symbolOrder.push (some symbolKey),
              properties.stringTombstones, properties.symbolTombstones⟩
          have metadata : MetadataValidRep next :=
            appendSymbolMetadata_valid properties valid.1 symbolKey found descriptor
          have stringCount : tombstoneCount next.stringOrder = next.stringTombstones := valid.2.1
          have symbolCount : tombstoneCount next.symbolOrder = next.symbolTombstones := by
            change tombstoneCount (properties.symbolOrder.push (some symbolKey)) =
              properties.symbolTombstones
            rw [tombstoneCount_push_some, valid.2.2.1]
          split
          · exact compactSymbols_valid next metadata stringCount valid.2.2.2.1
          · rename_i notCompact
            have ratio : next.symbolOrder.size < compactionThreshold ∨
                next.symbolTombstones * 2 ≤ next.symbolOrder.size := by
              simp [shouldCompact] at notCompact
              simp [next]
              omega
            exact ⟨metadata, stringCount, symbolCount, valid.2.2.2.1, ratio⟩

private theorem insertRep_lookup (properties : OrderedPropsRep) (key query : PropertyKey)
    (descriptor : PropertyDescriptor) :
    ((insertRep properties key descriptor).entries.get? query).map (·.descriptor) =
      if key == query then some descriptor else (properties.entries.get? query).map (·.descriptor) := by
  unfold insertRep
  cases found : properties.entries.get? key with
  | some stored =>
      simp only
      change Option.map _ ((properties.entries.insert key { stored with descriptor })[query]?) = _
      rw [Std.HashMap.getElem?_insert]
      split <;> simp_all
  | none =>
      cases key with
      | string stringKey =>
          cases parsed : PropertyKey.arrayIndex? stringKey with
          | some index =>
              simp only [parsed]
              change Option.map _ ((properties.entries.insert (.string stringKey)
                ⟨descriptor, none⟩)[query]?) = _
              rw [Std.HashMap.getElem?_insert]
              split <;> simp_all
          | none =>
              simp only [parsed]
              split
              · rename_i compact
                change Option.map _ ((compactStrings _ _).1.get? query) = _
                unfold compactStrings
                rw [compactOrder_descriptor]
                change Option.map _ ((properties.entries.insert (.string stringKey)
                  ⟨descriptor, some properties.stringOrder.size⟩)[query]?) = _
                rw [Std.HashMap.getElem?_insert]
                split <;> simp_all
              · change Option.map _ ((properties.entries.insert (.string stringKey)
                  ⟨descriptor, some properties.stringOrder.size⟩)[query]?) = _
                rw [Std.HashMap.getElem?_insert]
                split <;> simp_all
      | symbol symbolKey =>
          simp only
          split
          · change Option.map _ ((compactSymbols _ _).1.get? query) = _
            unfold compactSymbols
            rw [compactOrder_descriptor]
            change Option.map _ ((properties.entries.insert (.symbol symbolKey)
              ⟨descriptor, some properties.symbolOrder.size⟩)[query]?) = _
            rw [Std.HashMap.getElem?_insert]
            split <;> simp_all
          · change Option.map _ ((properties.entries.insert (.symbol symbolKey)
              ⟨descriptor, some properties.symbolOrder.size⟩)[query]?) = _
            rw [Std.HashMap.getElem?_insert]
            split <;> simp_all

private theorem insertRep_fresh_string_order (properties : OrderedPropsRep)
    (valid : MetadataValidRep properties) (key : JSString)
    (nonIndex : PropertyKey.arrayIndex? key = none)
    (absent : properties.entries.get? (.string key) = none) (descriptor : PropertyDescriptor) :
    orderedStrings (insertRep properties (.string key) descriptor) =
      orderedStrings properties ++ [.string key] ∧
    orderedSymbols (insertRep properties (.string key) descriptor) = orderedSymbols properties := by
  let next : OrderedPropsRep :=
    ⟨properties.entries.insert (.string key) ⟨descriptor, some properties.stringOrder.size⟩,
      properties.stringOrder.push (some key), properties.symbolOrder,
      properties.stringTombstones, properties.symbolTombstones⟩
  have nextValid : MetadataValidRep next :=
    appendStringMetadata_valid properties valid key nonIndex absent descriptor
  have covered : ∀ orderKey, some orderKey ∈ properties.stringOrder →
      ∃ stored, properties.entries.get? (.string orderKey) = some stored := fun _ member =>
    stringSlot_covered valid member
  have pushed := liveOrder_push_fresh PropertyKey.string (by
      intro left right equal
      exact PropertyKey.string.inj equal)
    properties.entries properties.stringOrder key
      ⟨descriptor, some properties.stringOrder.size⟩ absent covered
  have symbolsUnchanged : orderedSymbols next = orderedSymbols properties := by
    unfold orderedSymbols
    apply congrArg (List.map PropertyKey.symbol)
    apply liveOrder_entries_ext
    intro symbolKey
    rw [Std.HashMap.contains_insert]
    simp
  unfold insertRep
  simp only [absent]
  rw [nonIndex]
  simp only
  split
  · constructor
    · rw [compactStrings_orderedStrings next nextValid]
      unfold orderedStrings
      simpa [List.map_append] using (congrArg (List.map PropertyKey.string) pushed)
    · rw [compactStrings_orderedSymbols next, symbolsUnchanged]
  · constructor
    · unfold orderedStrings
      simpa [List.map_append] using (congrArg (List.map PropertyKey.string) pushed)
    · exact symbolsUnchanged

private theorem insertRep_fresh_symbol_order (properties : OrderedPropsRep)
    (valid : MetadataValidRep properties) (key : SymbolId)
    (absent : properties.entries.get? (.symbol key) = none) (descriptor : PropertyDescriptor) :
    orderedStrings (insertRep properties (.symbol key) descriptor) = orderedStrings properties ∧
    orderedSymbols (insertRep properties (.symbol key) descriptor) =
      orderedSymbols properties ++ [.symbol key] := by
  let next : OrderedPropsRep :=
    ⟨properties.entries.insert (.symbol key) ⟨descriptor, some properties.symbolOrder.size⟩,
      properties.stringOrder, properties.symbolOrder.push (some key),
      properties.stringTombstones, properties.symbolTombstones⟩
  have nextValid : MetadataValidRep next :=
    appendSymbolMetadata_valid properties valid key absent descriptor
  have covered : ∀ orderKey, some orderKey ∈ properties.symbolOrder →
      ∃ stored, properties.entries.get? (.symbol orderKey) = some stored := fun _ member =>
    symbolSlot_covered valid member
  have pushed := liveOrder_push_fresh PropertyKey.symbol (by
      intro left right equal
      exact PropertyKey.symbol.inj equal)
    properties.entries properties.symbolOrder key
      ⟨descriptor, some properties.symbolOrder.size⟩ absent covered
  have stringsUnchanged : orderedStrings next = orderedStrings properties := by
    unfold orderedStrings
    apply congrArg (List.map PropertyKey.string)
    apply liveOrder_entries_ext
    intro stringKey
    rw [Std.HashMap.contains_insert]
    simp
  unfold insertRep
  simp only [absent]
  split
  · constructor
    · rw [compactSymbols_orderedStrings next, stringsUnchanged]
    · rw [compactSymbols_orderedSymbols next nextValid]
      unfold orderedSymbols
      simpa [List.map_append] using (congrArg (List.map PropertyKey.symbol) pushed)
  · constructor
    · exact stringsUnchanged
    · unfold orderedSymbols
      simpa [List.map_append] using (congrArg (List.map PropertyKey.symbol) pushed)

private theorem insertRep_fresh_index_order (properties : OrderedPropsRep)
    (valid : MetadataValidRep properties) (key : JSString) (index : Nat)
    (parsed : PropertyKey.arrayIndex? key = some index)
    (absent : properties.entries.get? (.string key) = none) (descriptor : PropertyDescriptor) :
    orderedStrings (insertRep properties (.string key) descriptor) = orderedStrings properties ∧
    orderedSymbols (insertRep properties (.string key) descriptor) = orderedSymbols properties := by
  let next : OrderedPropsRep :=
    { properties with entries := properties.entries.insert (.string key) ⟨descriptor, none⟩ }
  have nextValid : MetadataValidRep next :=
    insertIndexMetadata_valid properties valid key index parsed absent descriptor
  have stringsUnchanged : orderedStrings next =
      orderedStrings properties := by
    unfold orderedStrings
    rw [liveOrder_eq_filterMap .string _ _ (fun orderKey member =>
      stringSlot_covered nextValid member), liveOrder_eq_filterMap .string _ _ (fun orderKey member =>
      stringSlot_covered valid member)]
  have symbolsUnchanged : orderedSymbols next = orderedSymbols properties := by
    unfold orderedSymbols
    rw [liveOrder_eq_filterMap .symbol _ _ (fun orderKey member =>
      symbolSlot_covered nextValid member), liveOrder_eq_filterMap .symbol _ _ (fun orderKey member =>
      symbolSlot_covered valid member)]
  unfold insertRep
  simp only [absent, parsed]
  exact ⟨stringsUnchanged, symbolsUnchanged⟩

private theorem deleteStringMetadata_valid (properties : OrderedPropsRep)
    (valid : MetadataValidRep properties) (key : JSString)
    (position : Nat)
    (slotAt : properties.stringOrder[position]? = some (some key)) :
    MetadataValidRep
      ⟨properties.entries.erase (.string key), tombstone properties.stringOrder position,
        properties.symbolOrder, properties.stringTombstones + 1, properties.symbolTombstones⟩ := by
  have positionBound : position < properties.stringOrder.size :=
    (Array.getElem?_eq_some_iff.mp slotAt).choose
  refine ⟨?_, ?_, ?_⟩
  · intro query result queryFound
    change (properties.entries.erase (.string key))[query]? = some result at queryFound
    rw [Std.HashMap.getElem?_erase] at queryFound
    split at queryFound
    · contradiction
    · rename_i different
      have oldValid := valid.1 query result queryFound
      cases query with
      | string oldKey =>
          cases parsed : PropertyKey.arrayIndex? oldKey with
          | some index => simpa [EntryValid, parsed] using oldValid
          | none =>
              simp [EntryValid, parsed] at oldValid ⊢
              rcases oldValid with ⟨oldPosition, resultPosition, oldSlot⟩
              have positionNe : oldPosition ≠ position := by
                intro equal
                subst oldPosition
                rw [slotAt] at oldSlot
                have keysEqual := Option.some.inj (Option.some.inj oldSlot)
                subst oldKey
                simp at different
              refine ⟨oldPosition, resultPosition, ?_⟩
              simp [tombstone, positionBound, Ne.symm positionNe, oldSlot]
      | symbol oldKey => simpa [EntryValid] using oldValid
  · intro oldPosition inBounds
    have orderBound : oldPosition < properties.stringOrder.size := by
      simpa [tombstone_size] using inBounds
    by_cases samePosition : oldPosition = position
    · subst oldPosition
      simp [tombstone, positionBound, Array.getElem_zipIdx, StringSlotValid]
    · have oldValid := valid.2.1 oldPosition (by simpa using orderBound)
      cases oldSlot : properties.stringOrder[oldPosition] with
      | none =>
          have tombstoneBound : oldPosition < (tombstone properties.stringOrder position).size := by
            simpa [tombstone_size] using orderBound
          have tombstonedSlot : (tombstone properties.stringOrder position)[oldPosition] = none := by
            simp [tombstone, positionBound, Array.getElem_set, Ne.symm samePosition, oldSlot]
          simp [Array.getElem_zipIdx, tombstonedSlot, StringSlotValid]
      | some oldKey =>
          simp [Array.getElem_zipIdx, oldSlot, StringSlotValid] at oldValid
          rcases oldValid with ⟨oldStored, oldFound, oldNonIndex, oldStoredPosition⟩
          have keyNe : PropertyKey.string key ≠ .string oldKey := by
            intro equal
            cases equal
            have slotValue : properties.stringOrder[position] = some key := by
              rw [Array.getElem?_eq_getElem positionBound] at slotAt
              exact Option.some.inj slotAt
            exact samePosition (stringSlot_unique valid positionBound orderBound
              slotValue oldSlot).symm
          have tombstoneBound : oldPosition < (tombstone properties.stringOrder position).size := by
            simpa [tombstone_size] using orderBound
          have tombstonedSlot : (tombstone properties.stringOrder position)[oldPosition] =
              some oldKey := by
            simp [tombstone, positionBound, Array.getElem_set, Ne.symm samePosition, oldSlot]
          simp [Array.getElem_zipIdx, tombstonedSlot, StringSlotValid]
          refine ⟨oldStored, ?_, oldNonIndex, oldStoredPosition⟩
          rw [Std.HashMap.getElem?_erase]
          simp [keyNe, oldFound]
  · intro oldPosition inBounds
    have oldBound : oldPosition < properties.symbolOrder.size := by simpa using inBounds
    have oldValid := valid.2.2 oldPosition (by simpa using oldBound)
    cases oldSlot : properties.symbolOrder[oldPosition] with
    | none =>
        simp [Array.getElem_zipIdx, oldSlot, SymbolSlotValid] at oldValid ⊢
    | some oldKey =>
        simp [Array.getElem_zipIdx, oldSlot, SymbolSlotValid] at oldValid
        rcases oldValid with ⟨oldStored, oldFound, oldStoredPosition⟩
        simp [Array.getElem_zipIdx, oldSlot, SymbolSlotValid]
        refine ⟨oldStored, ?_, oldStoredPosition⟩
        rw [Std.HashMap.getElem?_erase]
        simpa using oldFound

private theorem deleteSymbolMetadata_valid (properties : OrderedPropsRep)
    (valid : MetadataValidRep properties) (key : SymbolId)
    (position : Nat)
    (slotAt : properties.symbolOrder[position]? = some (some key)) :
    MetadataValidRep
      ⟨properties.entries.erase (.symbol key), properties.stringOrder,
        tombstone properties.symbolOrder position, properties.stringTombstones,
        properties.symbolTombstones + 1⟩ := by
  have positionBound : position < properties.symbolOrder.size :=
    (Array.getElem?_eq_some_iff.mp slotAt).choose
  refine ⟨?_, ?_, ?_⟩
  · intro query result queryFound
    change (properties.entries.erase (.symbol key))[query]? = some result at queryFound
    rw [Std.HashMap.getElem?_erase] at queryFound
    split at queryFound
    · contradiction
    · rename_i different
      have oldValid := valid.1 query result queryFound
      cases query with
      | string oldKey => simpa [EntryValid] using oldValid
      | symbol oldKey =>
          simp [EntryValid] at oldValid ⊢
          rcases oldValid with ⟨oldPosition, resultPosition, oldSlot⟩
          have positionNe : oldPosition ≠ position := by
            intro equal
            subst oldPosition
            rw [slotAt] at oldSlot
            have keysEqual := Option.some.inj (Option.some.inj oldSlot)
            subst oldKey
            simp at different
          refine ⟨oldPosition, resultPosition, ?_⟩
          simp [tombstone, positionBound, Ne.symm positionNe, oldSlot]
  · intro oldPosition inBounds
    have oldBound : oldPosition < properties.stringOrder.size := by simpa using inBounds
    have oldValid := valid.2.1 oldPosition (by simpa using oldBound)
    cases oldSlot : properties.stringOrder[oldPosition] with
    | none =>
        simp [Array.getElem_zipIdx, oldSlot, StringSlotValid] at oldValid ⊢
    | some oldKey =>
        simp [Array.getElem_zipIdx, oldSlot, StringSlotValid] at oldValid
        rcases oldValid with ⟨oldStored, oldFound, oldNonIndex, oldStoredPosition⟩
        simp [Array.getElem_zipIdx, oldSlot, StringSlotValid]
        refine ⟨oldStored, ?_, oldNonIndex, oldStoredPosition⟩
        rw [Std.HashMap.getElem?_erase]
        simpa using oldFound
  · intro oldPosition inBounds
    have orderBound : oldPosition < properties.symbolOrder.size := by
      simpa [tombstone_size] using inBounds
    by_cases samePosition : oldPosition = position
    · subst oldPosition
      simp [tombstone, positionBound, Array.getElem_zipIdx, SymbolSlotValid]
    · have oldValid := valid.2.2 oldPosition (by simpa using orderBound)
      cases oldSlot : properties.symbolOrder[oldPosition] with
      | none =>
          have tombstoneBound : oldPosition < (tombstone properties.symbolOrder position).size := by
            simpa [tombstone_size] using orderBound
          have tombstonedSlot : (tombstone properties.symbolOrder position)[oldPosition] = none := by
            simp [tombstone, positionBound, Array.getElem_set, Ne.symm samePosition, oldSlot]
          simp [Array.getElem_zipIdx, tombstonedSlot, SymbolSlotValid]
      | some oldKey =>
          simp [Array.getElem_zipIdx, oldSlot, SymbolSlotValid] at oldValid
          rcases oldValid with ⟨oldStored, oldFound, oldStoredPosition⟩
          have keyNe : PropertyKey.symbol key ≠ .symbol oldKey := by
            intro equal
            cases equal
            have slotValue : properties.symbolOrder[position] = some key := by
              rw [Array.getElem?_eq_getElem positionBound] at slotAt
              exact Option.some.inj slotAt
            exact samePosition (symbolSlot_unique valid positionBound orderBound
              slotValue oldSlot).symm
          have tombstoneBound : oldPosition < (tombstone properties.symbolOrder position).size := by
            simpa [tombstone_size] using orderBound
          have tombstonedSlot : (tombstone properties.symbolOrder position)[oldPosition] =
              some oldKey := by
            simp [tombstone, positionBound, Array.getElem_set, Ne.symm samePosition, oldSlot]
          simp [Array.getElem_zipIdx, tombstonedSlot, SymbolSlotValid]
          refine ⟨oldStored, ?_, oldStoredPosition⟩
          rw [Std.HashMap.getElem?_erase]
          simp [keyNe, oldFound]

private theorem eraseIndexMetadata_valid (properties : OrderedPropsRep)
    (valid : MetadataValidRep properties) (key : JSString) (index : Nat)
    (parsed : PropertyKey.arrayIndex? key = some index) :
    MetadataValidRep { properties with entries := properties.entries.erase (.string key) } := by
  refine ⟨?_, ?_, ?_⟩
  · intro query result queryFound
    change (properties.entries.erase (.string key))[query]? = some result at queryFound
    rw [Std.HashMap.getElem?_erase] at queryFound
    split at queryFound
    · contradiction
    · exact valid.1 query result queryFound
  · intro position inBounds
    have oldBound : position < properties.stringOrder.size := by simpa using inBounds
    have oldValid := valid.2.1 position (by simpa using oldBound)
    cases oldSlot : properties.stringOrder[position] with
    | none =>
        simp [Array.getElem_zipIdx, oldSlot, StringSlotValid] at oldValid ⊢
    | some oldKey =>
        simp [Array.getElem_zipIdx, oldSlot, StringSlotValid] at oldValid
        rcases oldValid with ⟨oldStored, oldFound, oldNonIndex, oldPosition⟩
        have keyNe : PropertyKey.string key ≠ .string oldKey := by
          intro equal
          cases equal
          rw [parsed] at oldNonIndex
          contradiction
        simp [Array.getElem_zipIdx, oldSlot, StringSlotValid]
        refine ⟨oldStored, ?_, oldNonIndex, oldPosition⟩
        rw [Std.HashMap.getElem?_erase]
        simp [keyNe, oldFound]
  · intro position inBounds
    have oldBound : position < properties.symbolOrder.size := by simpa using inBounds
    have oldValid := valid.2.2 position (by simpa using oldBound)
    cases oldSlot : properties.symbolOrder[position] with
    | none =>
        simp [Array.getElem_zipIdx, oldSlot, SymbolSlotValid] at oldValid ⊢
    | some oldKey =>
        simp [Array.getElem_zipIdx, oldSlot, SymbolSlotValid] at oldValid
        rcases oldValid with ⟨oldStored, oldFound, oldPosition⟩
        simp [Array.getElem_zipIdx, oldSlot, SymbolSlotValid]
        refine ⟨oldStored, ?_, oldPosition⟩
        rw [Std.HashMap.getElem?_erase]
        simpa using oldFound

private theorem eraseIndex_valid (properties : OrderedPropsRep) (valid : ValidRep properties)
    (key : JSString) (index : Nat) (parsed : PropertyKey.arrayIndex? key = some index) :
    ValidRep { properties with entries := properties.entries.erase (.string key) } :=
  ⟨eraseIndexMetadata_valid properties valid.1 key index parsed, valid.2⟩

private theorem deleteRep_valid (properties : OrderedPropsRep) (key : PropertyKey)
    (valid : ValidRep properties) : ValidRep (deleteRep properties key) := by
  unfold deleteRep
  cases found : properties.entries.get? key with
  | none => simp [valid]
  | some stored =>
      have entryValid := valid.1.1 key stored found
      cases key with
      | string stringKey =>
          cases parsed : PropertyKey.arrayIndex? stringKey with
          | some index =>
              have noPosition : stored.orderPosition = none := by
                simpa [EntryValid, parsed] using entryValid
              simp [noPosition]
              exact eraseIndex_valid properties valid stringKey index parsed
          | none =>
              simp [EntryValid, parsed] at entryValid
              rcases entryValid with ⟨position, storedPosition, slotAt⟩
              simp only [storedPosition, parsed, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
              let next : OrderedPropsRep :=
                ⟨properties.entries.erase (.string stringKey),
                  tombstone properties.stringOrder position, properties.symbolOrder,
                  properties.stringTombstones + 1, properties.symbolTombstones⟩
              have metadata : MetadataValidRep next :=
                deleteStringMetadata_valid properties valid.1 stringKey position slotAt
              have stringCount : tombstoneCount next.stringOrder = next.stringTombstones := by
                change tombstoneCount (tombstone properties.stringOrder position) =
                  properties.stringTombstones + 1
                rw [tombstoneCount_tombstone_some _ _ stringKey slotAt, valid.2.1]
              have symbolCount : tombstoneCount next.symbolOrder = next.symbolTombstones := valid.2.2.1
              unfold deleteString
              by_cases compact : shouldCompact (tombstone properties.stringOrder position).size
                  (properties.stringTombstones + 1) = true
              · simp only [compact, ↓reduceIte]
                exact compactStrings_valid next metadata symbolCount valid.2.2.2.2
              · have notCompact : shouldCompact (tombstone properties.stringOrder position).size
                    (properties.stringTombstones + 1) = false := by
                  cases equation : shouldCompact (tombstone properties.stringOrder position).size
                      (properties.stringTombstones + 1) with
                  | false => rfl
                  | true => exact False.elim (compact equation)
                simp only [notCompact, Bool.false_eq_true, ↓reduceIte]
                have ratio : next.stringOrder.size < compactionThreshold ∨
                    next.stringTombstones * 2 ≤ next.stringOrder.size := by
                  rw [tombstone_size] at notCompact
                  simp [shouldCompact] at notCompact
                  simp [next, tombstone_size]
                  omega
                exact ⟨metadata, stringCount, symbolCount, ratio, valid.2.2.2.2⟩
      | symbol symbolKey =>
          simp [EntryValid] at entryValid
          rcases entryValid with ⟨position, storedPosition, slotAt⟩
          simp only [storedPosition]
          let next : OrderedPropsRep :=
            ⟨properties.entries.erase (.symbol symbolKey), properties.stringOrder,
              tombstone properties.symbolOrder position, properties.stringTombstones,
              properties.symbolTombstones + 1⟩
          have metadata : MetadataValidRep next :=
            deleteSymbolMetadata_valid properties valid.1 symbolKey position slotAt
          have stringCount : tombstoneCount next.stringOrder = next.stringTombstones := valid.2.1
          have symbolCount : tombstoneCount next.symbolOrder = next.symbolTombstones := by
            change tombstoneCount (tombstone properties.symbolOrder position) =
              properties.symbolTombstones + 1
            rw [tombstoneCount_tombstone_some _ _ symbolKey slotAt, valid.2.2.1]
          unfold deleteSymbol
          by_cases compact : shouldCompact (tombstone properties.symbolOrder position).size
              (properties.symbolTombstones + 1) = true
          · simp only [compact, ↓reduceIte]
            exact compactSymbols_valid next metadata stringCount valid.2.2.2.1
          · have notCompact : shouldCompact (tombstone properties.symbolOrder position).size
                (properties.symbolTombstones + 1) = false := by
              cases equation : shouldCompact (tombstone properties.symbolOrder position).size
                  (properties.symbolTombstones + 1) with
              | false => rfl
              | true => exact False.elim (compact equation)
            simp only [notCompact, Bool.false_eq_true, ↓reduceIte]
            have ratio : next.symbolOrder.size < compactionThreshold ∨
                next.symbolTombstones * 2 ≤ next.symbolOrder.size := by
              rw [tombstone_size] at notCompact
              simp [shouldCompact] at notCompact
              simp [next, tombstone_size]
              omega
            exact ⟨metadata, stringCount, symbolCount, valid.2.2.2.1, ratio⟩

private theorem deleteRep_lookup (properties : OrderedPropsRep) (key query : PropertyKey)
    (valid : ValidRep properties) :
    ((deleteRep properties key).entries.get? query).map (·.descriptor) =
      if key == query then none else (properties.entries.get? query).map (·.descriptor) := by
  unfold deleteRep
  cases found : properties.entries.get? key with
  | none =>
      by_cases equal : key = query
      · subst query
        have absent : ¬key ∈ properties.entries := by
          intro member
          have present := Std.HashMap.getElem?_eq_some_getElem member
          change properties.entries.get? key = some _ at present
          rw [found] at present
          contradiction
        simp [absent]
      · simp [equal]
  | some stored =>
      have entryValid := valid.1.1 key stored found
      cases key with
      | string stringKey =>
          cases parsed : PropertyKey.arrayIndex? stringKey with
          | some index =>
              have noPosition : stored.orderPosition = none := by
                simpa [EntryValid, parsed] using entryValid
              simp only [noPosition]
              change Option.map _ ((properties.entries.erase (.string stringKey))[query]?) = _
              rw [Std.HashMap.getElem?_erase]
              split <;> simp_all
          | none =>
              simp [EntryValid, parsed] at entryValid
              rcases entryValid with ⟨position, storedPosition, slotAt⟩
              simp only [storedPosition, parsed, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
              unfold deleteString
              by_cases compact : shouldCompact (tombstone properties.stringOrder position).size
                  (properties.stringTombstones + 1) = true
              · simp only [compact, ↓reduceIte]
                change Option.map _ ((compactStrings _ _).1.get? query) = _
                unfold compactStrings
                rw [compactOrder_descriptor]
                change Option.map _ ((properties.entries.erase (.string stringKey))[query]?) = _
                rw [Std.HashMap.getElem?_erase]
                split <;> simp_all
              · have notCompact : shouldCompact (tombstone properties.stringOrder position).size
                    (properties.stringTombstones + 1) = false := by
                  cases equation : shouldCompact (tombstone properties.stringOrder position).size
                      (properties.stringTombstones + 1) with
                  | false => rfl
                  | true => exact False.elim (compact equation)
                simp only [notCompact, Bool.false_eq_true, ↓reduceIte]
                change Option.map _ ((properties.entries.erase (.string stringKey))[query]?) = _
                rw [Std.HashMap.getElem?_erase]
                split <;> simp_all
      | symbol symbolKey =>
          simp [EntryValid] at entryValid
          rcases entryValid with ⟨position, storedPosition, slotAt⟩
          simp only [storedPosition]
          unfold deleteSymbol
          by_cases compact : shouldCompact (tombstone properties.symbolOrder position).size
              (properties.symbolTombstones + 1) = true
          · simp only [compact, ↓reduceIte]
            change Option.map _ ((compactSymbols _ _).1.get? query) = _
            unfold compactSymbols
            rw [compactOrder_descriptor]
            change Option.map _ ((properties.entries.erase (.symbol symbolKey))[query]?) = _
            rw [Std.HashMap.getElem?_erase]
            split <;> simp_all
          · have notCompact : shouldCompact (tombstone properties.symbolOrder position).size
                (properties.symbolTombstones + 1) = false := by
              cases equation : shouldCompact (tombstone properties.symbolOrder position).size
                  (properties.symbolTombstones + 1) with
              | false => rfl
              | true => exact False.elim (compact equation)
            simp only [notCompact, Bool.false_eq_true, ↓reduceIte]
            change Option.map _ ((properties.entries.erase (.symbol symbolKey))[query]?) = _
            rw [Std.HashMap.getElem?_erase]
            split <;> simp_all

private theorem mem_sortedIndices_iff (properties : OrderedPropsRep) (key : PropertyKey) :
    key ∈ sortedIndices properties ↔
      (properties.entries.get? key).isSome ∧ match key with
        | .string stringKey => (PropertyKey.arrayIndex? stringKey).isSome
        | .symbol _ => False := by
  unfold sortedIndices
  rw [List.mem_map]
  simp only [List.mem_mergeSort]
  constructor
  · rintro ⟨entry, entryMember, rfl⟩
    simp only [List.mem_filterMap] at entryMember
    rcases entryMember with ⟨source, sourceMember, sourceValue⟩
    cases source with
    | mk sourceKey stored =>
        cases sourceKey with
        | string stringKey =>
            simp [indexEntry?] at sourceValue
            rcases sourceValue with ⟨index, parsed, rfl⟩
            have found := Std.HashMap.mem_toList_iff_getElem?_eq_some.mp sourceMember
            simp [found, parsed]
        | symbol symbolKey => simp [indexEntry?] at sourceValue
  · intro condition
    cases key with
    | string stringKey =>
        cases found : properties.entries.get? (.string stringKey) with
        | none =>
            have present := condition.1
            rw [found] at present
            contradiction
        | some stored =>
            cases parsed : PropertyKey.arrayIndex? stringKey with
            | none => simp [parsed] at condition
            | some index =>
                refine ⟨(index, .string stringKey), ?_, rfl⟩
                simp only [List.mem_filterMap]
                exact ⟨(.string stringKey, stored),
                  Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr found, by simp [indexEntry?, parsed]⟩
    | symbol symbolKey => simp at condition

private theorem mem_orderedStrings_iff (properties : OrderedPropsRep)
    (valid : MetadataValidRep properties) (key : JSString) :
    PropertyKey.string key ∈ orderedStrings properties ↔
      (properties.entries.get? (.string key)).isSome ∧ PropertyKey.arrayIndex? key = none := by
  have covered : ∀ key, some key ∈ properties.stringOrder →
      ∃ stored, properties.entries.get? (.string key) = some stored := fun _ member =>
    stringSlot_covered valid member
  have liveEq := liveOrder_eq_filterMap PropertyKey.string properties.entries
    properties.stringOrder covered
  rw [orderedStrings, List.mem_map]
  constructor
  · rintro ⟨liveKey, member, equal⟩
    have keysEqual := PropertyKey.string.inj equal
    subst liveKey
    rw [liveEq] at member
    obtain ⟨slot, slotMember, slotValue⟩ := List.mem_filterMap.mp member
    simp only [id_eq] at slotValue
    subst slot
    obtain ⟨stored, found⟩ := stringSlot_covered valid (Array.mem_toList_iff.mp slotMember)
    refine ⟨?_, stringSlot_nonIndex valid (Array.mem_toList_iff.mp slotMember)⟩
    rw [found]
    rfl
  · rintro ⟨present, nonIndex⟩
    cases found : properties.entries.get? (.string key) with
    | none =>
        rw [found] at present
        contradiction
    | some stored =>
        have entryValid := valid.1 (.string key) stored found
        simp [EntryValid, nonIndex] at entryValid
        rcases entryValid with ⟨position, storedPosition, slot⟩
        refine ⟨key, ?_, rfl⟩
        rw [liveEq]
        exact List.mem_filterMap.mpr ⟨some key,
          Array.mem_toList_iff.mpr (Array.mem_of_getElem? slot), rfl⟩

private theorem mem_orderedSymbols_iff (properties : OrderedPropsRep)
    (valid : MetadataValidRep properties) (key : SymbolId) :
    PropertyKey.symbol key ∈ orderedSymbols properties ↔
      (properties.entries.get? (.symbol key)).isSome := by
  have covered : ∀ key, some key ∈ properties.symbolOrder →
      ∃ stored, properties.entries.get? (.symbol key) = some stored := fun _ member =>
    symbolSlot_covered valid member
  have liveEq := liveOrder_eq_filterMap PropertyKey.symbol properties.entries
    properties.symbolOrder covered
  rw [orderedSymbols, List.mem_map]
  constructor
  · rintro ⟨liveKey, member, equal⟩
    have keysEqual := PropertyKey.symbol.inj equal
    subst liveKey
    rw [liveEq] at member
    obtain ⟨slot, slotMember, slotValue⟩ := List.mem_filterMap.mp member
    simp only [id_eq] at slotValue
    subst slot
    obtain ⟨stored, found⟩ := symbolSlot_covered valid (Array.mem_toList_iff.mp slotMember)
    rw [found]
    rfl
  · intro present
    cases found : properties.entries.get? (.symbol key) with
    | none =>
        rw [found] at present
        contradiction
    | some stored =>
        have entryValid := valid.1 (.symbol key) stored found
        simp [EntryValid] at entryValid
        rcases entryValid with ⟨position, storedPosition, slot⟩
        refine ⟨key, ?_, rfl⟩
        rw [liveEq]
        exact List.mem_filterMap.mpr ⟨some key,
          Array.mem_toList_iff.mpr (Array.mem_of_getElem? slot), rfl⟩

private theorem sortedIndices_nodup (properties : OrderedPropsRep) :
    (sortedIndices properties).Nodup := by
  have distinct := Std.HashMap.distinct_keys_toList (m := properties.entries)
  have filtered : (properties.entries.toList.filterMap indexEntry?).map (·.2) |>.Nodup := by
    rw [List.nodup_iff_pairwise_ne, List.pairwise_map, List.pairwise_filterMap]
    apply distinct.imp
    intro left right keysNe leftIndex leftValue rightIndex rightValue
    cases left with
    | mk leftKey leftStored =>
        cases right with
        | mk rightKey rightStored =>
            cases leftKey <;> cases rightKey <;> simp [indexEntry?] at leftValue rightValue ⊢
            rename_i leftKey rightKey
            rcases leftValue with ⟨leftParsed, leftParse, rfl⟩
            rcases rightValue with ⟨rightParsed, rightParse, rfl⟩
            intro equal
            have keysEqual := PropertyKey.string.inj equal
            subst rightKey
            simp [BEq.beq, PropertyKey.equal, JSString.equal] at keysNe
  unfold sortedIndices
  exact ((List.mergeSort_perm _ _).map (fun entry : Nat × PropertyKey => entry.2)).nodup_iff.mpr
    filtered

private theorem orderedStrings_nodup (properties : OrderedPropsRep)
    (valid : MetadataValidRep properties) : (orderedStrings properties).Nodup := by
  have covered : ∀ key, some key ∈ properties.stringOrder →
      ∃ stored, properties.entries.get? (.string key) = some stored := fun _ member =>
    stringSlot_covered valid member
  unfold orderedStrings
  rw [liveOrder_eq_filterMap .string properties.entries properties.stringOrder covered]
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
  exact (stringLiveOrder_nodup valid).imp fun notEqual => fun equal =>
    notEqual (PropertyKey.string.inj equal)

private theorem orderedSymbols_nodup (properties : OrderedPropsRep)
    (valid : MetadataValidRep properties) : (orderedSymbols properties).Nodup := by
  have covered : ∀ key, some key ∈ properties.symbolOrder →
      ∃ stored, properties.entries.get? (.symbol key) = some stored := fun _ member =>
    symbolSlot_covered valid member
  unfold orderedSymbols
  rw [liveOrder_eq_filterMap .symbol properties.entries properties.symbolOrder covered]
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
  exact (symbolLiveOrder_nodup valid).imp fun notEqual => fun equal =>
    notEqual (PropertyKey.symbol.inj equal)

private theorem deleteRep_order (properties : OrderedPropsRep) (key : PropertyKey)
    (valid : MetadataValidRep properties) :
    orderedStrings (deleteRep properties key) = (orderedStrings properties).erase key ∧
    orderedSymbols (deleteRep properties key) = (orderedSymbols properties).erase key := by
  unfold deleteRep
  cases found : properties.entries.get? key with
  | none =>
      have stringAbsent : key ∉ orderedStrings properties := by
        intro member
        cases key with
        | string stringKey =>
            have present := (mem_orderedStrings_iff properties valid stringKey).mp member |>.1
            rw [found] at present
            contradiction
        | symbol symbolKey => simp [orderedStrings] at member
      have symbolAbsent : key ∉ orderedSymbols properties := by
        intro member
        cases key with
        | string stringKey => simp [orderedSymbols] at member
        | symbol symbolKey =>
            have present := (mem_orderedSymbols_iff properties valid symbolKey).mp member
            rw [found] at present
            contradiction
      exact ⟨(List.erase_eq_self_iff.mpr stringAbsent).symm,
        (List.erase_eq_self_iff.mpr symbolAbsent).symm⟩
  | some stored =>
      have entryValid := valid.1 key stored found
      cases key with
      | string stringKey =>
          cases parsed : PropertyKey.arrayIndex? stringKey with
          | some index =>
              have noPosition : stored.orderPosition = none := by
                simpa [EntryValid, parsed] using entryValid
              simp only [noPosition]
              let next : OrderedPropsRep :=
                { properties with entries := properties.entries.erase (.string stringKey) }
              have nextValid := eraseIndexMetadata_valid properties valid stringKey index parsed
              have stringsEqual : orderedStrings next = orderedStrings properties := by
                unfold orderedStrings
                rw [liveOrder_eq_filterMap .string _ _ (fun orderKey member =>
                  stringSlot_covered nextValid member), liveOrder_eq_filterMap .string _ _ (fun orderKey member =>
                  stringSlot_covered valid member)]
              have symbolsEqual : orderedSymbols next = orderedSymbols properties := by
                unfold orderedSymbols
                rw [liveOrder_eq_filterMap .symbol _ _ (fun orderKey member =>
                  symbolSlot_covered nextValid member), liveOrder_eq_filterMap .symbol _ _ (fun orderKey member =>
                  symbolSlot_covered valid member)]
              have stringAbsent : PropertyKey.string stringKey ∉ orderedStrings properties := by
                intro member
                have nonIndex := (mem_orderedStrings_iff properties valid stringKey).mp member |>.2
                rw [parsed] at nonIndex
                contradiction
              have symbolAbsent : PropertyKey.string stringKey ∉ orderedSymbols properties := by
                intro member
                simp [orderedSymbols] at member
              change orderedStrings next = _ ∧ orderedSymbols next = _
              constructor
              · rw [stringsEqual, List.erase_eq_self_iff.mpr stringAbsent]
              · rw [symbolsEqual, List.erase_eq_self_iff.mpr symbolAbsent]
              all_goals rfl
          | none =>
              simp [EntryValid, parsed] at entryValid
              rcases entryValid with ⟨position, storedPosition, slotAt⟩
              simp only [storedPosition, parsed, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
              let next : OrderedPropsRep :=
                ⟨properties.entries.erase (.string stringKey), tombstone properties.stringOrder position,
                  properties.symbolOrder, properties.stringTombstones + 1, properties.symbolTombstones⟩
              have nextValid := deleteStringMetadata_valid properties valid stringKey position slotAt
              have stringsErased : orderedStrings next =
                  (orderedStrings properties).erase (.string stringKey) := by
                rw [(orderedStrings_nodup properties valid).erase_eq_filter]
                unfold orderedStrings
                rw [liveOrder_tombstone_deleted .string properties.entries properties.stringOrder stringKey
                  position slotAt, liveOrder_erase]
                rw [List.filter_map]
                congr 2
              have symbolsEqual : orderedSymbols next = orderedSymbols properties := by
                unfold orderedSymbols
                rw [liveOrder_eq_filterMap .symbol _ _ (fun orderKey member =>
                  symbolSlot_covered nextValid member), liveOrder_eq_filterMap .symbol _ _ (fun orderKey member =>
                  symbolSlot_covered valid member)]
              have symbolAbsent : PropertyKey.string stringKey ∉ orderedSymbols properties := by
                intro member
                simp [orderedSymbols] at member
              unfold deleteString
              by_cases compact : shouldCompact (tombstone properties.stringOrder position).size
                  (properties.stringTombstones + 1) = true
              · simp only [compact, ↓reduceIte]
                rw [compactStrings_orderedStrings next nextValid, stringsErased,
                  compactStrings_orderedSymbols next, symbolsEqual,
                  List.erase_eq_self_iff.mpr symbolAbsent]
                exact ⟨rfl, rfl⟩
              · have notCompact : shouldCompact (tombstone properties.stringOrder position).size
                    (properties.stringTombstones + 1) = false := by
                  cases equation : shouldCompact (tombstone properties.stringOrder position).size
                      (properties.stringTombstones + 1) with
                  | false => rfl
                  | true => exact False.elim (compact equation)
                simp only [notCompact, Bool.false_eq_true, ↓reduceIte]
                rw [stringsErased, symbolsEqual, List.erase_eq_self_iff.mpr symbolAbsent]
                exact ⟨rfl, rfl⟩
      | symbol symbolKey =>
          simp [EntryValid] at entryValid
          rcases entryValid with ⟨position, storedPosition, slotAt⟩
          simp only [storedPosition]
          let next : OrderedPropsRep :=
            ⟨properties.entries.erase (.symbol symbolKey), properties.stringOrder,
              tombstone properties.symbolOrder position, properties.stringTombstones,
              properties.symbolTombstones + 1⟩
          have nextValid := deleteSymbolMetadata_valid properties valid symbolKey position slotAt
          have stringsEqual : orderedStrings next = orderedStrings properties := by
            unfold orderedStrings
            rw [liveOrder_eq_filterMap .string _ _ (fun orderKey member =>
              stringSlot_covered nextValid member), liveOrder_eq_filterMap .string _ _ (fun orderKey member =>
              stringSlot_covered valid member)]
          have symbolsErased : orderedSymbols next =
              (orderedSymbols properties).erase (.symbol symbolKey) := by
            rw [(orderedSymbols_nodup properties valid).erase_eq_filter]
            unfold orderedSymbols
            rw [liveOrder_tombstone_deleted .symbol properties.entries properties.symbolOrder symbolKey
              position slotAt, liveOrder_erase]
            rw [List.filter_map]
            congr 2
          have stringAbsent : PropertyKey.symbol symbolKey ∉ orderedStrings properties := by
            intro member
            simp [orderedStrings] at member
          unfold deleteSymbol
          by_cases compact : shouldCompact (tombstone properties.symbolOrder position).size
              (properties.symbolTombstones + 1) = true
          · simp only [compact, ↓reduceIte]
            rw [compactSymbols_orderedStrings next, stringsEqual,
              compactSymbols_orderedSymbols next nextValid, symbolsErased,
              List.erase_eq_self_iff.mpr stringAbsent]
            exact ⟨rfl, rfl⟩
          · have notCompact : shouldCompact (tombstone properties.symbolOrder position).size
                (properties.symbolTombstones + 1) = false := by
              cases equation : shouldCompact (tombstone properties.symbolOrder position).size
                  (properties.symbolTombstones + 1) with
              | false => rfl
              | true => exact False.elim (compact equation)
            simp only [notCompact, Bool.false_eq_true, ↓reduceIte]
            rw [stringsEqual, symbolsErased, List.erase_eq_self_iff.mpr stringAbsent]
            exact ⟨rfl, rfl⟩

private theorem ownKeys_nodup_of_metadata (properties : OrderedPropsRep)
    (valid : MetadataValidRep properties) :
    (sortedIndices properties ++ orderedStrings properties ++ orderedSymbols properties).Nodup := by
  rw [List.nodup_append]
  refine ⟨?_, orderedSymbols_nodup properties valid, ?_⟩
  · rw [List.nodup_append]
    refine ⟨sortedIndices_nodup properties, orderedStrings_nodup properties valid, ?_⟩
    intro indexKey indexMember stringKey stringMember equal
    have indexClass := (mem_sortedIndices_iff properties indexKey).mp indexMember
    rw [orderedStrings] at stringMember
    rcases List.mem_map.mp stringMember with ⟨key, keyMember, rfl⟩
    subst indexKey
    have nonIndex := (mem_orderedStrings_iff properties valid key).mp (by
      rw [orderedStrings]
      exact List.mem_map.mpr ⟨key, keyMember, rfl⟩) |>.2
    simp [nonIndex] at indexClass
  · intro earlier earlierMember symbolKey symbolMember equal
    rw [orderedSymbols] at symbolMember
    rcases List.mem_map.mp symbolMember with ⟨key, keyMember, rfl⟩
    subst earlier
    rcases List.mem_append.mp earlierMember with indexMember | stringMember
    · have indexClass := (mem_sortedIndices_iff properties (.symbol key)).mp indexMember
      simp at indexClass
    · rw [orderedStrings] at stringMember
      rcases List.mem_map.mp stringMember with ⟨stringKey, _, impossible⟩
      contradiction

private def keyIndex? : PropertyKey → Option Nat
  | .string key => PropertyKey.arrayIndex? key
  | .symbol _ => none

private def isIndexKey : PropertyKey → Bool
  | .string key => (PropertyKey.arrayIndex? key).isSome
  | .symbol _ => false

private def isOrderedStringKey : PropertyKey → Bool
  | .string key => (PropertyKey.arrayIndex? key).isNone
  | .symbol _ => false

private def isSymbolKey : PropertyKey → Bool
  | .string _ => false
  | .symbol _ => true

private theorem ownKeyIndices_pairwise (properties : OrderedPropsRep)
    (valid : MetadataValidRep properties) :
    ((sortedIndices properties ++ orderedStrings properties ++ orderedSymbols properties).filterMap
      keyIndex?).Pairwise (· ≤ ·) := by
  let source := properties.entries.toList.filterMap indexEntry?
  let sorted := source.mergeSort indexEntryLE
  have sortedPairs : sorted.Pairwise (fun left right => indexEntryLE left right = true) := by
    apply List.pairwise_mergeSort
    · intro left middle right leftLe rightLe
      simp [indexEntryLE] at leftLe rightLe ⊢
      omega
    · intro left right
      simp [indexEntryLE]
      omega
  have parsedPair : ∀ pair ∈ sorted, keyIndex? pair.2 = some pair.1 := by
    intro pair member
    have sourceMember : pair ∈ source := List.mem_mergeSort.mp member
    simp only [source, List.mem_filterMap] at sourceMember
    rcases sourceMember with ⟨entry, entryMember, entryValue⟩
    rcases entry with ⟨entryKey, stored⟩
    cases entryKey with
    | string key =>
        cases parsed : PropertyKey.arrayIndex? key with
        | none => simp [indexEntry?, parsed] at entryValue
        | some index =>
            simp [indexEntry?, parsed] at entryValue
            subst pair
            exact parsed
    | symbol key => simp [indexEntry?] at entryValue
  have sortedIndicesEq : (sorted.map (·.2)).filterMap keyIndex? = sorted.map (·.1) := by
    have go : ∀ pairs : List (Nat × PropertyKey),
        (∀ pair ∈ pairs, keyIndex? pair.2 = some pair.1) →
        (pairs.map (·.2)).filterMap keyIndex? = pairs.map (·.1) := by
      intro pairs parsed
      induction pairs with
      | nil => rfl
      | cons pair pairs ih =>
          have head := parsed pair List.mem_cons_self
          have tail : ∀ entry ∈ pairs, keyIndex? entry.2 = some entry.1 := fun entry member =>
            parsed entry (List.mem_cons_of_mem pair member)
          simp only [List.map_cons, List.filterMap_cons]
          rw [head]
          simp only [List.cons.injEq, true_and]
          exact ih tail
    exact go sorted parsedPair
  have stringsEmpty : (orderedStrings properties).filterMap keyIndex? = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro key member
    cases key with
    | string stringKey =>
        have nonIndex := (mem_orderedStrings_iff properties valid stringKey).mp member |>.2
        simp [keyIndex?, nonIndex]
    | symbol symbolKey => simp [orderedStrings] at member
  have symbolsEmpty : (orderedSymbols properties).filterMap keyIndex? = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro key member
    cases key with
    | string stringKey => simp [orderedSymbols] at member
    | symbol symbolKey => rfl
  rw [List.filterMap_append, List.filterMap_append, stringsEmpty, symbolsEmpty,
    List.append_nil, List.append_nil]
  change (sorted.map (·.2)).filterMap keyIndex? |>.Pairwise (· ≤ ·)
  rw [sortedIndicesEq, List.pairwise_map]
  exact sortedPairs.imp fun pairLe => by simpa [indexEntryLE] using pairLe

private theorem arrayIndices_eq_sortedIndices (properties : OrderedPropsRep)
    (valid : MetadataValidRep properties) :
    arrayIndices (.mk properties) = (sortedIndices properties).filterMap keyIndex? := by
  have stringsEmpty : (orderedStrings properties).filterMap keyIndex? = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro key member
    cases key with
    | string stringKey =>
        have nonIndex := (mem_orderedStrings_iff properties valid stringKey).mp member |>.2
        simp [keyIndex?, nonIndex]
    | symbol symbolKey => simp [orderedStrings] at member
  have symbolsEmpty : (orderedSymbols properties).filterMap keyIndex? = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro key member
    cases key with
    | string stringKey => simp [orderedSymbols] at member
    | symbol symbolKey => rfl
  change (sortedIndices properties ++ orderedStrings properties ++ orderedSymbols properties).filterMap
    keyIndex? = _
  rw [List.filterMap_append, List.filterMap_append, stringsEmpty, symbolsEmpty]
  simp

private theorem sortedIndices_eq_arrayIndices (properties : OrderedPropsRep) :
    sortedIndices properties = ((sortedIndices properties).filterMap keyIndex?).map
      (fun index => PropertyKey.string (PropertyKey.arrayIndexString index)) := by
  have canonical : ∀ key ∈ sortedIndices properties,
      ∃ index, keyIndex? key = some index ∧
        key = .string (PropertyKey.arrayIndexString index) := by
    intro key member
    have classification := (mem_sortedIndices_iff properties key).mp member |>.2
    cases key with
    | string stringKey =>
        cases parsed : PropertyKey.arrayIndex? stringKey with
        | none => simp [parsed] at classification
        | some index =>
            exact ⟨index, by simp [keyIndex?, parsed], by
              rw [PropertyKey.arrayIndex?_sound parsed]⟩
    | symbol symbolKey => simp at classification
  have go : ∀ keys : List PropertyKey,
      (∀ key ∈ keys, ∃ index, keyIndex? key = some index ∧
        key = .string (PropertyKey.arrayIndexString index)) →
      keys = (keys.filterMap keyIndex?).map
        (fun index => PropertyKey.string (PropertyKey.arrayIndexString index)) := by
    intro keys valid
    induction keys with
    | nil => rfl
    | cons key keys ih =>
        rcases valid key List.mem_cons_self with ⟨index, parsed, canonicalKey⟩
        have tail : ∀ tailKey ∈ keys, ∃ index, keyIndex? tailKey = some index ∧
            tailKey = .string (PropertyKey.arrayIndexString index) := fun tailKey member =>
          valid tailKey (List.mem_cons_of_mem key member)
        simp only [List.filterMap_cons, parsed, List.map_cons]
        rw [canonicalKey]
        congr
        exact ih tail
  exact go _ canonical

private theorem stringKeys_eq_orderedStrings (properties : OrderedPropsRep)
    (valid : MetadataValidRep properties) : stringKeys (.mk properties) = orderedStrings properties := by
  have indexEmpty : (sortedIndices properties).filter isOrderedStringKey = [] := by
    rw [List.filter_eq_nil_iff]
    intro key member
    have classification := (mem_sortedIndices_iff properties key).mp member |>.2
    cases key with
    | string stringKey =>
        cases parsed : PropertyKey.arrayIndex? stringKey <;>
          simp [isOrderedStringKey, parsed] at classification ⊢
    | symbol symbolKey => simp at classification
  have strings : (orderedStrings properties).filter isOrderedStringKey = orderedStrings properties := by
    rw [List.filter_eq_self]
    intro key member
    cases key with
    | string stringKey =>
        have nonIndex := (mem_orderedStrings_iff properties valid stringKey).mp member |>.2
        simp [isOrderedStringKey, nonIndex]
    | symbol symbolKey => simp [orderedStrings] at member
  have symbolsEmpty : (orderedSymbols properties).filter isOrderedStringKey = [] := by
    rw [List.filter_eq_nil_iff]
    intro key member
    cases key with
    | string stringKey => simp [orderedSymbols] at member
    | symbol symbolKey => simp [isOrderedStringKey]
  change (sortedIndices properties ++ orderedStrings properties ++ orderedSymbols properties).filter
    isOrderedStringKey = _
  rw [List.filter_append, List.filter_append, indexEmpty, strings, symbolsEmpty]
  simp

private theorem symbolKeys_eq_orderedSymbols (properties : OrderedPropsRep) :
    symbolKeys (.mk properties) = orderedSymbols properties := by
  have indexEmpty : (sortedIndices properties).filter isSymbolKey = [] := by
    rw [List.filter_eq_nil_iff]
    intro key member
    have classification := (mem_sortedIndices_iff properties key).mp member |>.2
    cases key <;> simp [isSymbolKey] at classification ⊢
  have stringsEmpty : (orderedStrings properties).filter isSymbolKey = [] := by
    rw [List.filter_eq_nil_iff]
    intro key member
    cases key with
    | string stringKey => simp [isSymbolKey]
    | symbol symbolKey => simp [orderedStrings] at member
  have symbols : (orderedSymbols properties).filter isSymbolKey = orderedSymbols properties := by
    rw [List.filter_eq_self]
    intro key member
    cases key with
    | string stringKey => simp [orderedSymbols] at member
    | symbol symbolKey => simp [isSymbolKey]
  change (sortedIndices properties ++ orderedStrings properties ++ orderedSymbols properties).filter
    isSymbolKey = _
  rw [List.filter_append, List.filter_append, indexEmpty, stringsEmpty, symbols]
  simp

private theorem pairwise_le_eq_of_perm {left right : List Nat}
    (leftSorted : left.Pairwise (· ≤ ·)) (rightSorted : right.Pairwise (· ≤ ·))
    (permutation : left.Perm right) : left = right := by
  induction left generalizing right with
  | nil => exact (List.eq_nil_of_length_eq_zero permutation.length_eq.symm).symm
  | cons first rest ih =>
      cases right with
      | nil => simp at permutation
      | cons second tail =>
          have leftParts := List.pairwise_cons.mp leftSorted
          have rightParts := List.pairwise_cons.mp rightSorted
          have secondMember : second ∈ first :: rest := permutation.mem_iff.mpr (by simp)
          have firstLeSecond : first ≤ second := by
            rcases List.mem_cons.mp secondMember with equal | member
            · omega
            · exact leftParts.1 second member
          have firstMember : first ∈ second :: tail := permutation.mem_iff.mp (by simp)
          have secondLeFirst : second ≤ first := by
            rcases List.mem_cons.mp firstMember with equal | member
            · omega
            · exact rightParts.1 first member
          have equal : first = second := Nat.le_antisymm firstLeSecond secondLeFirst
          subst second
          exact congrArg (first :: ·) (ih leftParts.2 rightParts.2 (List.Perm.cons_inv permutation))

/-- Exact bidirectional agreement between map entries and occupied order slots. -/
def metadataConsistent (properties : OrderedProps) : Bool :=
  metadataConsistentRep properties.rep

/-- Propositional form of exact bidirectional order metadata agreement. -/
def MetadataValid (properties : OrderedProps) : Prop := MetadataValidRep properties.rep

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

/-- Proof-oriented form of the complete ordered-property representation invariant. -/
def Valid (properties : OrderedProps) : Prop := ValidRep properties.rep

/-- The executable metadata check is sound and complete. -/
theorem metadataConsistent_iff_valid (properties : OrderedProps) :
    properties.metadataConsistent = true ↔ properties.MetadataValid :=
  metadataConsistentRep_iff properties.rep

/-- The executable complete invariant check is sound and complete. -/
theorem isWellFormed_iff_valid (properties : OrderedProps) :
    properties.isWellFormed = true ↔ properties.Valid := by
  simp [isWellFormed, invariantChecks, Valid, ValidRep, metadataConsistentRep_iff,
    compactionThreshold]

/-- The public well-formedness proposition is the proof-oriented representation invariant. -/
theorem wellFormed_iff_valid (properties : OrderedProps) :
    WellFormed properties ↔ properties.Valid := isWellFormed_iff_valid properties

/-- Insertion preserves the complete ordered-property invariant, including compaction branches. -/
theorem insert_wellFormed (properties : OrderedProps) (key : PropertyKey)
    (descriptor : PropertyDescriptor) (valid : WellFormed properties) :
    WellFormed (properties.insert key descriptor) := by
  rw [wellFormed_iff_valid] at valid ⊢
  exact insertRep_valid properties.rep key descriptor valid

/-- Deletion preserves the complete ordered-property invariant, including compaction branches. -/
theorem delete_wellFormed (properties : OrderedProps) (key : PropertyKey)
    (valid : WellFormed properties) : WellFormed (properties.delete key) := by
  rw [wellFormed_iff_valid] at valid ⊢
  exact deleteRep_valid properties.rep key valid

/-- Inserting a descriptor that satisfies a predicate preserves that predicate for all descriptors. -/
theorem descriptors_all_insert (properties : OrderedProps) (key : PropertyKey)
    (descriptor : PropertyDescriptor) (predicate : PropertyDescriptor → Bool)
    (current : properties.descriptors.all predicate = true) (inserted : predicate descriptor = true) :
    (properties.insert key descriptor).descriptors.all predicate = true := by
  rw [List.all_eq_true] at current ⊢
  intro observed member
  rw [descriptors, List.mem_map] at member
  obtain ⟨entry, entryMember, rfl⟩ := member
  have found := Std.HashMap.mem_toList_iff_getElem?_eq_some.mp entryMember
  have descriptorFound := congrArg (Option.map (·.descriptor)) found
  change Option.map _ ((insertRep properties.rep key descriptor).entries.get? entry.1) = _
    at descriptorFound
  rw [insertRep_lookup] at descriptorFound
  simp only [Option.map_some] at descriptorFound
  split at descriptorFound
  · cases descriptorFound
    exact inserted
  · cases oldFound : properties.rep.entries[entry.1]? with
    | none => simp [oldFound] at descriptorFound
    | some oldEntry =>
        have oldMember := Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr oldFound
        have oldValid := current oldEntry.descriptor (by
          rw [descriptors, List.mem_map]
          exact ⟨(entry.1, oldEntry), oldMember, rfl⟩)
        simp [oldFound] at descriptorFound
        rw [← descriptorFound]
        exact oldValid

/-- Deleting a property preserves every predicate satisfied by all remaining descriptors. -/
theorem descriptors_all_delete (properties : OrderedProps) (key : PropertyKey)
    (predicate : PropertyDescriptor → Bool) (valid : WellFormed properties)
    (current : properties.descriptors.all predicate = true) :
    (properties.delete key).descriptors.all predicate = true := by
  rw [List.all_eq_true] at current ⊢
  intro observed member
  rw [descriptors, List.mem_map] at member
  obtain ⟨entry, entryMember, rfl⟩ := member
  have found := Std.HashMap.mem_toList_iff_getElem?_eq_some.mp entryMember
  have descriptorFound := congrArg (Option.map (·.descriptor)) found
  change Option.map _ ((deleteRep properties.rep key).entries.get? entry.1) = _
    at descriptorFound
  rw [deleteRep_lookup properties.rep key entry.1
    ((wellFormed_iff_valid properties).mp valid)] at descriptorFound
  simp only [Option.map_some] at descriptorFound
  split at descriptorFound
  · simp at descriptorFound
  · cases oldFound : properties.rep.entries[entry.1]? with
    | none => simp [oldFound] at descriptorFound
    | some oldEntry =>
        have oldMember := Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr oldFound
        have oldValid := current oldEntry.descriptor (by
          rw [descriptors, List.mem_map]
          exact ⟨(entry.1, oldEntry), oldMember, rfl⟩)
        simp [oldFound] at descriptorFound
        rw [← descriptorFound]
        exact oldValid

/-- Inserting a key satisfying a predicate preserves that predicate for all stored keys. -/
theorem keysAll_insert (properties : OrderedProps) (key : PropertyKey)
    (descriptor : PropertyDescriptor) (predicate : PropertyKey → Bool)
    (current : properties.keysAll predicate = true) (inserted : predicate key = true) :
    (properties.insert key descriptor).keysAll predicate = true := by
  unfold keysAll at current ⊢
  rw [List.all_eq_true] at current ⊢
  intro entry member
  have found := Std.HashMap.mem_toList_iff_getElem?_eq_some.mp member
  have descriptorFound := congrArg (Option.map (·.descriptor)) found
  change Option.map _ ((insertRep properties.rep key descriptor).entries.get? entry.1) = _
    at descriptorFound
  rw [insertRep_lookup] at descriptorFound
  split at descriptorFound
  · simp_all
  · cases oldFound : properties.rep.entries[entry.1]? with
    | none => simp [oldFound] at descriptorFound
    | some oldEntry =>
        exact current (entry.1, oldEntry)
          (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr oldFound)

/-- Deleting a property preserves every predicate satisfied by all remaining keys. -/
theorem keysAll_delete (properties : OrderedProps) (key : PropertyKey)
    (predicate : PropertyKey → Bool) (valid : WellFormed properties)
    (current : properties.keysAll predicate = true) :
    (properties.delete key).keysAll predicate = true := by
  unfold keysAll at current ⊢
  rw [List.all_eq_true] at current ⊢
  intro entry member
  have found := Std.HashMap.mem_toList_iff_getElem?_eq_some.mp member
  have descriptorFound := congrArg (Option.map (·.descriptor)) found
  change Option.map _ ((deleteRep properties.rep key).entries.get? entry.1) = _
    at descriptorFound
  rw [deleteRep_lookup properties.rep key entry.1
    ((wellFormed_iff_valid properties).mp valid)] at descriptorFound
  split at descriptorFound
  · simp at descriptorFound
  · cases oldFound : properties.rep.entries[entry.1]? with
    | none => simp [oldFound] at descriptorFound
    | some oldEntry =>
        exact current (entry.1, oldEntry)
          (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr oldFound)

/-- A key predicate holds globally when it holds for every successful descriptor lookup. -/
theorem keysAll_of_lookup (properties : OrderedProps) (predicate : PropertyKey → Bool)
    (holds : ∀ key descriptor, properties.lookup key = some descriptor → predicate key = true) :
    properties.keysAll predicate = true := by
  unfold keysAll
  rw [List.all_eq_true]
  intro entry member
  have found := Std.HashMap.mem_toList_iff_getElem?_eq_some.mp member
  apply holds entry.1 entry.2.descriptor
  exact congrArg (Option.map (·.descriptor)) found

/-- A successful lookup inherits every predicate satisfied by all stored keys. -/
theorem key_of_lookup_satisfies (properties : OrderedProps) (predicate : PropertyKey → Bool)
    (current : properties.keysAll predicate = true) (key : PropertyKey)
    (descriptor : PropertyDescriptor) (found : properties.lookup key = some descriptor) :
    predicate key = true := by
  unfold keysAll at current
  rw [List.all_eq_true] at current
  have rawSome : ∃ stored, properties.rep.entries.get? key = some stored ∧
      stored.descriptor = descriptor := by
    simpa [lookup] using found
  rcases rawSome with ⟨stored, storedFound, _⟩
  exact current (key, stored) (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr storedFound)

/-- Insertion installs the supplied descriptor at the inserted key. -/
theorem lookup_insert_same (properties : OrderedProps) (key : PropertyKey)
    (descriptor : PropertyDescriptor) :
    (properties.insert key descriptor).lookup key = some descriptor := by
  unfold lookup insert
  change Option.map _ ((insertRep properties.rep key descriptor).entries.get? key) = _
  rw [insertRep_lookup]
  simp

/-- Insertion leaves every different descriptor lookup unchanged. -/
theorem lookup_insert_ne (properties : OrderedProps) (key query : PropertyKey)
    (descriptor : PropertyDescriptor) (different : key ≠ query) :
    (properties.insert key descriptor).lookup query = properties.lookup query := by
  unfold lookup insert
  change Option.map _ ((insertRep properties.rep key descriptor).entries.get? query) = _
  rw [insertRep_lookup]
  simp [different]

/-- Deletion makes the deleted key absent. -/
theorem lookup_delete_same (properties : OrderedProps) (key : PropertyKey)
    (valid : WellFormed properties) : (properties.delete key).lookup key = none := by
  unfold lookup delete
  change Option.map _ ((deleteRep properties.rep key).entries.get? key) = _
  rw [deleteRep_lookup properties.rep key key ((wellFormed_iff_valid properties).mp valid)]
  simp

/-- Deletion leaves every different descriptor lookup unchanged. -/
theorem lookup_delete_ne (properties : OrderedProps) (key query : PropertyKey)
    (different : key ≠ query) (valid : WellFormed properties) :
    (properties.delete key).lookup query = properties.lookup query := by
  unfold lookup delete
  change Option.map _ ((deleteRep properties.rep key).entries.get? query) = _
  rw [deleteRep_lookup properties.rep key query ((wellFormed_iff_valid properties).mp valid)]
  simp [different]

/-- A live key occurs in `ownKeys` exactly when descriptor lookup succeeds. -/
theorem mem_ownKeys_iff_lookup_isSome (properties : OrderedProps) (key : PropertyKey)
    (valid : WellFormed properties) :
    key ∈ properties.ownKeys ↔ (properties.lookup key).isSome := by
  have metadata := (wellFormed_iff_valid properties).mp valid |>.1
  cases key with
  | string key =>
      have noSymbol : PropertyKey.string key ∉ orderedSymbols properties.rep := by
        intro member
        rw [orderedSymbols] at member
        rcases List.mem_map.mp member with ⟨symbolKey, _, impossible⟩
        contradiction
      rw [ownKeys, List.mem_append, List.mem_append,
        mem_sortedIndices_iff, mem_orderedStrings_iff properties.rep metadata]
      simp only [noSymbol, or_false, lookup]
      cases found : properties.rep.entries.get? (.string key) <;>
        cases parsed : PropertyKey.arrayIndex? key <;> simp
  | symbol key =>
      have noString : PropertyKey.symbol key ∉ orderedStrings properties.rep := by
        intro member
        rw [orderedStrings] at member
        rcases List.mem_map.mp member with ⟨stringKey, _, impossible⟩
        contradiction
      rw [ownKeys, List.mem_append, List.mem_append,
        mem_sortedIndices_iff, mem_orderedSymbols_iff properties.rep metadata]
      simp [noString, lookup]

/-- Well-formed `ownKeys` output contains no duplicate key. -/
theorem ownKeys_nodup (properties : OrderedProps) (valid : WellFormed properties) :
    properties.ownKeys.Nodup := by
  have metadata := (wellFormed_iff_valid properties).mp valid |>.1
  exact ownKeys_nodup_of_metadata properties.rep metadata

/-- The numeric array-index projection contains no duplicate index. -/
theorem arrayIndices_nodup (properties : OrderedProps) (valid : WellFormed properties) :
    properties.arrayIndices.Nodup := by
  rw [arrayIndices, List.nodup_iff_pairwise_ne, List.pairwise_filterMap]
  have preserves : ∀ (left right : PropertyKey), left ≠ right →
      ∀ leftIndex, keyIndex? left = some leftIndex →
      ∀ rightIndex, keyIndex? right = some rightIndex → leftIndex ≠ rightIndex := by
    intro left right keysNe leftIndex leftParsed rightIndex rightParsed indicesEqual
    cases left with
    | string leftString =>
        cases right with
        | string rightString =>
            simp [keyIndex?] at leftParsed rightParsed
            subst rightIndex
            exact keysNe (congrArg PropertyKey.string
              (PropertyKey.arrayIndex?_injective leftParsed rightParsed))
        | symbol rightSymbol => simp [keyIndex?] at rightParsed
    | symbol leftSymbol => simp [keyIndex?] at leftParsed
  exact (ownKeys_nodup properties valid).imp (preserves _ _)

/-- Well-formed `ownKeys` is a permutation of the HashMap's complete key set. -/
private theorem ownKeys_perm_keys (properties : OrderedProps) (valid : WellFormed properties) :
    properties.ownKeys.Perm properties.rep.entries.keys := by
  rw [List.perm_iff_count]
  intro key
  rw [(ownKeys_nodup properties valid).count,
    (Std.HashMap.nodup_keys (m := properties.rep.entries)).count]
  have membership := mem_ownKeys_iff_lookup_isSome properties key valid
  have mapMembership : key ∈ properties.rep.entries.keys ↔ (properties.lookup key).isSome := by
    calc
      key ∈ properties.rep.entries.keys ↔ key ∈ properties.rep.entries := Std.HashMap.mem_keys
      _ ↔ properties.rep.entries[key]?.isSome := Std.HashMap.mem_iff_isSome_getElem?
      _ ↔ (properties.lookup key).isSome := by
        change (properties.rep.entries.get? key).isSome ↔
          ((properties.rep.entries.get? key).map (·.descriptor)).isSome
        cases properties.rep.entries.get? key <;> rfl
  simp only [membership, mapMembership]

/-- The number of emitted own keys is exactly the live HashMap size. -/
theorem ownKeys_length (properties : OrderedProps) (valid : WellFormed properties) :
    properties.ownKeys.length = properties.size := by
  rw [(ownKeys_perm_keys properties valid).length_eq, Std.HashMap.length_keys]
  rfl

/-- Array-index keys extracted from `ownKeys` are in nondecreasing numeric order. -/
theorem ownKeys_indices_ascending (properties : OrderedProps) (valid : WellFormed properties) :
    (properties.ownKeys.filterMap fun key => match key with
      | .string stringKey => PropertyKey.arrayIndex? stringKey
      | .symbol _ => none).Pairwise (· ≤ ·) := by
  have metadata := (wellFormed_iff_valid properties).mp valid |>.1
  exact ownKeyIndices_pairwise properties.rep metadata

private theorem arrayIndices_ext (left right : OrderedProps)
    (leftValid : WellFormed left) (rightValid : WellFormed right)
    (support : ∀ stringKey index, PropertyKey.arrayIndex? stringKey = some index →
      (left.lookup (.string stringKey)).isSome = (right.lookup (.string stringKey)).isSome) :
    left.arrayIndices = right.arrayIndices := by
  apply pairwise_le_eq_of_perm (ownKeys_indices_ascending left leftValid)
    (ownKeys_indices_ascending right rightValid)
  rw [List.perm_iff_count]
  intro index
  change List.count index left.arrayIndices = List.count index right.arrayIndices
  rw [(arrayIndices_nodup left leftValid).count, (arrayIndices_nodup right rightValid).count]
  have membership : index ∈ left.arrayIndices ↔ index ∈ right.arrayIndices := by
    constructor
    · intro member
      rcases List.mem_filterMap.mp member with ⟨key, keyMember, parsed⟩
      cases key with
      | symbol symbolKey => simp at parsed
      | string stringKey =>
        apply List.mem_filterMap.mpr
        refine ⟨.string stringKey, ?_, parsed⟩
        apply (mem_ownKeys_iff_lookup_isSome right (.string stringKey) rightValid).mpr
        rw [← support stringKey index parsed]
        exact (mem_ownKeys_iff_lookup_isSome left (.string stringKey) leftValid).mp keyMember
    · intro member
      rcases List.mem_filterMap.mp member with ⟨key, keyMember, parsed⟩
      cases key with
      | symbol symbolKey => simp at parsed
      | string stringKey =>
        apply List.mem_filterMap.mpr
        refine ⟨.string stringKey, ?_, parsed⟩
        apply (mem_ownKeys_iff_lookup_isSome left (.string stringKey) leftValid).mpr
        rw [support stringKey index parsed]
        exact (mem_ownKeys_iff_lookup_isSome right (.string stringKey) rightValid).mp keyMember
  simp [membership]

/-- `ownKeys` is partitioned into indices, ordinary strings, then symbols. -/
theorem ownKeys_partition (properties : OrderedProps) (valid : WellFormed properties) :
    properties.ownKeys =
      properties.ownKeys.filter (fun key => match key with
        | .string stringKey => (PropertyKey.arrayIndex? stringKey).isSome
        | .symbol _ => false) ++
      properties.ownKeys.filter (fun key => match key with
        | .string stringKey => (PropertyKey.arrayIndex? stringKey).isNone
        | .symbol _ => false) ++
      properties.ownKeys.filter (fun key => match key with
        | .string _ => false
        | .symbol _ => true) := by
  have metadata := (wellFormed_iff_valid properties).mp valid |>.1
  have indexIndex : (sortedIndices properties.rep).filter isIndexKey = sortedIndices properties.rep := by
    rw [List.filter_eq_self]
    intro key member
    have classification := (mem_sortedIndices_iff properties.rep key).mp member |>.2
    cases key with
    | string stringKey => exact classification
    | symbol symbolKey => simp at classification
  have indexString : (orderedStrings properties.rep).filter isIndexKey = [] := by
    rw [List.filter_eq_nil_iff]
    intro key member
    cases key with
    | string stringKey =>
        have nonIndex := (mem_orderedStrings_iff properties.rep metadata stringKey).mp member |>.2
        simp [isIndexKey, nonIndex]
    | symbol symbolKey => simp [orderedStrings] at member
  have indexSymbol : (orderedSymbols properties.rep).filter isIndexKey = [] := by
    rw [List.filter_eq_nil_iff]
    intro key member
    cases key with
    | string stringKey => simp [orderedSymbols] at member
    | symbol symbolKey => simp [isIndexKey]
  have stringIndex : (sortedIndices properties.rep).filter isOrderedStringKey = [] := by
    rw [List.filter_eq_nil_iff]
    intro key member
    have classification := (mem_sortedIndices_iff properties.rep key).mp member |>.2
    cases key with
    | string stringKey =>
        cases parsed : PropertyKey.arrayIndex? stringKey <;>
          simp [isOrderedStringKey, parsed] at classification ⊢
    | symbol symbolKey => simp at classification
  have stringString : (orderedStrings properties.rep).filter isOrderedStringKey =
      orderedStrings properties.rep := by
    rw [List.filter_eq_self]
    intro key member
    cases key with
    | string stringKey =>
        have nonIndex := (mem_orderedStrings_iff properties.rep metadata stringKey).mp member |>.2
        simp [isOrderedStringKey, nonIndex]
    | symbol symbolKey => simp [orderedStrings] at member
  have stringSymbol : (orderedSymbols properties.rep).filter isOrderedStringKey = [] := by
    rw [List.filter_eq_nil_iff]
    intro key member
    cases key with
    | string stringKey => simp [orderedSymbols] at member
    | symbol symbolKey => simp [isOrderedStringKey]
  have symbolIndex : (sortedIndices properties.rep).filter isSymbolKey = [] := by
    rw [List.filter_eq_nil_iff]
    intro key member
    have classification := (mem_sortedIndices_iff properties.rep key).mp member |>.2
    cases key <;> simp [isSymbolKey] at classification ⊢
  have symbolString : (orderedStrings properties.rep).filter isSymbolKey = [] := by
    rw [List.filter_eq_nil_iff]
    intro key member
    cases key with
    | string stringKey => simp [isSymbolKey]
    | symbol symbolKey => simp [orderedStrings] at member
  have symbolSymbol : (orderedSymbols properties.rep).filter isSymbolKey =
      orderedSymbols properties.rep := by
    rw [List.filter_eq_self]
    intro key member
    cases key with
    | string stringKey => simp [orderedSymbols] at member
    | symbol symbolKey => simp [isSymbolKey]
  change sortedIndices properties.rep ++ orderedStrings properties.rep ++ orderedSymbols properties.rep = _
  change _ =
    (sortedIndices properties.rep ++ orderedStrings properties.rep ++ orderedSymbols properties.rep).filter
        isIndexKey ++
    (sortedIndices properties.rep ++ orderedStrings properties.rep ++ orderedSymbols properties.rep).filter
        isOrderedStringKey ++
    (sortedIndices properties.rep ++ orderedStrings properties.rep ++ orderedSymbols properties.rep).filter
        isSymbolKey
  simp [List.filter_append, indexIndex, indexString, indexSymbol, stringIndex, stringString,
    stringSymbol, symbolIndex, symbolString, symbolSymbol]

/-- The three public projections reconstruct the complete observable own-key sequence. -/
theorem ownKeys_eq_projections (properties : OrderedProps) (valid : WellFormed properties) :
    properties.ownKeys =
      properties.arrayIndices.map (fun index =>
        PropertyKey.string (PropertyKey.arrayIndexString index)) ++
      properties.stringKeys ++ properties.symbolKeys := by
  rcases properties with ⟨rep⟩
  have metadata := (wellFormed_iff_valid (.mk rep)).mp valid |>.1
  rw [arrayIndices_eq_sortedIndices rep metadata,
    stringKeys_eq_orderedStrings rep metadata, symbolKeys_eq_orderedSymbols rep,
    ← sortedIndices_eq_arrayIndices rep]
  rfl

private theorem exists_stored_of_lookup_isSome {properties : OrderedProps} {key : PropertyKey}
    (present : (properties.lookup key).isSome) :
    ∃ stored, properties.rep.entries.get? key = some stored := by
  unfold lookup at present
  cases found : properties.rep.entries.get? key with
  | none =>
      rw [found] at present
      contradiction
  | some stored => exact ⟨stored, rfl⟩

private theorem get?_none_of_lookup_none {properties : OrderedProps} {key : PropertyKey}
    (absent : properties.lookup key = none) : properties.rep.entries.get? key = none := by
  unfold lookup at absent
  change (properties.rep.entries.get? key).map (·.descriptor) = none at absent
  cases found : properties.rep.entries.get? key with
  | none => rfl
  | some stored =>
      rw [found] at absent
      contradiction

/-- Updating a live key leaves the numeric index projection unchanged. -/
theorem arrayIndices_insert_existing (properties : OrderedProps) (key : PropertyKey)
    (descriptor : PropertyDescriptor) (valid : WellFormed properties)
    (present : (properties.lookup key).isSome) :
    (properties.insert key descriptor).arrayIndices = properties.arrayIndices := by
  have nextValid := insert_wellFormed properties key descriptor valid
  have support : ∀ query, ((properties.insert key descriptor).lookup query).isSome =
      (properties.lookup query).isSome := by
    intro query
    by_cases equal : key = query
    · subst query
      rw [lookup_insert_same]
      exact present.symm
    · rw [lookup_insert_ne properties key query descriptor equal]
  exact arrayIndices_ext (properties.insert key descriptor) properties nextValid valid
    (fun stringKey index parsed => support (.string stringKey))

/-- Updating a live key leaves ordinary-string insertion order unchanged. -/
theorem stringKeys_insert_existing (properties : OrderedProps) (key : PropertyKey)
    (descriptor : PropertyDescriptor) (valid : WellFormed properties)
    (present : (properties.lookup key).isSome) :
    (properties.insert key descriptor).stringKeys = properties.stringKeys := by
  rcases properties with ⟨rep⟩
  obtain ⟨stored, found⟩ := exists_stored_of_lookup_isSome present
  change rep.entries.get? key = some stored at found
  let nextRep : OrderedPropsRep :=
    { rep with entries := rep.entries.insert key { stored with descriptor } }
  have repEq : insertRep rep key descriptor = nextRep := by
    unfold insertRep
    rw [found]
  have oldMetadata := (wellFormed_iff_valid (.mk rep)).mp valid |>.1
  have newMetadata : MetadataValidRep nextRep := by
    rw [← repEq]
    exact (insertRep_valid rep key descriptor ((wellFormed_iff_valid (.mk rep)).mp valid)).1
  change stringKeys (.mk (insertRep rep key descriptor)) = stringKeys (.mk rep)
  rw [repEq, stringKeys_eq_orderedStrings nextRep newMetadata,
    stringKeys_eq_orderedStrings rep oldMetadata]
  unfold orderedStrings
  exact congrArg (List.map PropertyKey.string)
    (liveOrder_insert_existing .string rep.entries rep.stringOrder key stored
      { stored with descriptor } found)

/-- Updating a live key leaves symbol insertion order unchanged. -/
theorem symbolKeys_insert_existing (properties : OrderedProps) (key : PropertyKey)
    (descriptor : PropertyDescriptor) (valid : WellFormed properties)
    (present : (properties.lookup key).isSome) :
    (properties.insert key descriptor).symbolKeys = properties.symbolKeys := by
  rcases properties with ⟨rep⟩
  obtain ⟨stored, found⟩ := exists_stored_of_lookup_isSome present
  change rep.entries.get? key = some stored at found
  let nextRep : OrderedPropsRep :=
    { rep with entries := rep.entries.insert key { stored with descriptor } }
  have repEq : insertRep rep key descriptor = nextRep := by
    unfold insertRep
    rw [found]
  change symbolKeys (.mk (insertRep rep key descriptor)) = symbolKeys (.mk rep)
  rw [repEq, symbolKeys_eq_orderedSymbols nextRep, symbolKeys_eq_orderedSymbols rep]
  unfold orderedSymbols
  exact congrArg (List.map PropertyKey.symbol)
    (liveOrder_insert_existing .symbol rep.entries rep.symbolOrder key stored
      { stored with descriptor } found)

/-- Updating a live key changes only its descriptor, never the observable key sequence. -/
theorem ownKeys_insert_existing (properties : OrderedProps) (key : PropertyKey)
    (descriptor : PropertyDescriptor) (valid : WellFormed properties)
    (present : (properties.lookup key).isSome) :
    (properties.insert key descriptor).ownKeys = properties.ownKeys := by
  have nextValid := insert_wellFormed properties key descriptor valid
  rw [ownKeys_eq_projections _ nextValid, ownKeys_eq_projections _ valid,
    arrayIndices_insert_existing properties key descriptor valid present,
    stringKeys_insert_existing properties key descriptor valid present,
    symbolKeys_insert_existing properties key descriptor valid present]

/-- A fresh ordinary string leaves numeric indices unchanged. -/
theorem arrayIndices_insert_nonIndex_string (properties : OrderedProps) (key : JSString)
    (descriptor : PropertyDescriptor) (valid : WellFormed properties)
    (nonIndex : PropertyKey.arrayIndex? key = none) :
    (properties.insert (.string key) descriptor).arrayIndices = properties.arrayIndices := by
  apply arrayIndices_ext _ _ (insert_wellFormed properties (.string key) descriptor valid) valid
  intro indexKey index parsed
  have different : PropertyKey.string key ≠ .string indexKey := by
    intro equal
    cases equal
    rw [nonIndex] at parsed
    contradiction
  rw [lookup_insert_ne properties (.string key) (.string indexKey) descriptor different]

/-- A fresh ordinary string appends to its partition and leaves symbols unchanged. -/
theorem orderedKeys_insert_fresh_string (properties : OrderedProps) (key : JSString)
    (descriptor : PropertyDescriptor) (valid : WellFormed properties)
    (nonIndex : PropertyKey.arrayIndex? key = none)
    (absent : properties.lookup (.string key) = none) :
    (properties.insert (.string key) descriptor).stringKeys =
      properties.stringKeys ++ [.string key] ∧
    (properties.insert (.string key) descriptor).symbolKeys = properties.symbolKeys := by
  rcases properties with ⟨rep⟩
  have rawAbsent : rep.entries.get? (.string key) = none :=
    get?_none_of_lookup_none absent
  have oldValid := (wellFormed_iff_valid (.mk rep)).mp valid
  have oldMetadata := oldValid.1
  have nextMetadata := (insertRep_valid rep (.string key) descriptor oldValid).1
  have order := insertRep_fresh_string_order rep oldMetadata key nonIndex rawAbsent descriptor
  constructor
  · change stringKeys (.mk (insertRep rep (.string key) descriptor)) = _
    rw [stringKeys_eq_orderedStrings _ nextMetadata, stringKeys_eq_orderedStrings rep oldMetadata]
    exact order.1
  · change symbolKeys (.mk (insertRep rep (.string key) descriptor)) = _
    rw [symbolKeys_eq_orderedSymbols, symbolKeys_eq_orderedSymbols]
    exact order.2

/-- A fresh symbol leaves numeric indices unchanged. -/
theorem arrayIndices_insert_symbol (properties : OrderedProps) (key : SymbolId)
    (descriptor : PropertyDescriptor) (valid : WellFormed properties) :
    (properties.insert (.symbol key) descriptor).arrayIndices = properties.arrayIndices := by
  apply arrayIndices_ext _ _ (insert_wellFormed properties (.symbol key) descriptor valid) valid
  intro indexKey index parsed
  rw [lookup_insert_ne]
  intro impossible
  contradiction

/-- A fresh symbol appends to its partition and leaves ordinary strings unchanged. -/
theorem orderedKeys_insert_fresh_symbol (properties : OrderedProps) (key : SymbolId)
    (descriptor : PropertyDescriptor) (valid : WellFormed properties)
    (absent : properties.lookup (.symbol key) = none) :
    (properties.insert (.symbol key) descriptor).stringKeys = properties.stringKeys ∧
    (properties.insert (.symbol key) descriptor).symbolKeys =
      properties.symbolKeys ++ [.symbol key] := by
  rcases properties with ⟨rep⟩
  have rawAbsent : rep.entries.get? (.symbol key) = none :=
    get?_none_of_lookup_none absent
  have oldValid := (wellFormed_iff_valid (.mk rep)).mp valid
  have oldMetadata := oldValid.1
  have nextMetadata := (insertRep_valid rep (.symbol key) descriptor oldValid).1
  have order := insertRep_fresh_symbol_order rep oldMetadata key rawAbsent descriptor
  constructor
  · change stringKeys (.mk (insertRep rep (.symbol key) descriptor)) = _
    rw [stringKeys_eq_orderedStrings _ nextMetadata, stringKeys_eq_orderedStrings rep oldMetadata]
    exact order.1
  · change symbolKeys (.mk (insertRep rep (.symbol key) descriptor)) = _
    rw [symbolKeys_eq_orderedSymbols, symbolKeys_eq_orderedSymbols]
    exact order.2

/-- A fresh array index is inserted into the exact ascending numeric projection. -/
theorem arrayIndices_insert_fresh_index (properties : OrderedProps) (key : JSString) (index : Nat)
    (descriptor : PropertyDescriptor) (valid : WellFormed properties)
    (parsed : PropertyKey.arrayIndex? key = some index)
    (absent : properties.lookup (.string key) = none) :
    (properties.insert (.string key) descriptor).arrayIndices =
      (index :: properties.arrayIndices).mergeSort (· ≤ ·) := by
  let next := properties.insert (.string key) descriptor
  have nextValid := insert_wellFormed properties (.string key) descriptor valid
  have oldNodup := arrayIndices_nodup properties valid
  have indexAbsent : index ∉ properties.arrayIndices := by
    intro member
    rcases List.mem_filterMap.mp member with ⟨oldKey, oldMember, oldParsed⟩
    cases oldKey with
    | symbol symbolKey => simp at oldParsed
    | string oldString =>
        have keysEqual := PropertyKey.arrayIndex?_injective parsed oldParsed
        subst oldString
        have present := (mem_ownKeys_iff_lookup_isSome properties (.string key) valid).mp oldMember
        rw [absent] at present
        contradiction
  have expectedNodup : ((index :: properties.arrayIndices).mergeSort (· ≤ ·)).Nodup :=
    (List.mergeSort_perm _ _).nodup_iff.mpr (List.nodup_cons.mpr ⟨indexAbsent, oldNodup⟩)
  have membership : ∀ candidate,
      candidate ∈ next.arrayIndices ↔ candidate = index ∨ candidate ∈ properties.arrayIndices := by
    intro candidate
    constructor
    · intro member
      rcases List.mem_filterMap.mp member with ⟨observedKey, keyMember, observedParsed⟩
      by_cases equal : observedKey = .string key
      · subst observedKey
        exact Or.inl (Option.some.inj (observedParsed.symm.trans parsed))
      · right
        apply List.mem_filterMap.mpr
        refine ⟨observedKey, ?_, observedParsed⟩
        apply (mem_ownKeys_iff_lookup_isSome properties observedKey valid).mpr
        rw [← lookup_insert_ne properties (.string key) observedKey descriptor (Ne.symm equal)]
        exact (mem_ownKeys_iff_lookup_isSome next observedKey nextValid).mp keyMember
    · rintro (rfl | member)
      · apply List.mem_filterMap.mpr
        exact ⟨.string key,
          (mem_ownKeys_iff_lookup_isSome next (.string key) nextValid).mpr (by
            rw [lookup_insert_same]; rfl), parsed⟩
      · rcases List.mem_filterMap.mp member with ⟨observedKey, keyMember, observedParsed⟩
        apply List.mem_filterMap.mpr
        refine ⟨observedKey, ?_, observedParsed⟩
        apply (mem_ownKeys_iff_lookup_isSome next observedKey nextValid).mpr
        by_cases equal : PropertyKey.string key = observedKey
        · subst observedKey
          have oldPresent := (mem_ownKeys_iff_lookup_isSome properties (.string key) valid).mp keyMember
          rw [absent] at oldPresent
          contradiction
        · rw [lookup_insert_ne properties (.string key) observedKey descriptor equal]
          exact (mem_ownKeys_iff_lookup_isSome properties observedKey valid).mp keyMember
  have expectedSorted : ((index :: properties.arrayIndices).mergeSort (· ≤ ·)).Pairwise (· ≤ ·) := by
    have sorted := List.pairwise_mergeSort (l := index :: properties.arrayIndices)
      (le := fun left right : Nat => decide (left ≤ right)) (by
        intro left middle right leftLe rightLe
        simp at leftLe rightLe ⊢
        omega) (by
        intro left right
        simp
        omega)
    simpa using sorted
  apply pairwise_le_eq_of_perm (ownKeys_indices_ascending next nextValid) expectedSorted
  rw [List.perm_iff_count]
  intro candidate
  change List.count candidate next.arrayIndices = List.count candidate
    ((index :: properties.arrayIndices).mergeSort (· ≤ ·))
  rw [(arrayIndices_nodup next nextValid).count, expectedNodup.count]
  simp [membership]

/-- Fresh index insertion leaves ordinary-string and symbol partitions unchanged. -/
theorem orderedKeys_insert_fresh_index (properties : OrderedProps) (key : JSString) (index : Nat)
    (descriptor : PropertyDescriptor) (valid : WellFormed properties)
    (parsed : PropertyKey.arrayIndex? key = some index)
    (absent : properties.lookup (.string key) = none) :
    (properties.insert (.string key) descriptor).stringKeys = properties.stringKeys ∧
    (properties.insert (.string key) descriptor).symbolKeys = properties.symbolKeys := by
  rcases properties with ⟨rep⟩
  have rawAbsent : rep.entries.get? (.string key) = none := get?_none_of_lookup_none absent
  have oldValid := (wellFormed_iff_valid (.mk rep)).mp valid
  have nextMetadata := (insertRep_valid rep (.string key) descriptor oldValid).1
  have order := insertRep_fresh_index_order rep oldValid.1 key index parsed rawAbsent descriptor
  constructor
  · change stringKeys (.mk (insertRep rep (.string key) descriptor)) = _
    rw [stringKeys_eq_orderedStrings _ nextMetadata, stringKeys_eq_orderedStrings rep oldValid.1]
    exact order.1
  · change symbolKeys (.mk (insertRep rep (.string key) descriptor)) = _
    rw [symbolKeys_eq_orderedSymbols, symbolKeys_eq_orderedSymbols]
    exact order.2

/-- Deletion removes exactly the requested key from each insertion-order partition. -/
theorem orderedKeys_delete (properties : OrderedProps) (key : PropertyKey)
    (valid : WellFormed properties) :
    (properties.delete key).stringKeys = properties.stringKeys.erase key ∧
    (properties.delete key).symbolKeys = properties.symbolKeys.erase key := by
  rcases properties with ⟨rep⟩
  have oldValid := (wellFormed_iff_valid (.mk rep)).mp valid
  have nextValid := deleteRep_valid rep key oldValid
  have order := deleteRep_order rep key oldValid.1
  constructor
  · change stringKeys (.mk (deleteRep rep key)) = _
    rw [stringKeys_eq_orderedStrings _ nextValid.1, stringKeys_eq_orderedStrings rep oldValid.1]
    exact order.1
  · change symbolKeys (.mk (deleteRep rep key)) = _
    rw [symbolKeys_eq_orderedSymbols, symbolKeys_eq_orderedSymbols]
    exact order.2

private theorem stringKeys_nodup (properties : OrderedProps) (valid : WellFormed properties) :
    properties.stringKeys.Nodup := by
  unfold stringKeys
  exact (ownKeys_nodup properties valid).sublist List.filter_sublist

private theorem symbolKeys_nodup (properties : OrderedProps) (valid : WellFormed properties) :
    properties.symbolKeys.Nodup := by
  unfold symbolKeys
  exact (ownKeys_nodup properties valid).sublist List.filter_sublist

/-- Deleting an ordinary string leaves the numeric index projection unchanged. -/
theorem arrayIndices_delete_nonIndex_string (properties : OrderedProps) (key : JSString)
    (valid : WellFormed properties) (nonIndex : PropertyKey.arrayIndex? key = none) :
    (properties.delete (.string key)).arrayIndices = properties.arrayIndices := by
  have nextValid := delete_wellFormed properties (.string key) valid
  apply arrayIndices_ext _ _ nextValid valid
  intro indexKey index parsed
  have different : PropertyKey.string key ≠ .string indexKey := by
    intro equal
    cases equal
    rw [nonIndex] at parsed
    contradiction
  rw [lookup_delete_ne properties (.string key) (.string indexKey) different valid]

/-- Deleting a symbol leaves the numeric index projection unchanged. -/
theorem arrayIndices_delete_symbol (properties : OrderedProps) (key : SymbolId)
    (valid : WellFormed properties) :
    (properties.delete (.symbol key)).arrayIndices = properties.arrayIndices := by
  have nextValid := delete_wellFormed properties (.symbol key) valid
  apply arrayIndices_ext _ _ nextValid valid
  intro indexKey index parsed
  rw [lookup_delete_ne properties (.symbol key) (.string indexKey) (by
    intro impossible
    contradiction) valid]

/-- Deleting an array index removes exactly that number from the ascending projection. -/
theorem arrayIndices_delete_index (properties : OrderedProps) (key : JSString) (index : Nat)
    (valid : WellFormed properties) (parsed : PropertyKey.arrayIndex? key = some index) :
    (properties.delete (.string key)).arrayIndices = properties.arrayIndices.erase index := by
  let next := properties.delete (.string key)
  have nextValid := delete_wellFormed properties (.string key) valid
  have oldNodup := arrayIndices_nodup properties valid
  have expectedNodup := oldNodup.erase index
  have membership : ∀ candidate,
      candidate ∈ next.arrayIndices ↔ candidate ≠ index ∧ candidate ∈ properties.arrayIndices := by
    intro candidate
    constructor
    · intro member
      rcases List.mem_filterMap.mp member with ⟨observedKey, keyMember, observedParsed⟩
      have different : PropertyKey.string key ≠ observedKey := by
        intro equal
        subst observedKey
        have absent := (mem_ownKeys_iff_lookup_isSome next (.string key) nextValid).mp keyMember
        rw [lookup_delete_same properties (.string key) valid] at absent
        contradiction
      refine ⟨?_, ?_⟩
      · intro indicesEqual
        cases observedKey with
        | symbol symbolKey => simp at observedParsed
        | string observedString =>
            subst candidate
            have keysEqual := PropertyKey.arrayIndex?_injective parsed observedParsed
            exact different (congrArg PropertyKey.string keysEqual)
      · apply List.mem_filterMap.mpr
        refine ⟨observedKey, ?_, observedParsed⟩
        apply (mem_ownKeys_iff_lookup_isSome properties observedKey valid).mpr
        rw [← lookup_delete_ne properties (.string key) observedKey different valid]
        exact (mem_ownKeys_iff_lookup_isSome next observedKey nextValid).mp keyMember
    · rintro ⟨notIndex, member⟩
      rcases List.mem_filterMap.mp member with ⟨observedKey, keyMember, observedParsed⟩
      have different : PropertyKey.string key ≠ observedKey := by
        intro equal
        subst observedKey
        exact notIndex (Option.some.inj (observedParsed.symm.trans parsed))
      apply List.mem_filterMap.mpr
      refine ⟨observedKey, ?_, observedParsed⟩
      apply (mem_ownKeys_iff_lookup_isSome next observedKey nextValid).mpr
      rw [lookup_delete_ne properties (.string key) observedKey different valid]
      exact (mem_ownKeys_iff_lookup_isSome properties observedKey valid).mp keyMember
  have expectedSorted : (properties.arrayIndices.erase index).Pairwise (· ≤ ·) :=
    (ownKeys_indices_ascending properties valid).sublist
      (List.erase_sublist (l := properties.arrayIndices) (a := index))
  apply pairwise_le_eq_of_perm (ownKeys_indices_ascending next nextValid) expectedSorted
  rw [List.perm_iff_count]
  intro candidate
  change List.count candidate next.arrayIndices = List.count candidate (properties.arrayIndices.erase index)
  rw [(arrayIndices_nodup next nextValid).count, expectedNodup.count]
  simp [membership, oldNodup.mem_erase_iff]

private theorem arrayIndexString_parse_of_mem (properties : OrderedProps) {index : Nat}
    (member : index ∈ properties.arrayIndices) :
    PropertyKey.arrayIndex? (PropertyKey.arrayIndexString index) = some index := by
  rcases List.mem_filterMap.mp member with ⟨key, keyMember, parsed⟩
  cases key with
  | symbol symbolKey => simp at parsed
  | string stringKey =>
      rw [← PropertyKey.arrayIndex?_sound parsed]
      exact parsed

/-- Deletion removes exactly one key from the complete observable own-key sequence. -/
theorem ownKeys_delete (properties : OrderedProps) (key : PropertyKey)
    (valid : WellFormed properties) :
    (properties.delete key).ownKeys = properties.ownKeys.erase key := by
  have nextValid := delete_wellFormed properties key valid
  have ordered := orderedKeys_delete properties key valid
  rw [(ownKeys_nodup properties valid).erase_eq_filter]
  rw [ownKeys_eq_projections _ nextValid, ownKeys_eq_projections _ valid,
    List.filter_append, List.filter_append]
  cases key with
  | string stringKey =>
      cases parsed : PropertyKey.arrayIndex? stringKey with
      | some index =>
          have arrays := arrayIndices_delete_index properties stringKey index valid parsed
          have stringsAbsent : PropertyKey.string stringKey ∉ properties.stringKeys := by
            intro member
            rw [stringKeys] at member
            simp [parsed] at member
          have symbolsAbsent : PropertyKey.string stringKey ∉ properties.symbolKeys := by
            intro member
            rw [symbolKeys] at member
            simp at member
          have stringsFilter : properties.stringKeys.filter (· != PropertyKey.string stringKey) =
              properties.stringKeys := by
            rw [← (stringKeys_nodup properties valid).erase_eq_filter,
              List.erase_eq_self_iff.mpr stringsAbsent]
          have symbolsFilter : properties.symbolKeys.filter (· != PropertyKey.string stringKey) =
              properties.symbolKeys := by
            rw [← (symbolKeys_nodup properties valid).erase_eq_filter,
              List.erase_eq_self_iff.mpr symbolsAbsent]
          have arrayFilter :
              (properties.arrayIndices.erase index).map (fun value =>
                PropertyKey.string (PropertyKey.arrayIndexString value)) =
              (properties.arrayIndices.map (fun value =>
                PropertyKey.string (PropertyKey.arrayIndexString value))).filter
                (· != PropertyKey.string stringKey) := by
            rw [(arrayIndices_nodup properties valid).erase_eq_filter, List.filter_map]
            congr 1
            apply List.filter_congr
            intro value member
            have valueParsed := arrayIndexString_parse_of_mem properties member
            rw [PropertyKey.arrayIndex?_sound parsed]
            by_cases equal : value = index
            · subst value
              simp
            · have indexParsed : PropertyKey.arrayIndex? (PropertyKey.arrayIndexString index) =
                  some index := by
                rw [← PropertyKey.arrayIndex?_sound parsed]
                exact parsed
              have stringsNe : PropertyKey.string (PropertyKey.arrayIndexString value) ≠
                  PropertyKey.string (PropertyKey.arrayIndexString index) := by
                intro stringsEqual
                have parsedEqual := congrArg PropertyKey.arrayIndex?
                  (PropertyKey.string.inj stringsEqual)
                rw [valueParsed, indexParsed] at parsedEqual
                exact equal (Option.some.inj parsedEqual)
              rw [bne_iff_ne.mpr equal]
              change true = (PropertyKey.string (PropertyKey.arrayIndexString value) !=
                PropertyKey.string (PropertyKey.arrayIndexString index))
              exact (bne_iff_ne.mpr stringsNe).symm
          rw [arrays, ordered.1, ordered.2,
            List.erase_eq_self_iff.mpr stringsAbsent, List.erase_eq_self_iff.mpr symbolsAbsent,
            arrayFilter, stringsFilter, symbolsFilter]
      | none =>
          have arrays := arrayIndices_delete_nonIndex_string properties stringKey valid parsed
          have symbolsAbsent : PropertyKey.string stringKey ∉ properties.symbolKeys := by
            intro member
            rw [symbolKeys] at member
            simp at member
          have symbolsFilter : properties.symbolKeys.filter (· != PropertyKey.string stringKey) =
              properties.symbolKeys := by
            rw [← (symbolKeys_nodup properties valid).erase_eq_filter,
              List.erase_eq_self_iff.mpr symbolsAbsent]
          have arrayFilter :
              (properties.arrayIndices.map (fun value =>
                PropertyKey.string (PropertyKey.arrayIndexString value))).filter
                (· != PropertyKey.string stringKey) =
              properties.arrayIndices.map (fun value =>
                PropertyKey.string (PropertyKey.arrayIndexString value)) := by
            rw [List.filter_eq_self]
            intro observed member
            rcases List.mem_map.mp member with ⟨value, valueMember, rfl⟩
            have valueParsed := arrayIndexString_parse_of_mem properties valueMember
            have different : PropertyKey.string (PropertyKey.arrayIndexString value) ≠
                PropertyKey.string stringKey := by
              intro equal
              have stringsEqual := PropertyKey.string.inj equal
              rw [← stringsEqual, valueParsed] at parsed
              contradiction
            simp [different]
          rw [arrays, ordered.1, ordered.2,
            (stringKeys_nodup properties valid).erase_eq_filter,
            List.erase_eq_self_iff.mpr symbolsAbsent, arrayFilter, symbolsFilter]
  | symbol symbolKey =>
      have arrays := arrayIndices_delete_symbol properties symbolKey valid
      have stringsAbsent : PropertyKey.symbol symbolKey ∉ properties.stringKeys := by
        intro member
        rw [stringKeys] at member
        simp at member
      have stringsFilter : properties.stringKeys.filter (· != PropertyKey.symbol symbolKey) =
          properties.stringKeys := by
        rw [← (stringKeys_nodup properties valid).erase_eq_filter,
          List.erase_eq_self_iff.mpr stringsAbsent]
      have arrayFilter :
          (properties.arrayIndices.map (fun value =>
            PropertyKey.string (PropertyKey.arrayIndexString value))).filter
              (· != PropertyKey.symbol symbolKey) =
          properties.arrayIndices.map (fun value =>
            PropertyKey.string (PropertyKey.arrayIndexString value)) := by
        rw [List.filter_eq_self]
        intro observed member
        rcases List.mem_map.mp member with ⟨value, valueMember, rfl⟩
        simp
      rw [arrays, ordered.1, ordered.2,
        List.erase_eq_self_iff.mpr stringsAbsent,
        (symbolKeys_nodup properties valid).erase_eq_filter, arrayFilter, stringsFilter]

/-- Deleting and reinserting a live ordinary string moves it to the end of its partition. -/
theorem projections_delete_insert_string (properties : OrderedProps) (key : JSString)
    (descriptor : PropertyDescriptor) (valid : WellFormed properties)
    (nonIndex : PropertyKey.arrayIndex? key = none)
    (present : (properties.lookup (.string key)).isSome) :
    let next := (properties.delete (.string key)).insert (.string key) descriptor
    next.arrayIndices = properties.arrayIndices ∧
    next.stringKeys = properties.stringKeys.erase (.string key) ++ [.string key] ∧
    next.symbolKeys = properties.symbolKeys := by
  dsimp only
  have _wasLive := (mem_ownKeys_iff_lookup_isSome properties (.string key) valid).mpr present
  have deletedValid := delete_wellFormed properties (.string key) valid
  have deletedAbsent := lookup_delete_same properties (.string key) valid
  have inserted := orderedKeys_insert_fresh_string (properties.delete (.string key)) key descriptor
    deletedValid nonIndex deletedAbsent
  have deletedOrder := orderedKeys_delete properties (.string key) valid
  refine ⟨?_, ?_, ?_⟩
  · rw [arrayIndices_insert_nonIndex_string _ key descriptor deletedValid nonIndex,
      arrayIndices_delete_nonIndex_string properties key valid nonIndex]
  · rw [inserted.1, deletedOrder.1]
  · rw [inserted.2, deletedOrder.2]
    simp [symbolKeys]

/-- Deleting and reinserting a live symbol moves it to the end of its partition. -/
theorem projections_delete_insert_symbol (properties : OrderedProps) (key : SymbolId)
    (descriptor : PropertyDescriptor) (valid : WellFormed properties)
    (present : (properties.lookup (.symbol key)).isSome) :
    let next := (properties.delete (.symbol key)).insert (.symbol key) descriptor
    next.arrayIndices = properties.arrayIndices ∧
    next.stringKeys = properties.stringKeys ∧
    next.symbolKeys = properties.symbolKeys.erase (.symbol key) ++ [.symbol key] := by
  dsimp only
  have _wasLive := (mem_ownKeys_iff_lookup_isSome properties (.symbol key) valid).mpr present
  have deletedValid := delete_wellFormed properties (.symbol key) valid
  have deletedAbsent := lookup_delete_same properties (.symbol key) valid
  have inserted := orderedKeys_insert_fresh_symbol (properties.delete (.symbol key)) key descriptor
    deletedValid deletedAbsent
  have deletedOrder := orderedKeys_delete properties (.symbol key) valid
  refine ⟨?_, ?_, ?_⟩
  · rw [arrayIndices_insert_symbol _ key descriptor deletedValid,
      arrayIndices_delete_symbol properties key valid]
  · rw [inserted.1, deletedOrder.1]
    simp [stringKeys]
  · rw [inserted.2, deletedOrder.2]

/-- Deleting and reinserting a live array index restores the same numeric key order. -/
theorem ownKeys_delete_insert_index (properties : OrderedProps) (key : JSString)
    (descriptor : PropertyDescriptor) (valid : WellFormed properties)
    (index : Nat) (parsed : PropertyKey.arrayIndex? key = some index)
    (present : (properties.lookup (.string key)).isSome) :
    ((properties.delete (.string key)).insert (.string key) descriptor).ownKeys = properties.ownKeys := by
  let deleted := properties.delete (.string key)
  let next := deleted.insert (.string key) descriptor
  have deletedValid := delete_wellFormed properties (.string key) valid
  have nextValid := insert_wellFormed deleted (.string key) descriptor deletedValid
  have deletedAbsent := lookup_delete_same properties (.string key) valid
  have orderInsert := orderedKeys_insert_fresh_index deleted key index descriptor deletedValid parsed deletedAbsent
  have orderDelete := orderedKeys_delete properties (.string key) valid
  have stringAbsent : PropertyKey.string key ∉ properties.stringKeys := by
    intro member
    rw [stringKeys] at member
    simp [parsed] at member
  have symbolAbsent : PropertyKey.string key ∉ properties.symbolKeys := by
    intro member
    rw [symbolKeys] at member
    simp at member
  have stringErase := List.erase_eq_self_iff.mpr stringAbsent
  have symbolErase := List.erase_eq_self_iff.mpr symbolAbsent
  have indices : next.arrayIndices = properties.arrayIndices := by
    apply arrayIndices_ext next properties nextValid valid
    intro query queryIndex queryParsed
    by_cases equal : PropertyKey.string key = .string query
    · have stringsEqual := PropertyKey.string.inj equal
      subst query
      rw [lookup_insert_same]
      exact present.symm
    · rw [lookup_insert_ne deleted (.string key) (.string query) descriptor equal,
        lookup_delete_ne properties (.string key) (.string query) equal valid]
  rw [ownKeys_eq_projections next nextValid, ownKeys_eq_projections properties valid,
    indices, orderInsert.1, orderInsert.2, orderDelete.1, orderDelete.2,
    stringErase, symbolErase]

private theorem compactStrings_observable (properties : OrderedPropsRep) (valid : ValidRep properties) :
    let compacted := compactStrings properties.entries properties.stringOrder
    let next : OrderedProps := .mk
      ⟨compacted.1, compacted.2, properties.symbolOrder, 0, properties.symbolTombstones⟩
    next.ownKeys = (.mk properties : OrderedProps).ownKeys ∧
      ∀ key, next.lookup key = (.mk properties : OrderedProps).lookup key := by
  let compacted := compactStrings properties.entries properties.stringOrder
  let nextRep : OrderedPropsRep :=
    ⟨compacted.1, compacted.2, properties.symbolOrder, 0, properties.symbolTombstones⟩
  have nextValid : ValidRep nextRep :=
    compactStrings_valid properties valid.1 valid.2.2.1 valid.2.2.2.2
  have oldWellFormed := (wellFormed_iff_valid (.mk properties)).mpr valid
  have nextWellFormed := (wellFormed_iff_valid (.mk nextRep)).mpr nextValid
  have lookupEqual : ∀ key, (.mk nextRep : OrderedProps).lookup key =
      (.mk properties : OrderedProps).lookup key := by
    intro key
    unfold lookup nextRep compacted compactStrings
    exact compactOrder_descriptor .string properties.entries properties.stringOrder key
  have indices : (.mk nextRep : OrderedProps).arrayIndices =
      (.mk properties : OrderedProps).arrayIndices := by
    apply arrayIndices_ext _ _ nextWellFormed oldWellFormed
    intro stringKey index parsed
    simp only [lookupEqual]
  have strings : (.mk nextRep : OrderedProps).stringKeys =
      (.mk properties : OrderedProps).stringKeys := by
    rw [stringKeys_eq_orderedStrings nextRep nextValid.1,
      stringKeys_eq_orderedStrings properties valid.1]
    exact compactStrings_orderedStrings properties valid.1
  have symbols : (.mk nextRep : OrderedProps).symbolKeys =
      (.mk properties : OrderedProps).symbolKeys := by
    rw [symbolKeys_eq_orderedSymbols, symbolKeys_eq_orderedSymbols]
    exact compactStrings_orderedSymbols properties
  dsimp only
  constructor
  · rw [ownKeys_eq_projections _ nextWellFormed, ownKeys_eq_projections _ oldWellFormed,
      indices, strings, symbols]
  · exact lookupEqual

private theorem compactSymbols_observable (properties : OrderedPropsRep) (valid : ValidRep properties) :
    let compacted := compactSymbols properties.entries properties.symbolOrder
    let next : OrderedProps := .mk
      ⟨compacted.1, properties.stringOrder, compacted.2, properties.stringTombstones, 0⟩
    next.ownKeys = (.mk properties : OrderedProps).ownKeys ∧
      ∀ key, next.lookup key = (.mk properties : OrderedProps).lookup key := by
  let compacted := compactSymbols properties.entries properties.symbolOrder
  let nextRep : OrderedPropsRep :=
    ⟨compacted.1, properties.stringOrder, compacted.2, properties.stringTombstones, 0⟩
  have nextValid : ValidRep nextRep :=
    compactSymbols_valid properties valid.1 valid.2.1 valid.2.2.2.1
  have oldWellFormed := (wellFormed_iff_valid (.mk properties)).mpr valid
  have nextWellFormed := (wellFormed_iff_valid (.mk nextRep)).mpr nextValid
  have lookupEqual : ∀ key, (.mk nextRep : OrderedProps).lookup key =
      (.mk properties : OrderedProps).lookup key := by
    intro key
    unfold lookup nextRep compacted compactSymbols
    exact compactOrder_descriptor .symbol properties.entries properties.symbolOrder key
  have indices : (.mk nextRep : OrderedProps).arrayIndices =
      (.mk properties : OrderedProps).arrayIndices := by
    apply arrayIndices_ext _ _ nextWellFormed oldWellFormed
    intro stringKey index parsed
    simp only [lookupEqual]
  have strings : (.mk nextRep : OrderedProps).stringKeys =
      (.mk properties : OrderedProps).stringKeys := by
    rw [stringKeys_eq_orderedStrings nextRep nextValid.1,
      stringKeys_eq_orderedStrings properties valid.1]
    exact compactSymbols_orderedStrings properties
  have symbols : (.mk nextRep : OrderedProps).symbolKeys =
      (.mk properties : OrderedProps).symbolKeys := by
    rw [symbolKeys_eq_orderedSymbols, symbolKeys_eq_orderedSymbols]
    exact compactSymbols_orderedSymbols properties valid.1
  dsimp only
  constructor
  · rw [ownKeys_eq_projections _ nextWellFormed, ownKeys_eq_projections _ oldWellFormed,
      indices, strings, symbols]
  · exact lookupEqual

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
