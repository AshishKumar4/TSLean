import TSLean.Refinement.Core
import TSLean.Refinement.Evidence

namespace TSLean.Refinement

open TSLean.JS

namespace Array

/-- The canonical own key for an array index. -/
def indexKey (index : Nat) : PropertyKey :=
  .string (PropertyKey.arrayIndexString index)

private def denseKeysFrom (first : Nat) : Nat → List PropertyKey
  | 0 => [Heap.lengthPropertyKey]
  | remaining + 1 => indexKey first :: denseKeysFrom (first + 1) remaining

/-- Exact own-key sequence of a dense array of the given length: every index key in ascending order
followed by the synthetic `length` key.

Specification only. Never evaluate this on an array's *declared* length: a sparse array may declare
2³² - 1 and materializing that sequence is the unbounded cost `matchesDenseKeys` exists to avoid. -/
def denseKeys (length : Nat) : List PropertyKey := denseKeysFrom 0 length

private def matchesDenseKeysFrom (first : Nat) : Nat → List PropertyKey → Bool
  | 0, keys => keys == [Heap.lengthPropertyKey]
  | _ + 1, [] => false
  | remaining + 1, key :: rest =>
      key == indexKey first && matchesDenseKeysFrom (first + 1) remaining rest

/-- Decides `keys = denseKeys length` in one pass over `keys`, stopping at the first difference. The
expected sequence is never materialized, so a sparse object costs its own key count rather than its
declared length. -/
def matchesDenseKeys (length : Nat) (keys : List PropertyKey) : Bool :=
  matchesDenseKeysFrom 0 length keys

private theorem denseKeysFrom_length (first remaining : Nat) :
    (denseKeysFrom first remaining).length = remaining + 1 := by
  induction remaining generalizing first with
  | zero => rfl
  | succ remaining ih => simp [denseKeysFrom, ih]

/-- The dense key sequence has one key per index plus `length`, so it determines the length. -/
theorem denseKeys_injective {left right : Nat} (equal : denseKeys left = denseKeys right) :
    left = right := by
  have lengths := congrArg List.length equal
  simpa [denseKeys, denseKeysFrom_length] using lengths

private theorem denseKeysFrom_eq_range' (first remaining : Nat) :
    denseKeysFrom first remaining =
      (List.range' first remaining).map indexKey ++ [Heap.lengthPropertyKey] := by
  induction remaining generalizing first with
  | zero => rfl
  | succ remaining ih => simp [denseKeysFrom, List.range'_succ, ih]

/-- The dense key sequence is the ascending index keys followed by `length`. -/
theorem denseKeys_eq_range (length : Nat) :
    denseKeys length = (List.range length).map indexKey ++ [Heap.lengthPropertyKey] := by
  rw [denseKeys, denseKeysFrom_eq_range', List.range_eq_range']

private theorem matchesDenseKeysFrom_iff (first remaining : Nat) (keys : List PropertyKey) :
    matchesDenseKeysFrom first remaining keys = true ↔ keys = denseKeysFrom first remaining := by
  induction remaining generalizing first keys with
  | zero => simp [matchesDenseKeysFrom, denseKeysFrom]
  | succ remaining ih =>
      cases keys with
      | nil => simp [matchesDenseKeysFrom, denseKeysFrom]
      | cons key rest => simp [matchesDenseKeysFrom, denseKeysFrom, ih]

/-- The streamed key check accepts exactly the dense own-key sequence. -/
theorem matchesDenseKeys_iff (length : Nat) (keys : List PropertyKey) :
    matchesDenseKeys length keys = true ↔ keys = denseKeys length :=
  matchesDenseKeysFrom_iff 0 length keys

/-- Typed failures produced while validating the dense-array boundary. -/
inductive ShapeFault where
  | expectedObject
  | invalidRef (ref : RefId)
  | wrongKind (actual : ObjectKindTag)
  | wrongPrototype (actual : RefId)
  | notExtensible
  | nonWritableLength
  | unexpectedKeys (actual : List PropertyKey)
  | malformedIndex (index : Nat)
  deriving DecidableEq

/-- Reads each index as an exact dense data element. Every other own-property observation at that
index, including absence, is reported as one malformed element. -/
private def readDenseIndices (heap : Heap) (root : RefId) :
    List Nat → _root_.Array Value → Except ShapeFault (_root_.Array Value)
  | [], values => .ok values
  | index :: rest, values =>
      match heap.getOwnProperty root (indexKey index) with
      | .ok (some (.data ⟨value, true, true, true⟩)) =>
          readDenseIndices heap root rest (values.push value)
      | _ => .error (.malformedIndex index)

/-- Validates and materializes only the exact dense shape accepted by this refinement: an
extensible array object with a null prototype, a writable length, and exactly the dense own keys.

Every step costs the object's actual own-key count. The length is read from the array's own slots
rather than from the descriptor `getOwnProperty` synthesizes out of them, and the key check streams
against the expected sequence instead of building it, so a sparse array with a huge declared length
is rejected in the number of keys it really has. -/
def inspectDense (heap : Heap) (value : Value) :
    Except ShapeFault (RefId × _root_.Array Value) := do
  let root ← match value with
    | .object ref => pure ref
    | .primitive _ => throw .expectedObject
  let object ← match heap.get? root with
    | .ok object => pure object
    | .error _ => throw (.invalidRef root)
  let slots ← match object.kind with
    | .array slots => pure slots
    | actual => throw (.wrongKind actual.tag)
  match object.prototype with
    | some prototype => throw (.wrongPrototype prototype)
    | none => pure ()
  if !object.extensible then throw .notExtensible
  if !slots.lengthWritable then throw .nonWritableLength
  -- `ownPropertyKeys` reads through the same `get?` that already succeeded above for this heap and
  -- root, so its failure branch is unreachable; it repeats that read's fault rather than invent one.
  let keys ← match heap.ownPropertyKeys root with
    | .ok keys => pure keys
    | .error _ => throw (.invalidRef root)
  if !matchesDenseKeys slots.length keys then throw (.unexpectedKeys keys)
  let values ← readDenseIndices heap root (List.range slots.length) #[]
  pure (root, values)

private theorem readDenseIndices_sound (heap : Heap) (root : RefId) :
    ∀ (indices : List Nat) (accumulated values : _root_.Array Value),
      readDenseIndices heap root indices accumulated = .ok values →
      values.size = accumulated.size + indices.length ∧
      (∀ index, index < accumulated.size → values[index]? = accumulated[index]?) ∧
      ∀ (position : Nat) (inBounds : position < indices.length), ∃ encoded,
        values[accumulated.size + position]? = some encoded ∧
        heap.getOwnProperty root (indexKey indices[position]) =
          .ok (some (.data ⟨encoded, true, true, true⟩))
  | [], accumulated, values, read => by
      simp only [readDenseIndices, Except.ok.injEq] at read
      subst read
      exact ⟨by simp, fun index _ => rfl, fun position inBounds => by simp at inBounds⟩
  | index :: rest, accumulated, values, read => by
      unfold readDenseIndices at read
      split at read
      · rename_i element found
        obtain ⟨size, prefixEq, elements⟩ :=
          readDenseIndices_sound heap root rest (accumulated.push element) values read
        have pushSize : (accumulated.push element).size = accumulated.size + 1 := by simp
        refine ⟨by simp [size, pushSize]; omega, ?_, ?_⟩
        · intro position inRange
          rw [prefixEq position (by omega), Array.getElem?_push]
          simp [Nat.ne_of_lt inRange]
        · intro position inBounds
          match position with
          | 0 =>
              refine ⟨element, ?_, by simpa using found⟩
              rw [Nat.add_zero, prefixEq accumulated.size (by omega), Array.getElem?_push]
              simp
          | next + 1 =>
              obtain ⟨encoded, valueEq, elementFound⟩ :=
                elements next (by simpa using Nat.lt_of_succ_lt_succ inBounds)
              refine ⟨encoded, ?_, by simpa using elementFound⟩
              rw [pushSize] at valueEq
              simpa [Nat.add_assoc, Nat.add_comm 1] using valueEq
      · exact absurd read (by simp)

private theorem readDenseIndices_complete (heap : Heap) (root : RefId) :
    ∀ (indices : List Nat) (accumulated : _root_.Array Value),
      (∀ index ∈ indices, ∃ encoded,
        heap.getOwnProperty root (indexKey index) =
          .ok (some (.data ⟨encoded, true, true, true⟩))) →
      ∃ values, readDenseIndices heap root indices accumulated = .ok values
  | [], accumulated, _ => ⟨accumulated, rfl⟩
  | index :: rest, accumulated, present => by
      obtain ⟨encoded, found⟩ := present index (by simp)
      obtain ⟨values, read⟩ :=
        readDenseIndices_complete heap root rest (accumulated.push encoded)
          (fun other member => present other (by simp [member]))
      exact ⟨values, by unfold readDenseIndices; rw [found]; exact read⟩

/-- The observable shape this refinement accepts, stated in ECMAScript observations rather than as
"the checker returned ok": one extensible array object with a null prototype and a writable length,
whose own keys are exactly the dense sequence and whose every index carries a standard data
descriptor. -/
def DenseShape (heap : Heap) (value : Value) : Prop :=
  ∃ root object slots,
    value = .object root ∧
    heap.get? root = .ok object ∧
    object.kind = .array slots ∧
    object.prototype = none ∧
    object.extensible = true ∧
    slots.lengthWritable = true ∧
    heap.ownPropertyKeys root = .ok (denseKeys slots.length) ∧
    ∀ index, index < slots.length → ∃ encoded,
      heap.getOwnProperty root (indexKey index) =
        .ok (some (.data ⟨encoded, true, true, true⟩))

/-- A successful inspection returns the inspected object's exact dense element sequence. -/
theorem inspectDense_sound {heap : Heap} {value : Value} {root : RefId}
    {values : _root_.Array Value} (inspected : inspectDense heap value = .ok (root, values)) :
    ∃ object slots,
      value = .object root ∧
      heap.get? root = .ok object ∧
      object.kind = .array slots ∧
      object.prototype = none ∧
      object.extensible = true ∧
      slots.lengthWritable = true ∧
      slots.length = values.size ∧
      heap.ownPropertyKeys root = .ok (denseKeys values.size) ∧
      ∀ index, index < values.size → ∃ encoded,
        values[index]? = some encoded ∧
        heap.getOwnProperty root (indexKey index) =
          .ok (some (.data ⟨encoded, true, true, true⟩)) := by
  cases value with
  | primitive primitive =>
      simp [inspectDense, Bind.bind, Except.bind] at inspected
  | object ref =>
      unfold inspectDense at inspected
      simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at inspected
      split at inspected <;> try (simp at inspected; done)
      rename_i object found
      split at inspected <;> try (simp at inspected; done)
      rename_i slots kindEq
      split at inspected <;> try (simp at inspected; done)
      rename_i prototypeEq
      split at inspected <;> try (simp at inspected; done)
      rename_i notExtensible
      split at inspected <;> try (simp at inspected; done)
      rename_i notWritable
      split at inspected <;> try (simp at inspected; done)
      rename_i keys keysEq
      split at inspected <;> try (simp at inspected; done)
      rename_i mismatch
      split at inspected <;> try (simp at inspected; done)
      rename_i readValues read
      simp only [Except.ok.injEq, Prod.mk.injEq] at inspected
      obtain ⟨rootEq, valuesEq⟩ := inspected
      subst rootEq
      subst valuesEq
      obtain ⟨size, _, elements⟩ :=
        readDenseIndices_sound heap ref (List.range slots.length) #[] readValues read
      have sizeEq : slots.length = readValues.size := by simpa using size.symm
      have matched : matchesDenseKeys slots.length keys = true := by simpa using mismatch
      refine ⟨object, slots, rfl, found, kindEq, prototypeEq, by simpa using notExtensible,
        by simpa using notWritable, sizeEq, ?_, ?_⟩
      · rw [keysEq, ← sizeEq]
        exact congrArg Except.ok ((matchesDenseKeys_iff slots.length keys).mp matched)
      · intro index inBounds
        obtain ⟨encoded, valueEq, elementFound⟩ := elements index (by simpa [sizeEq] using inBounds)
        exact ⟨encoded, by simpa using valueEq, by simpa using elementFound⟩

/-- Every value with the accepted shape is inspected successfully. -/
theorem inspectDense_complete {heap : Heap} {value : Value} (shape : DenseShape heap value) :
    ∃ root values, inspectDense heap value = .ok (root, values) := by
  obtain ⟨root, object, slots, rfl, found, kindEq, prototypeEq, extensibleEq, writableEq, keysEq,
    elements⟩ := shape
  obtain ⟨values, read⟩ :=
    readDenseIndices_complete heap root (List.range slots.length) #[] (by
      intro index member
      exact elements index (by simpa using member))
  have matched : matchesDenseKeys slots.length (denseKeys slots.length) = true :=
    (matchesDenseKeys_iff slots.length (denseKeys slots.length)).mpr rfl
  refine ⟨root, values, ?_⟩
  simp [inspectDense, Bind.bind, Except.bind, Pure.pure,
    Except.pure, found, kindEq, prototypeEq, extensibleEq, writableEq, keysEq, matched, read]

/-- Executable eligibility guard for the exact dense array shape. -/
def denseShapeGuard (heap : Heap) : Guard Value (DenseShape heap) :=
  Guard.create "exact dense array shape" (by decide)
    (fun value => (inspectDense heap value).isOk)
    (fun value accepted => by
      cases inspected : inspectDense heap value with
      | error fault =>
          change (inspectDense heap value).isOk = true at accepted
          rw [inspected] at accepted
          contradiction
      | ok result =>
          rcases result with ⟨root, values⟩
          obtain ⟨object, slots, valueEq, found, kindEq, prototypeEq, extensibleEq, writableEq,
            sizeEq, keysEq, elements⟩ := inspectDense_sound inspected
          refine ⟨root, object, slots, valueEq, found, kindEq, prototypeEq, extensibleEq,
            writableEq, by rw [keysEq, sizeEq], ?_⟩
          intro index inBounds
          obtain ⟨encoded, _, found⟩ := elements index (by omega)
          exact ⟨encoded, found⟩)

/-- Passing the dense-shape guard proves the value really has the accepted ECMAScript shape. -/
theorem denseShapeGuard_sound (heap : Heap) (value : Value)
    (accepted : (denseShapeGuard heap).check value = true) :
    DenseShape heap value :=
  (denseShapeGuard heap).sound value accepted

/-- Every value with the accepted shape passes the executable guard. -/
theorem denseShapeGuard_complete (heap : Heap) (value : Value) (shape : DenseShape heap value) :
    (denseShapeGuard heap).check value = true := by
  obtain ⟨root, values, inspected⟩ := inspectDense_complete shape
  change (inspectDense heap value).isOk = true
  rw [inspected]
  rfl

/-- A Lean array is represented by one exact, hole-free ECMAScript array object with a null
prototype. This is structural correspondence only: heap well-formedness is a hypothesis of the
theorems that need it, never part of the relation. -/
def DenseArrayRel (element : Refinement α)
    (heap : Heap) (native : _root_.Array α) (value : Value) : Prop :=
  ∃ root object slots,
    value = .object root ∧
    heap.get? root = .ok object ∧
    object.kind = .array slots ∧
    object.prototype = none ∧
    object.extensible = true ∧
    slots.length = native.size ∧
    slots.lengthWritable = true ∧
    heap.ownPropertyKeys root = .ok (denseKeys native.size) ∧
    ∀ index (inBounds : index < native.size), ∃ encoded,
      heap.getOwnProperty root (indexKey index) =
        .ok (some (.data ⟨encoded, true, true, true⟩)) ∧
      element.Rel heap native[index] encoded

/-- A dense relation always points at a valid root reference. -/
theorem DenseArrayRel.root_valueValid
    (related : DenseArrayRel element heap native value) :
    heap.valueValid value = true := by
  obtain ⟨root, object, slots, rfl, found, _⟩ := related
  exact decide_eq_true (Heap.get?_ok_valid heap root object found)

/-- Every related value really has the ECMAScript shape the guard decides. -/
theorem DenseArrayRel.denseShape (related : DenseArrayRel element heap native value) :
    DenseShape heap value := by
  obtain ⟨root, object, slots, valueEq, found, kindEq, prototypeEq, extensibleEq, lengthEq,
    writable, keys, elements⟩ := related
  refine ⟨root, object, slots, valueEq, found, kindEq, prototypeEq, extensibleEq, writable,
    by rw [keys, lengthEq], ?_⟩
  intro index inBounds
  obtain ⟨encoded, elementFound, _⟩ := elements index (lengthEq ▸ inBounds)
  exact ⟨encoded, elementFound⟩

/-- Exact heap extension preserves an immutable dense-array snapshot. -/
theorem DenseArrayRel.stable (extension : Heap.ExactExtension old next)
    (related : DenseArrayRel element old native value) :
    DenseArrayRel element next native value := by
  obtain ⟨root, object, slots, valueEq, found, kindEq, prototypeEq, extensibleEq, lengthEq,
    writable, keys, elements⟩ := related
  refine ⟨root, object, slots, valueEq, extension.get_eq root object found, kindEq, prototypeEq,
    extensibleEq, lengthEq, writable, ?_, ?_⟩
  · rw [extension.preserves_ownPropertyKeys root object found]
    exact keys
  · intro index inBounds
    obtain ⟨encoded, elementFound, elementRelated⟩ := elements index inBounds
    refine ⟨encoded, ?_, element.stable extension elementRelated⟩
    rw [extension.preserves_getOwnProperty root object found]
    exact elementFound

/-- Immutable snapshot refinement for Lean arrays: one exact, hole-free ECMAScript array object with
a null prototype, as `DenseArrayRel` spells out. -/
def refinement (element : Refinement α) : Refinement (_root_.Array α) where
  Rel := DenseArrayRel element
  valueValid := DenseArrayRel.root_valueValid
  stable := DenseArrayRel.stable

/-- Dense snapshots decode uniquely when each element does. -/
theorem refinement_uniqueDecode (unique : element.UniqueDecode) :
    (refinement element).UniqueDecode := by
  intro heap left right value leftRelated rightRelated
  obtain ⟨leftRoot, leftObject, leftSlots, leftValueEq, leftFound, leftKind, leftPrototype,
    leftExtensible, leftLength, leftWritable, leftKeys, leftElements⟩ := leftRelated
  obtain ⟨rightRoot, rightObject, rightSlots, rightValueEq, rightFound, rightKind, rightPrototype,
    rightExtensible, rightLength, rightWritable, rightKeys, rightElements⟩ := rightRelated
  have rootsEqual : leftRoot = rightRoot := by
    rw [leftValueEq] at rightValueEq
    exact Value.object.inj rightValueEq
  subst rightRoot
  rw [leftFound] at rightFound
  have objectsEqual : leftObject = rightObject := Except.ok.inj rightFound
  subst rightObject
  rw [leftKind] at rightKind
  have slotsEqual : leftSlots = rightSlots := ObjectKind.array.inj rightKind
  subst rightSlots
  apply _root_.Array.ext
  · exact leftLength.symm.trans rightLength
  · intro index leftBound rightBound
    obtain ⟨leftValue, leftElementFound, leftElement⟩ := leftElements index leftBound
    obtain ⟨rightValue, rightElementFound, rightElement⟩ := rightElements index rightBound
    rw [leftElementFound] at rightElementFound
    have valuesEqual : leftValue = rightValue := by
      have descriptorsEqual :=
        PropertyDescriptor.data.inj (Option.some.inj (Except.ok.inj rightElementFound))
      cases descriptorsEqual
      rfl
    subst rightValue
    exact unique leftElement rightElement

/-- Dense array length observation commutes with Lean array size. -/
theorem length_commutes (related : DenseArrayRel element heap native value) :
    ∃ root, value = .object root ∧ heap.arrayLength root = .ok native.size := by
  obtain ⟨root, object, slots, valueEq, found, kindEq, prototypeEq, extensibleEq, lengthEq,
    writable, keys, elements⟩ := related
  refine ⟨root, valueEq, ?_⟩
  unfold Heap.arrayLength
  rw [found]
  simp only [Bind.bind, Except.bind]
  rw [kindEq]
  exact congrArg Except.ok lengthEq

/-- An in-bounds own-index read returns a value refining the matching Lean element. -/
theorem getOwnProperty_commutes
    (related : DenseArrayRel element heap native value)
    (index : Nat) (inBounds : index < native.size) :
    ∃ root encoded,
      value = .object root ∧
      heap.getOwnProperty root (indexKey index) =
        .ok (some (.data ⟨encoded, true, true, true⟩)) ∧
      element.Rel heap native[index] encoded := by
  obtain ⟨root, object, slots, valueEq, found, kindEq, prototypeEq, extensibleEq, lengthEq,
    writable, keys, elements⟩ := related
  obtain ⟨encoded, elementFound, elementRelated⟩ := elements index inBounds
  exact ⟨root, encoded, valueEq, elementFound, elementRelated⟩

/-- Every element stored by a dense relation is valid in the same heap. -/
theorem DenseArrayRel.element_valueValid
    (related : DenseArrayRel element heap native value)
    (index : Nat) (inBounds : index < native.size) :
    ∃ root encoded,
      value = .object root ∧
      heap.getOwnProperty root (indexKey index) =
        .ok (some (.data ⟨encoded, true, true, true⟩)) ∧
      heap.valueValid encoded = true := by
  obtain ⟨root, encoded, valueEq, elementFound, elementRelated⟩ :=
    getOwnProperty_commutes related index inBounds
  exact ⟨root, encoded, valueEq, elementFound, element.valueValid elementRelated⟩

/-- A root returned by `Heap.allocateArray` differs from every reference valid before it ran. -/
theorem fresh_root_distinct (old next : Heap) (elements : List (Option Value))
    (prototype : Option RefId) (fresh previous : RefId)
    (allocated : old.allocateArray elements prototype = .ok (fresh, next))
    (previousValid : old.valueValid (.object previous) = true) : fresh ≠ previous := by
  obtain ⟨freshIndex, _⟩ :=
    Heap.allocateArray_result_fresh_kind old next elements prototype fresh allocated
  exact Heap.fresh_distinct_of_oldValid old fresh previous (Nat.le_of_eq freshIndex.symm)
    previousValid

/-- Array-level encoding failures preserve the exact failing element index.

`tooLong` is pinned by `encode_tooLong`. `allocation` cannot fire on a representable array in a
well-formed heap, which is what `encode_total` establishes. `element` is unreachable for every
element codec committed in this repository — `Bool`, `BigInt`, `String` and `Float` all encode with
`Empty` faults — but it stays because the element codec is a parameter, not a fixed set. -/
inductive EncodeFault (ElementFault : Type u) where
  | tooLong (length : Nat)
  | element (index : Nat) (fault : ElementFault)
  | allocation (fault : DefinePropertyFault)
  deriving DecidableEq

/-- Array-level decoding distinguishes shape rejection from element rejection. -/
inductive DecodeFault (ElementFault : Type u) where
  | shape (fault : ShapeFault)
  | element (index : Nat) (fault : ElementFault)
  deriving DecidableEq

private def encodeValues (elementCodec : Codec α ElementEncodeFault ElementDecodeFault element)
    (source : List α) (index : Nat) (heap : Heap) (values : _root_.Array Value) :
    Except (EncodeFault ElementEncodeFault) (_root_.Array Value × Heap) :=
  match source with
  | [] => .ok (values, heap)
  | native :: rest =>
      match elementCodec.encode heap native with
      | .error fault => .error (.element index fault)
      | .ok (value, next) => encodeValues elementCodec rest (index + 1) next (values.push value)

/-- Sequentially encodes elements through the heap, then allocates one fresh null-prototype array
holding exactly them. The encoder never produces a hole. -/
def encode (elementCodec : Codec α ElementEncodeFault ElementDecodeFault element)
    (heap : Heap) (native : _root_.Array α) :
    Except (EncodeFault ElementEncodeFault) (Value × Heap) :=
  if native.size > Heap.maxArrayLength then .error (.tooLong native.size)
  else
    match encodeValues elementCodec native.toList 0 heap #[] with
    | .error fault => .error fault
    | .ok (values, encodedHeap) =>
        match encodedHeap.allocateArrayFromArray (values.map some) none with
        | .error fault => .error (.allocation fault)
        | .ok (root, next) => .ok (.object root, next)

private def decodeValues (elementCodec : Codec α ElementEncodeFault ElementDecodeFault element)
    (heap : Heap) (source : List Value) (index : Nat) (values : _root_.Array α) :
    Except (DecodeFault ElementDecodeFault) (_root_.Array α) :=
  match source with
  | [] => .ok values
  | value :: rest =>
      match elementCodec.decode heap value with
      | .error fault => .error (.element index fault)
      | .ok native => decodeValues elementCodec heap rest (index + 1) (values.push native)

/-- Decodes only an exact dense shape, then decodes elements in index order. -/
def decode (elementCodec : Codec α ElementEncodeFault ElementDecodeFault element)
    (heap : Heap) (value : Value) :
    Except (DecodeFault ElementDecodeFault) (_root_.Array α) :=
  match inspectDense heap value with
  | .error fault => .error (.shape fault)
  | .ok (_, values) => decodeValues elementCodec heap values.toList 0 #[]

private theorem decodeValues_sound
    (elementCodec : Codec α ElementEncodeFault ElementDecodeFault element) (heap : Heap) :
    ∀ (source : List Value) (index : Nat) (accumulated result : _root_.Array α),
      decodeValues elementCodec heap source index accumulated = .ok result →
      result.size = accumulated.size + source.length ∧
      (∀ position, position < accumulated.size → result[position]? = accumulated[position]?) ∧
      ∀ (position : Nat) (inBounds : position < source.length), ∃ native,
        result[accumulated.size + position]? = some native ∧
        elementCodec.decode heap source[position] = .ok native
  | [], index, accumulated, result, decoded => by
      simp only [decodeValues, Except.ok.injEq] at decoded
      subst decoded
      exact ⟨by simp, fun position _ => rfl, fun position inBounds => by simp at inBounds⟩
  | value :: rest, index, accumulated, result, decoded => by
      unfold decodeValues at decoded
      split at decoded
      · exact absurd decoded (by simp)
      · rename_i native elementDecoded
        obtain ⟨size, prefixEq, elements⟩ :=
          decodeValues_sound elementCodec heap rest (index + 1) (accumulated.push native) result
            decoded
        have pushSize : (accumulated.push native).size = accumulated.size + 1 := by simp
        refine ⟨by simp [size, pushSize]; omega, ?_, ?_⟩
        · intro position inRange
          rw [prefixEq position (by omega), Array.getElem?_push]
          simp [Nat.ne_of_lt inRange]
        · intro position inBounds
          match position with
          | 0 =>
              refine ⟨native, ?_, by simpa using elementDecoded⟩
              rw [Nat.add_zero, prefixEq accumulated.size (by omega), Array.getElem?_push]
              simp
          | next + 1 =>
              obtain ⟨decodedNative, valueEq, found⟩ :=
                elements next (by simpa using Nat.lt_of_succ_lt_succ inBounds)
              refine ⟨decodedNative, ?_, by simpa using found⟩
              rw [pushSize] at valueEq
              simpa [Nat.add_assoc, Nat.add_comm 1] using valueEq

private theorem decodeValues_complete
    (elementCodec : Codec α ElementEncodeFault ElementDecodeFault element) (heap : Heap) :
    ∀ (source : List Value) (index : Nat) (accumulated : _root_.Array α),
      (∀ value ∈ source, ∃ native, elementCodec.decode heap value = .ok native) →
      ∃ result, decodeValues elementCodec heap source index accumulated = .ok result
  | [], _, accumulated, _ => ⟨accumulated, rfl⟩
  | value :: rest, index, accumulated, decodable => by
      obtain ⟨native, elementDecoded⟩ := decodable value (by simp)
      obtain ⟨result, decoded⟩ :=
        decodeValues_complete elementCodec heap rest (index + 1) (accumulated.push native)
          (fun other member => decodable other (by simp [member]))
      exact ⟨result, by unfold decodeValues; rw [elementDecoded]; exact decoded⟩

/-- Decoding an exact dense array establishes the refinement relation for the decoded elements. -/
theorem decode_sound (elementCodec : Codec α ElementEncodeFault ElementDecodeFault element)
    {heap : Heap} {value : Value} {native : _root_.Array α}
    (decoded : decode elementCodec heap value = .ok native) :
    DenseArrayRel element heap native value := by
  cases inspected : inspectDense heap value with
  | error fault => simp [decode, inspected] at decoded
  | ok result =>
      obtain ⟨root, values⟩ := result
      simp only [decode, inspected] at decoded
      obtain ⟨object, slots, valueEq, found, kindEq, prototypeEq, extensibleEq, writableEq, sizeEq,
        keysEq, elements⟩ := inspectDense_sound inspected
      obtain ⟨size, _, decodedElements⟩ :=
        decodeValues_sound elementCodec heap values.toList 0 #[] native decoded
      have nativeSize : native.size = values.size := by simpa using size
      refine ⟨root, object, slots, valueEq, found, kindEq, prototypeEq, extensibleEq,
        by rw [sizeEq, nativeSize], writableEq, by rw [keysEq, nativeSize], ?_⟩
      intro index inBounds
      have indexBound : index < values.size := by omega
      obtain ⟨encoded, valueAt, elementFound⟩ := elements index indexBound
      obtain ⟨decodedNative, nativeAt, elementDecoded⟩ := decodedElements index (by simpa using indexBound)
      have valueAtIndex : values[index] = encoded := by
        rw [Array.getElem?_eq_getElem indexBound] at valueAt
        exact Option.some.inj valueAt
      have nativeAtIndex : native[index] = decodedNative := by
        rw [show (#[] : _root_.Array α).size = 0 from rfl, Nat.zero_add,
          Array.getElem?_eq_getElem inBounds] at nativeAt
        exact Option.some.inj nativeAt
      refine ⟨encoded, elementFound, ?_⟩
      rw [nativeAtIndex]
      exact elementCodec.decode_sound (by simpa [valueAtIndex] using elementDecoded)

/-- Sequential element encoding threads one exact extension through the whole element list: the
final heap extends the initial one and every element already encoded stays related in it. -/
private theorem encodeValues_sound
    (elementCodec : Codec α ElementEncodeFault ElementDecodeFault element) :
    ∀ (source : List α) (index : Nat) (heap : Heap) (accumulated values : _root_.Array Value)
      (next : Heap), heap.WellFormed →
      encodeValues elementCodec source index heap accumulated = .ok (values, next) →
      Heap.ExactExtension heap next ∧
      values.size = accumulated.size + source.length ∧
      (∀ position, position < accumulated.size → values[position]? = accumulated[position]?) ∧
      ∀ (position : Nat) (inBounds : position < source.length), ∃ encoded,
        values[accumulated.size + position]? = some encoded ∧
        element.Rel next source[position] encoded
  | [], index, heap, accumulated, values, next, valid, encoded => by
      simp only [encodeValues, Except.ok.injEq, Prod.mk.injEq] at encoded
      obtain ⟨valuesEq, nextEq⟩ := encoded
      subst valuesEq
      subst nextEq
      exact ⟨Heap.ExactExtension.refl heap valid, by simp, fun position _ => rfl,
        fun position inBounds => by simp at inBounds⟩
  | native :: rest, index, heap, accumulated, values, next, valid, encoded => by
      unfold encodeValues at encoded
      split at encoded
      · exact absurd encoded (by simp)
      · rename_i value middle elementEncoded
        obtain ⟨firstExtension, firstRelated⟩ := elementCodec.encode_sound valid elementEncoded
        obtain ⟨extension, size, prefixEq, elements⟩ :=
          encodeValues_sound elementCodec rest (index + 1) middle (accumulated.push value) values
            next firstExtension.nextWellFormed encoded
        have pushSize : (accumulated.push value).size = accumulated.size + 1 := by simp
        refine ⟨firstExtension.trans extension, by simp [size, pushSize]; omega, ?_, ?_⟩
        · intro position inRange
          rw [prefixEq position (by omega), Array.getElem?_push]
          simp [Nat.ne_of_lt inRange]
        · intro position inBounds
          match position with
          | 0 =>
              refine ⟨value, ?_, by simpa using element.stable extension firstRelated⟩
              rw [Nat.add_zero, prefixEq accumulated.size (by omega), Array.getElem?_push]
              simp
          | shifted + 1 =>
              obtain ⟨encodedValue, valueEq, related⟩ :=
                elements shifted (by simpa using Nat.lt_of_succ_lt_succ inBounds)
              refine ⟨encodedValue, ?_, by simpa using related⟩
              rw [pushSize] at valueEq
              simpa [Nat.add_assoc, Nat.add_comm 1] using valueEq

/-- A lawful element codec encodes every element list from a well-formed heap. -/
private theorem encodeValues_total
    {elementCodec : Codec α ElementEncodeFault ElementDecodeFault element}
    (elementLawful : LawfulCodec elementCodec) :
    ∀ (source : List α) (index : Nat) (heap : Heap) (accumulated : _root_.Array Value),
      heap.WellFormed →
      ∃ values next, encodeValues elementCodec source index heap accumulated = .ok (values, next)
  | [], _, heap, accumulated, _ => ⟨accumulated, heap, rfl⟩
  | native :: rest, index, heap, accumulated, valid => by
      obtain ⟨value, middle, elementEncoded⟩ := elementLawful.encode_total heap native valid
      obtain ⟨extension, _⟩ := elementCodec.encode_sound valid elementEncoded
      obtain ⟨values, next, encoded⟩ :=
        encodeValues_total elementLawful rest (index + 1) middle (accumulated.push value)
          extension.nextWellFormed
      exact ⟨values, next, by unfold encodeValues; rw [elementEncoded]; exact encoded⟩

/-- Encoding extends the heap exactly and relates the fresh array to the encoded Lean array. -/
theorem encode_sound (elementCodec : Codec α ElementEncodeFault ElementDecodeFault element)
    {old : Heap} {native : _root_.Array α} {value : Value} {next : Heap} (valid : old.WellFormed)
    (encoded : encode elementCodec old native = .ok (value, next)) :
    Heap.ExactExtension old next ∧ DenseArrayRel element next native value := by
  unfold encode at encoded
  split at encoded
  · exact absurd encoded (by simp)
  · split at encoded
    · exact absurd encoded (by simp)
    · rename_i values encodedHeap sequenced
      split at encoded
      · exact absurd encoded (by simp)
      · rename_i root allocatedHeap allocated
        simp only [Except.ok.injEq, Prod.mk.injEq] at encoded
        obtain ⟨valueEq, nextEq⟩ := encoded
        subst valueEq
        subst nextEq
        obtain ⟨sequencedExtension, size, _, elements⟩ :=
          encodeValues_sound elementCodec native.toList 0 old #[] values encodedHeap valid sequenced
        have allocationExtension := Heap.allocateArrayFromArray_exactExtension encodedHeap
          allocatedHeap (values.map some) none root sequencedExtension.nextWellFormed allocated
        obtain ⟨⟨object, found, prototypeEq, extensibleEq, kindEq⟩, keys, descriptors⟩ :=
          Heap.allocateArrayFromArray_dense encodedHeap allocatedHeap values none root allocated
        have valuesSize : values.size = native.size := by simpa using size
        refine ⟨sequencedExtension.trans allocationExtension,
          root, object, ⟨values.size, true⟩, rfl, found, kindEq, prototypeEq, extensibleEq,
          valuesSize, rfl, ?_, ?_⟩
        · rw [keys, denseKeys_eq_range, valuesSize]
          rfl
        · intro index inBounds
          have indexBound : index < values.size := by omega
          obtain ⟨encodedValue, valueAt, related⟩ := elements index (by simpa using inBounds)
          have valueAtIndex : values[index] = encodedValue := by
            rw [show (#[] : _root_.Array Value).size = 0 from rfl, Nat.zero_add,
              Array.getElem?_eq_getElem indexBound] at valueAt
            exact Option.some.inj valueAt
          refine ⟨values[index], descriptors index indexBound, ?_⟩
          rw [valueAtIndex]
          exact element.stable allocationExtension related

/-- Every related dense array decodes back to exactly its Lean array. The hypothesis is the element
codec's completeness alone, never its totality, so this composes into arrays of arrays. -/
theorem decode_complete {elementCodec : Codec α ElementEncodeFault ElementDecodeFault element}
    (elementComplete : elementCodec.Complete) {heap : Heap} {native : _root_.Array α}
    {value : Value} (related : DenseArrayRel element heap native value) :
    decode elementCodec heap value = .ok native := by
  obtain ⟨root, values, inspected⟩ := inspectDense_complete (DenseArrayRel.denseShape related)
  obtain ⟨_, _, valueEq, _, _, _, _, _, _, keysEq, elements⟩ := inspectDense_sound inspected
  obtain ⟨relatedRoot, _, _, relatedValueEq, _, _, _, _, _, _, relatedKeys, relatedElements⟩ :=
    id related
  have rootEq : relatedRoot = root := by
    rw [relatedValueEq] at valueEq
    exact Value.object.inj valueEq
  subst rootEq
  have sizeEq : values.size = native.size :=
    denseKeys_injective (Except.ok.inj (keysEq.symm.trans relatedKeys))
  obtain ⟨result, decoded⟩ :=
    decodeValues_complete elementCodec heap values.toList 0 #[] (by
      intro encoded member
      obtain ⟨index, inBounds, indexEq⟩ := List.getElem_of_mem member
      have indexBound : index < values.size := by simpa using inBounds
      obtain ⟨inspectedEncoded, valueAt, elementFound⟩ := elements index indexBound
      obtain ⟨relatedEncoded, relatedFound, relatedRel⟩ := relatedElements index (by omega)
      rw [elementFound] at relatedFound
      have encodedEq : inspectedEncoded = relatedEncoded := by
        have descriptorsEqual :=
          PropertyDescriptor.data.inj (Option.some.inj (Except.ok.inj relatedFound))
        cases descriptorsEqual
        rfl
      have valueAtIndex : values[index] = inspectedEncoded := by
        rw [Array.getElem?_eq_getElem indexBound] at valueAt
        exact Option.some.inj valueAt
      refine ⟨native[index]'(by omega), ?_⟩
      rw [← indexEq]
      simpa [valueAtIndex, encodedEq] using elementComplete relatedRel)
  have decodeEq : decode elementCodec heap value = .ok result := by
    simp only [decode, inspected]
    exact decoded
  rw [decodeEq]
  exact congrArg Except.ok
    (refinement_uniqueDecode elementComplete.uniqueDecode
      (decode_sound elementCodec decodeEq) related)

/-- Dense-snapshot codec: bounded exact-shape validation inbound, one fresh null-prototype array
outbound. Element lawfulness is not needed to build it, nor to prove it sound or complete; only the
totality results (`encode_total`, `codec_roundtrip`) ask for it, and no array codec can supply it
(`not_lawful`), so those two do not compose into arrays of arrays without a per-element bound. -/
def codec (elementCodec : Codec α ElementEncodeFault ElementDecodeFault element) :
    Codec (_root_.Array α) (EncodeFault ElementEncodeFault) (DecodeFault ElementDecodeFault)
      (refinement element) where
  encode := encode elementCodec
  decode := decode elementCodec
  encode_sound valid encoded := encode_sound elementCodec valid encoded
  decode_sound decoded := decode_sound elementCodec decoded

/-- Encoding succeeds for every array a well-formed heap can represent. This genuinely needs element
totality, so it does not instantiate at an element codec that is itself an array codec: `not_lawful`
refutes the hypothesis there. Nesting needs a bound on every element's encoded size, which this
slice does not carry. -/
theorem encode_total {elementCodec : Codec α ElementEncodeFault ElementDecodeFault element}
    (elementLawful : LawfulCodec elementCodec) (heap : Heap) (native : _root_.Array α)
    (valid : heap.WellFormed) (bound : native.size ≤ Heap.maxArrayLength) :
    ∃ value next, (codec elementCodec).encode heap native = .ok (value, next) := by
  obtain ⟨values, encodedHeap, sequenced⟩ :=
    encodeValues_total elementLawful native.toList 0 heap #[] valid
  obtain ⟨_, size, _, elements⟩ :=
    encodeValues_sound elementCodec native.toList 0 heap #[] values encodedHeap valid sequenced
  have valuesSize : values.size = native.size := by simpa using size
  obtain ⟨root, next, allocated⟩ :=
    Heap.allocateArrayFromArray_ok encodedHeap (values.map some) (by simpa [valuesSize] using bound)
      (by
        simp only [List.all_eq_true]
        intro entry member
        obtain ⟨encodedValue, valueMember, entryEq⟩ : ∃ value, value ∈ values ∧ some value = entry := by
          simpa using member
        obtain ⟨index, inBounds, indexEq⟩ :=
          List.getElem_of_mem ((Array.mem_toList_iff encodedValue values).mpr valueMember)
        have indexBound : index < values.size := by simpa using inBounds
        obtain ⟨related, valueAt, relation⟩ := elements index (by simpa [valuesSize] using indexBound)
        have valueAtIndex : values[index] = related := by
          rw [show (#[] : _root_.Array Value).size = 0 from rfl, Nat.zero_add,
            Array.getElem?_eq_getElem indexBound] at valueAt
          exact Option.some.inj valueAt
        have encodedValueEqRelated : encodedValue = related := by
          calc
            encodedValue = values.toList[index] := indexEq.symm
            _ = values[index] := Array.getElem_toList indexBound
            _ = related := valueAtIndex
        subst entryEq
        rw [encodedValueEqRelated]
        exact element.valueValid relation)
  refine ⟨.object root, next, ?_⟩
  change encode elementCodec heap native = _
  unfold encode
  rw [if_neg (by omega), sequenced]
  simp only
  rw [allocated]

/-- Encoding returns exactly one freshly allocated array root: an object reference that was not
valid in the input heap, carrying the complete dense relation in the extended heap. -/
theorem encode_exact (elementCodec : Codec α ElementEncodeFault ElementDecodeFault element)
    {old : Heap} {native : _root_.Array α} {value : Value} {next : Heap} (valid : old.WellFormed)
    (encoded : encode elementCodec old native = .ok (value, next)) :
    ∃ root, value = .object root ∧ old.valueValid (.object root) = false ∧
      DenseArrayRel element next native (.object root) := by
  obtain ⟨extension, related⟩ := encode_sound elementCodec valid encoded
  unfold encode at encoded
  split at encoded
  · exact absurd encoded (by simp)
  · split at encoded
    · exact absurd encoded (by simp)
    · rename_i values encodedHeap sequenced
      split at encoded
      · exact absurd encoded (by simp)
      · rename_i root allocatedHeap allocated
        simp only [Except.ok.injEq, Prod.mk.injEq] at encoded
        obtain ⟨valueEq, nextEq⟩ := encoded
        subst valueEq
        subst nextEq
        obtain ⟨sequencedExtension, _, _, _⟩ :=
          encodeValues_sound elementCodec native.toList 0 old #[] values encodedHeap valid sequenced
        obtain ⟨freshIndex, _⟩ := Heap.allocateArray_result_fresh_kind encodedHeap allocatedHeap
          (values.map some).toList none root
          (by simpa [Heap.allocateArray, ← Array.toList_map] using allocated)
        refine ⟨root, rfl, ?_, related⟩
        have sizeLe := sequencedExtension.size_le
        simp only [Heap.valueValid, decide_eq_false_iff_not, Nat.not_lt]
        omega

/-- The encode boundary: an array the heap cannot represent is rejected on its length alone, before
any element is encoded and before anything is allocated. -/
theorem encode_tooLong (elementCodec : Codec α ElementEncodeFault ElementDecodeFault element)
    (heap : Heap) (native : _root_.Array α) (oversized : native.size > Heap.maxArrayLength) :
    encode elementCodec heap native = .error (.tooLong native.size) := by
  unfold encode
  rw [if_pos oversized]

/-- Array encoding cannot be lawful in the ECMAScript model: Lean arrays are unbounded while an
array's length is not, so totality fails exactly on unrepresentable sizes. -/
theorem not_lawful [Inhabited α]
    (elementCodec : Codec α ElementEncodeFault ElementDecodeFault element) :
    ¬LawfulCodec (codec elementCodec) := by
  intro lawful
  obtain ⟨oversized, oversizedSize⟩ : ∃ oversized : _root_.Array α,
      oversized.size = Heap.maxArrayLength + 1 :=
    ⟨(List.replicate (Heap.maxArrayLength + 1) default).toArray, by simp⟩
  have rejected : (codec elementCodec).encode Heap.empty oversized =
      .error (.tooLong oversized.size) :=
    encode_tooLong elementCodec Heap.empty oversized (by rw [oversizedSize]; omega)
  obtain ⟨value, next, encoded⟩ := lawful.encode_total Heap.empty oversized Heap.empty_wellFormed
  rw [rejected] at encoded
  cases encoded

/-- The array codec is complete: every related dense array decodes back to exactly its Lean array.
This needs only `Codec.Complete` of the element codec, so it holds for arrays of arrays, where the
full `LawfulCodec` hypothesis would be false by `not_lawful` and would make the statement vacuous. -/
theorem codec_complete {elementCodec : Codec α ElementEncodeFault ElementDecodeFault element}
    (elementComplete : elementCodec.Complete) {heap : Heap} {native : _root_.Array α}
    {value : Value} (related : (refinement element).Rel heap native value) :
    (codec elementCodec).decode heap value = .ok native :=
  decode_complete elementComplete related

/-- Decoding accepts exactly the values the refinement relates to the decoded array. Element
completeness is the only hypothesis, so this also holds for arrays of arrays. -/
theorem decode_exact {elementCodec : Codec α ElementEncodeFault ElementDecodeFault element}
    (elementComplete : elementCodec.Complete) (heap : Heap) (value : Value)
    (native : _root_.Array α) :
    (codec elementCodec).decode heap value = .ok native ↔
      (refinement element).Rel heap native value :=
  ⟨decode_sound elementCodec, decode_complete elementComplete⟩

/-- Full composition: a representable array encodes to a fresh dense array in an exactly extended
heap, and decoding that exact pair returns the original Lean array. Inherits `encode_total`'s element
totality hypothesis, so like it this does not instantiate for arrays of arrays. -/
theorem codec_roundtrip {elementCodec : Codec α ElementEncodeFault ElementDecodeFault element}
    (elementLawful : LawfulCodec elementCodec) (heap : Heap) (native : _root_.Array α)
    (valid : heap.WellFormed) (bound : native.size ≤ Heap.maxArrayLength) :
    ∃ value next,
      (codec elementCodec).encode heap native = .ok (value, next) ∧
      Heap.ExactExtension heap next ∧
      (refinement element).Rel next native value ∧
      (codec elementCodec).decode next value = .ok native := by
  obtain ⟨value, next, encoded⟩ := encode_total elementLawful heap native valid bound
  obtain ⟨extension, related⟩ := (codec elementCodec).encode_sound valid encoded
  exact ⟨value, next, encoded, extension, related, codec_complete elementLawful.complete related⟩

/-- Decoding rejects every primitive with the object-domain shape fault. -/
theorem decode_primitive (elementCodec : Codec α ElementEncodeFault ElementDecodeFault element)
    (heap : Heap) (primitive : JS.Primitive) :
    (codec elementCodec).decode heap (.primitive primitive) = .error (.shape .expectedObject) := rfl

/-- Decoding rejects dangling object references with the exact reference that failed. -/
theorem decode_invalidRef (elementCodec : Codec α ElementEncodeFault ElementDecodeFault element)
    (heap : Heap) (ref : RefId) (fault : HeapFault) (missing : heap.get? ref = .error fault) :
    (codec elementCodec).decode heap (.object ref) = .error (.shape (.invalidRef ref)) := by
  change decode elementCodec heap (.object ref) = _
  simp [decode, inspectDense, Bind.bind, Except.bind, Pure.pure, Except.pure, missing]

/-- Decoding rejects references to objects of any other kind with their exact kind tag. -/
theorem decode_wrongKind (elementCodec : Codec α ElementEncodeFault ElementDecodeFault element)
    (heap : Heap) (ref : RefId) (object : ObjectRecord) (found : heap.get? ref = .ok object)
    (notArray : ∀ slots, object.kind ≠ .array slots) :
    (codec elementCodec).decode heap (.object ref) =
      .error (.shape (.wrongKind object.kind.tag)) := by
  change decode elementCodec heap (.object ref) = _
  cases kindEq : object.kind with
  | array slots => exact absurd kindEq (notArray slots)
  | ordinary => simp [decode, inspectDense, Bind.bind, Except.bind, Pure.pure, Except.pure,
      found, kindEq]
  | function slots => simp [decode, inspectDense, Bind.bind, Except.bind, Pure.pure, Except.pure,
      found, kindEq]
  | arrayIterator slots => simp [decode, inspectDense, Bind.bind, Except.bind, Pure.pure,
      Except.pure, found, kindEq]
  | primitiveWrapper slots => simp [decode, inspectDense, Bind.bind, Except.bind, Pure.pure,
      Except.pure, found, kindEq]

end Array

end TSLean.Refinement
