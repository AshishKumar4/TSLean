import TSLean.Refinement

namespace TSLean.Refinement.Tests

open TSLean.JS

namespace ArrayContracts

open TSLean.Refinement.Array

universe u v w

/-- Typed statement of every theorem registered under `TSLean.Refinement.Array.` in
`scripts/refinement-proof-registry.mjs`, in registry order, plus the `Codec.Complete.uniqueDecode`
lemma this slice depends on. Each conjunct spells out the proposition the registry demands, so
weakening any registered statement stops this from compiling: the named theorem no longer inhabits
its conjunct. -/
theorem array_contract_inventory {α : Type u} {ElementEncodeFault : Type v}
    {ElementDecodeFault : Type w} [Inhabited α] {element : Refinement α}
    (elementCodec : Codec α ElementEncodeFault ElementDecodeFault element) :
    -- DenseArrayRel.denseShape
    (∀ (heap : Heap) (native : _root_.Array α) (value : Value),
      DenseArrayRel element heap native value → DenseShape heap value) ∧
    -- DenseArrayRel.element_valueValid
    (∀ (heap : Heap) (native : _root_.Array α) (value : Value) (index : Nat),
      DenseArrayRel element heap native value → index < native.size →
      ∃ root encoded, value = .object root ∧
        heap.getOwnProperty root (indexKey index) =
          .ok (some (.data ⟨encoded, true, true, true⟩)) ∧
        heap.valueValid encoded = true) ∧
    -- DenseArrayRel.root_valueValid
    (∀ (heap : Heap) (native : _root_.Array α) (value : Value),
      DenseArrayRel element heap native value → heap.valueValid value = true) ∧
    -- DenseArrayRel.stable
    (∀ (old next : Heap) (native : _root_.Array α) (value : Value),
      Refinement.Heap.ExactExtension old next → DenseArrayRel element old native value →
      DenseArrayRel element next native value) ∧
    -- codec_complete (element completeness only, so arrays of arrays compose)
    (elementCodec.Complete → ∀ (heap : Heap) (native : _root_.Array α) (value : Value),
      (refinement element).Rel heap native value →
      (codec elementCodec).decode heap value = .ok native) ∧
    -- codec_roundtrip (element totality, so arrays of arrays do not compose)
    (LawfulCodec elementCodec → ∀ (heap : Heap) (native : _root_.Array α), heap.WellFormed →
      native.size ≤ Heap.maxArrayLength →
      ∃ value next,
        (codec elementCodec).encode heap native = .ok (value, next) ∧
        Refinement.Heap.ExactExtension heap next ∧
        (refinement element).Rel next native value ∧
        (codec elementCodec).decode next value = .ok native) ∧
    -- decode_complete (element completeness only)
    (elementCodec.Complete → ∀ (heap : Heap) (native : _root_.Array α) (value : Value),
      DenseArrayRel element heap native value → decode elementCodec heap value = .ok native) ∧
    -- decode_exact (element completeness only)
    (elementCodec.Complete → ∀ (heap : Heap) (value : Value) (native : _root_.Array α),
      (codec elementCodec).decode heap value = .ok native ↔
        (refinement element).Rel heap native value) ∧
    -- decode_invalidRef
    (∀ (heap : Heap) (ref : RefId) (fault : HeapFault), heap.get? ref = .error fault →
      (codec elementCodec).decode heap (.object ref) = .error (.shape (.invalidRef ref))) ∧
    -- decode_primitive
    (∀ (heap : Heap) (primitive : JS.Primitive),
      (codec elementCodec).decode heap (.primitive primitive) = .error (.shape .expectedObject)) ∧
    -- decode_sound
    (∀ (heap : Heap) (value : Value) (native : _root_.Array α),
      decode elementCodec heap value = .ok native → DenseArrayRel element heap native value) ∧
    -- decode_wrongKind
    (∀ (heap : Heap) (ref : RefId) (object : ObjectRecord), heap.get? ref = .ok object →
      (∀ slots, object.kind ≠ .array slots) →
      (codec elementCodec).decode heap (.object ref) =
        .error (.shape (.wrongKind object.kind.tag))) ∧
    -- denseKeys_eq_range
    (∀ length : Nat,
      denseKeys length = (List.range length).map indexKey ++ [Heap.lengthPropertyKey]) ∧
    -- denseKeys_injective
    (∀ left right : Nat, denseKeys left = denseKeys right → left = right) ∧
    -- denseShapeGuard_complete
    (∀ (heap : Heap) (value : Value), DenseShape heap value →
      (denseShapeGuard heap).check value = true) ∧
    -- denseShapeGuard_sound
    (∀ (heap : Heap) (value : Value), (denseShapeGuard heap).check value = true →
      DenseShape heap value) ∧
    -- Codec.Complete.uniqueDecode (lives in Core; the decode side of this slice depends on it)
    (elementCodec.Complete → element.UniqueDecode) ∧
    -- encode_exact
    (∀ (old : Heap) (native : _root_.Array α) (value : Value) (next : Heap), old.WellFormed →
      encode elementCodec old native = .ok (value, next) →
      ∃ root, value = .object root ∧ old.valueValid (.object root) = false ∧
        DenseArrayRel element next native (.object root)) ∧
    -- encode_sound
    (∀ (old : Heap) (native : _root_.Array α) (value : Value) (next : Heap), old.WellFormed →
      encode elementCodec old native = .ok (value, next) →
      Refinement.Heap.ExactExtension old next ∧ DenseArrayRel element next native value) ∧
    -- encode_tooLong
    (∀ (heap : Heap) (native : _root_.Array α), native.size > Heap.maxArrayLength →
      encode elementCodec heap native = .error (.tooLong native.size)) ∧
    -- encode_total (element totality, so arrays of arrays do not compose)
    (LawfulCodec elementCodec → ∀ (heap : Heap) (native : _root_.Array α), heap.WellFormed →
      native.size ≤ Heap.maxArrayLength →
      ∃ value next, (codec elementCodec).encode heap native = .ok (value, next)) ∧
    -- fresh_root_distinct
    (∀ (old next : Heap) (elements : List (Option Value)) (prototype : Option RefId)
      (fresh previous : RefId), old.allocateArray elements prototype = .ok (fresh, next) →
      old.valueValid (.object previous) = true → fresh ≠ previous) ∧
    -- getOwnProperty_commutes
    (∀ (heap : Heap) (native : _root_.Array α) (value : Value) (index : Nat),
      DenseArrayRel element heap native value → ∀ inBounds : index < native.size,
      ∃ root encoded, value = .object root ∧
        heap.getOwnProperty root (indexKey index) =
          .ok (some (.data ⟨encoded, true, true, true⟩)) ∧
        element.Rel heap native[index] encoded) ∧
    -- inspectDense_complete
    (∀ (heap : Heap) (value : Value), DenseShape heap value →
      ∃ root values, inspectDense heap value = .ok (root, values)) ∧
    -- inspectDense_sound
    (∀ (heap : Heap) (value : Value) (root : RefId) (values : _root_.Array Value),
      inspectDense heap value = .ok (root, values) →
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
            .ok (some (.data ⟨encoded, true, true, true⟩))) ∧
    -- length_commutes
    (∀ (heap : Heap) (native : _root_.Array α) (value : Value),
      DenseArrayRel element heap native value →
      ∃ root, value = .object root ∧ heap.arrayLength root = .ok native.size) ∧
    -- matchesDenseKeys_iff
    (∀ (length : Nat) (keys : List PropertyKey),
      matchesDenseKeys length keys = true ↔ keys = denseKeys length) ∧
    -- not_lawful
    (¬LawfulCodec (codec elementCodec)) ∧
    -- refinement_uniqueDecode
    (element.UniqueDecode → (refinement element).UniqueDecode) :=
  ⟨fun _ _ _ related => DenseArrayRel.denseShape related,
    fun _ _ _ index related inBounds => DenseArrayRel.element_valueValid related index inBounds,
    fun _ _ _ related => DenseArrayRel.root_valueValid related,
    fun _ _ _ _ extension related => DenseArrayRel.stable extension related,
    fun elementComplete _ _ _ related => codec_complete elementComplete related,
    fun elementLawful heap native valid bound =>
      codec_roundtrip elementLawful heap native valid bound,
    fun elementComplete _ _ _ related => decode_complete elementComplete related,
    fun elementComplete heap value native => decode_exact elementComplete heap value native,
    fun heap ref fault missing => decode_invalidRef elementCodec heap ref fault missing,
    fun heap primitive => decode_primitive elementCodec heap primitive,
    fun _ _ _ decoded => decode_sound elementCodec decoded,
    fun heap ref object found notArray =>
      decode_wrongKind elementCodec heap ref object found notArray,
    denseKeys_eq_range,
    fun _ _ equal => denseKeys_injective equal,
    fun heap value shape => denseShapeGuard_complete heap value shape,
    fun heap value accepted => denseShapeGuard_sound heap value accepted,
    fun elementComplete => elementComplete.uniqueDecode,
    fun _ _ _ _ valid encoded => encode_exact elementCodec valid encoded,
    fun _ _ _ _ valid encoded => encode_sound elementCodec valid encoded,
    fun heap native oversized => encode_tooLong elementCodec heap native oversized,
    fun elementLawful heap native valid bound => encode_total elementLawful heap native valid bound,
    fun old next elements prototype fresh previous allocated previousValid =>
      fresh_root_distinct old next elements prototype fresh previous allocated previousValid,
    fun _ _ _ index related inBounds => getOwnProperty_commutes related index inBounds,
    fun _ _ shape => inspectDense_complete shape,
    fun _ _ _ _ inspected => inspectDense_sound inspected,
    fun _ _ _ related => length_commutes related,
    matchesDenseKeys_iff,
    not_lawful elementCodec,
    fun unique => refinement_uniqueDecode unique⟩

/-- Every premise of the array codec contracts is jointly satisfiable: one encode against the
committed Boolean codec discharges heap well-formedness, the representable-length bound and element
lawfulness at once. Each conjunct below is then produced by applying one registered theorem to that
instance, covering twelve of them; the remaining registered statements are pinned by
`array_contract_inventory` and by the executable assertions further down this file. -/
theorem array_codec_contract_witness :
    ∃ value next root,
      (codec Bool.codec).encode Heap.empty #[true, false] = .ok (value, next) ∧
      Refinement.Heap.ExactExtension Heap.empty next ∧
      (refinement Bool.refinement).Rel next #[true, false] value ∧
      (codec Bool.codec).decode next value = .ok #[true, false] ∧
      value = .object root ∧
      Heap.empty.valueValid (.object root) = false ∧
      next.valueValid value = true ∧
      next.arrayLength root = .ok 2 ∧
      DenseShape next value ∧
      (denseShapeGuard next).check value = true ∧
      (∃ encoded, next.getOwnProperty root (indexKey 0) =
          .ok (some (.data ⟨encoded, true, true, true⟩)) ∧
        Bool.refinement.Rel next true encoded ∧ next.valueValid encoded = true) ∧
      (∃ values, inspectDense next value = .ok (root, values) ∧
        next.ownPropertyKeys root = .ok (denseKeys values.size)) := by
  obtain ⟨value, next, encoded, extension, related, decoded⟩ :=
    codec_roundtrip Bool.codec_lawful Heap.empty #[true, false] Heap.empty_wellFormed
      (by simp [Heap.maxArrayLength])
  obtain ⟨root, valueEq, fresh, _⟩ :=
    encode_exact (native := #[true, false]) (value := value) (next := next) Bool.codec
      Heap.empty_wellFormed encoded
  obtain ⟨lengthRoot, lengthValueEq, lengthEq⟩ := length_commutes related
  obtain ⟨elementRoot, elementEncoded, elementValueEq, elementFound, elementRelated⟩ :=
    getOwnProperty_commutes related 0 (by decide)
  obtain ⟨validRoot, validEncoded, validValueEq, validFound, validValid⟩ :=
    DenseArrayRel.element_valueValid related 0 (by decide)
  have shape := DenseArrayRel.denseShape related
  have accepted := denseShapeGuard_complete next value shape
  obtain ⟨inspectedRoot, values, inspected⟩ :=
    inspectDense_complete (denseShapeGuard_sound next value accepted)
  obtain ⟨_, _, inspectedValueEq, _, _, _, _, _, _, keys, _⟩ := inspectDense_sound inspected
  have rootOf : ∀ other : RefId, value = .object other → other = root := by
    intro other otherEq
    rw [valueEq] at otherEq
    exact (Value.object.inj otherEq).symm
  rw [rootOf lengthRoot lengthValueEq] at lengthEq
  rw [rootOf elementRoot elementValueEq] at elementFound
  rw [rootOf validRoot validValueEq] at validFound
  rw [rootOf inspectedRoot inspectedValueEq] at inspected keys
  refine ⟨value, next, root, encoded, extension, related,
    (decode_exact Bool.codec_lawful.complete next value #[true, false]).mpr related,
    valueEq, fresh, DenseArrayRel.root_valueValid related, by simpa using lengthEq, shape,
    accepted, ⟨elementEncoded, elementFound, elementRelated, ?_⟩, values, inspected, keys⟩
  rw [elementFound] at validFound
  have descriptorsEqual := PropertyDescriptor.data.inj (Option.some.inj (Except.ok.inj validFound))
  cases descriptorsEqual
  exact validValid

/-- The decode side composes into arrays of arrays. The inner array codec supplies `Codec.Complete`
even though `not_lawful` refutes `LawfulCodec` for it, so none of these four conjuncts is vacuous:
the hypothesis discharged here is a theorem of this slice, not an assumption that cannot hold. -/
theorem nested_array_contract :
    (codec Bool.codec).Complete ∧
    (refinement Bool.refinement).UniqueDecode ∧
    (∀ {heap : Heap} {native : _root_.Array (_root_.Array Bool)} {value : Value},
      (refinement (refinement Bool.refinement)).Rel heap native value →
      (codec (codec Bool.codec)).decode heap value = .ok native) ∧
    ∀ (heap : Heap) (value : Value) (native : _root_.Array (_root_.Array Bool)),
      (codec (codec Bool.codec)).decode heap value = .ok native ↔
        (refinement (refinement Bool.refinement)).Rel heap native value :=
  ⟨codec_complete Bool.codec_lawful.complete,
    Codec.Complete.uniqueDecode (codec_complete Bool.codec_lawful.complete),
    codec_complete (codec_complete Bool.codec_lawful.complete),
    decode_exact (codec_complete Bool.codec_lawful.complete)⟩

/-- The array codec is not lawful, and the witness is a length no ECMAScript array can hold. -/
theorem array_codec_not_lawful : ¬LawfulCodec (codec Bool.codec) := not_lawful Bool.codec

/-- The empty heap witnesses the dangling-reference premise. -/
theorem array_decode_rejects_dangling :
    (codec Bool.codec).decode Heap.empty (.object ⟨0⟩) = .error (.shape (.invalidRef ⟨0⟩)) :=
  decode_invalidRef Bool.codec Heap.empty ⟨0⟩ (.invalidRef ⟨0⟩) rfl

/-- Primitives are rejected in the object domain, whatever the heap. -/
theorem array_decode_rejects_primitive (heap : Heap) (primitive : JS.Primitive) :
    (codec Bool.codec).decode heap (.primitive primitive) = .error (.shape .expectedObject) :=
  decode_primitive Bool.codec heap primitive

/-- An array iterator witnesses the wrong-kind premise with a genuinely allocated object. -/
theorem array_decode_rejects_wrong_kind (heap next : Heap) (target iterator : RefId)
    (allocated : heap.allocateArrayIterator target none = .ok (iterator, next)) :
    ∃ tag, (codec Bool.codec).decode next (.object iterator) = .error (.shape (.wrongKind tag)) := by
  obtain ⟨_, kindEq⟩ :=
    Heap.allocateArrayIterator_result_fresh_kind heap next target none iterator allocated
  unfold Heap.objectKind? at kindEq
  cases found : next.get? iterator with
  | error fault => rw [found] at kindEq; simp at kindEq
  | ok object =>
      rw [found] at kindEq
      simp only [Option.some.injEq] at kindEq
      exact ⟨object.kind.tag, decode_wrongKind Bool.codec next iterator object found
        (by rw [kindEq]; intro slots; simp)⟩

end ArrayContracts

private def check (label : String) (condition : Bool) : IO Unit :=
  if condition then pure () else throw (IO.userError s!"array refinement regression: {label}")

private def orFail (label : String) : Except ε β → IO β
  | .ok value => pure value
  | .error _ => throw (IO.userError s!"array fixture failed: {label}")

private def allocateOrFail (label : String) (elements : List (Option Value))
    (prototype : Option RefId := none) (heap : Heap := Heap.empty) : IO (RefId × Heap) :=
  orFail label (heap.allocateArray elements prototype)

private def defineOrFail (label : String) (heap : Heap) (root : RefId) (key : PropertyKey)
    (update : DescriptorUpdate) : IO Heap := do
  match ← orFail label (heap.defineOwnProperty root key update) with
  | (true, next) => pure next
  | (false, _) => throw (IO.userError s!"array fixture rejected: {label}")

private def createOrFail (label : String) (heap : Heap) (root : RefId) (key : PropertyKey)
    (value : Value) : IO Heap := do
  match ← orFail label (heap.createDataProperty root key value) with
  | (true, next) => pure next
  | (false, _) => throw (IO.userError s!"array fixture rejected: {label}")

/-- Compares a shape inspection against the exact expected element list or the exact typed fault. -/
private def shapeIs (heap : Heap) (value : Value)
    (expected : Except Array.ShapeFault (List Value)) : Bool :=
  match (Array.inspectDense heap value).map (fun result => result.2.toList), expected with
  | .ok actual, .ok wanted => decide (actual = wanted)
  | .error actual, .error wanted => decide (actual = wanted)
  | _, _ => false

private def checkShape (label : String) (heap : Heap) (value : Value)
    (expected : Except Array.ShapeFault (List Value)) : IO Unit :=
  check label (shapeIs heap value expected)

/-- Compares an array decode against the exact expected elements or the exact typed fault. -/
private def decodeIs {α : Type} [DecidableEq α] {ElementEncodeFault ElementDecodeFault : Type}
    [DecidableEq ElementDecodeFault] {element : Refinement α}
    (elementCodec : Codec α ElementEncodeFault ElementDecodeFault element) (heap : Heap)
    (value : Value) (expected : Except (Array.DecodeFault ElementDecodeFault) (List α)) : Bool :=
  match (Array.decode elementCodec heap value).map (·.toList), expected with
  | .ok actual, .ok wanted => decide (actual = wanted)
  | .error actual, .error wanted => decide (actual = wanted)
  | _, _ => false

private def checkDecode {α : Type} [DecidableEq α] {ElementEncodeFault ElementDecodeFault : Type}
    [DecidableEq ElementDecodeFault] {element : Refinement α}
    (elementCodec : Codec α ElementEncodeFault ElementDecodeFault element) (label : String)
    (heap : Heap) (value : Value)
    (expected : Except (Array.DecodeFault ElementDecodeFault) (List α)) : IO Unit :=
  check label (decodeIs elementCodec heap value expected)

private def denseTrue : Value := .primitive (.boolean true)
private def denseSeven : Value := .primitive (.bigint 7)

/-- Exact typed fault identity for every reachable rejection of the dense-shape validator. -/
private def testShapeFaultIdentity : IO Unit := do
  let (root, heap) ← allocateOrFail "dense pair" [some denseTrue, some denseSeven]
  let pairKeys : List PropertyKey := [Array.indexKey 0, Array.indexKey 1, Heap.lengthPropertyKey]
  checkShape "dense pair is accepted with its exact elements" heap (.object root)
    (.ok [denseTrue, denseSeven])
  let (emptyRoot, emptyHeap) ← allocateOrFail "empty array" []
  checkShape "empty array is accepted" emptyHeap (.object emptyRoot) (.ok [])

  checkShape "undefined primitive" Heap.empty (.primitive .undefined) (.error .expectedObject)
  checkShape "null primitive" Heap.empty (.primitive .null) (.error .expectedObject)
  checkShape "string primitive" heap (.primitive (.string (JSString.ofLeanString "0")))
    (.error .expectedObject)

  checkShape "dangling reference into the empty heap" Heap.empty (.object ⟨0⟩)
    (.error (.invalidRef ⟨0⟩))
  checkShape "dangling reference past the frontier" heap (.object ⟨7⟩) (.error (.invalidRef ⟨7⟩))

  let (ordinaryRoot, ordinaryHeap) ← orFail "ordinary object" (Heap.empty.allocate none true)
  checkShape "ordinary object" ordinaryHeap (.object ordinaryRoot) (.error (.wrongKind .ordinary))
  let (iteratorRoot, iteratorHeap) ← orFail "array iterator"
    (heap.allocateArrayIterator root none)
  checkShape "array iterator" iteratorHeap (.object iteratorRoot)
    (.error (.wrongKind .arrayIterator))
  let (wrapperRoot, wrapperHeap) ← orFail "primitive wrapper"
    (Heap.empty.allocatePrimitiveWrapper (.boolean true) none)
  checkShape "primitive wrapper" wrapperHeap (.object wrapperRoot)
    (.error (.wrongKind .primitiveWrapper))
  let (functionRoot, functionHeap) ← orFail "function"
    (Heap.empty.allocateFunction ⟨0⟩ .ordinary false none none)
  checkShape "function object" functionHeap (.object functionRoot)
    (.error (.wrongKind .function))

  let (prototypeRoot, prototypeHeap) ← allocateOrFail "prototype array" []
  let (childRoot, childHeap) ←
    allocateOrFail "array with a prototype" [some denseTrue] (some prototypeRoot) prototypeHeap
  checkShape "wrong prototype" childHeap (.object childRoot)
    (.error (.wrongPrototype prototypeRoot))
  -- An inherited index is unexhibitable: the refinement fixes the prototype at `none`, so the
  -- prototype check rejects before any index is read. This pins that ordering instead of asserting
  -- an inherited-index fault that cannot occur.
  let prototypeWithIndex ← createOrFail "inherited index" prototypeHeap prototypeRoot
    (Array.indexKey 0) denseTrue
  let (inheritedRoot, inheritedHeap) ←
    allocateOrFail "array inheriting an index" [none] (some prototypeRoot) prototypeWithIndex
  checkShape "inherited index is masked by the prototype fault" inheritedHeap (.object inheritedRoot)
    (.error (.wrongPrototype prototypeRoot))

  let frozen ← orFail "preventExtensions" (heap.preventExtensions root)
  checkShape "non-extensible array" frozen (.object root) (.error .notExtensible)

  let readonlyLength ← defineOrFail "non-writable length" heap root Heap.lengthPropertyKey
    { writable := .present false }
  checkShape "non-writable length" readonlyLength (.object root) (.error .nonWritableLength)

  let (holeRoot, holeHeap) ← allocateOrFail "array with a hole"
    [some (.primitive .undefined), none]
  checkShape "hole" holeHeap (.object holeRoot)
    (.error (.unexpectedKeys [Array.indexKey 0, Heap.lengthPropertyKey]))

  let extraKey ← createOrFail "extra string key" heap root
    (.string (JSString.ofLeanString "extra")) denseTrue
  checkShape "extra string key" extraKey (.object root)
    (.error (.unexpectedKeys (pairKeys ++ [.string (JSString.ofLeanString "extra")])))

  let symbolKey ← createOrFail "symbol key" heap root (.symbol (.allocated 0)) denseTrue
  checkShape "symbol key" symbolKey (.object root)
    (.error (.unexpectedKeys (pairKeys ++ [.symbol (.allocated 0)])))

  let accessorIndex ← defineOrFail "accessor index" heap root (Array.indexKey 0) {
    get := .present none
    set := .present none
    enumerable := .present true
    configurable := .present true
  }
  checkShape "accessor at an index" accessorIndex (.object root) (.error (.malformedIndex 0))

  let nonWritableIndex ← defineOrFail "non-writable index" heap root (Array.indexKey 1)
    { writable := .present false }
  checkShape "non-writable index" nonWritableIndex (.object root) (.error (.malformedIndex 1))

  let nonEnumerableIndex ← defineOrFail "non-enumerable index" heap root (Array.indexKey 0)
    { enumerable := .present false }
  checkShape "non-enumerable index" nonEnumerableIndex (.object root) (.error (.malformedIndex 0))

  let nonConfigurableIndex ← defineOrFail "non-configurable index" heap root (Array.indexKey 1)
    { configurable := .present false }
  checkShape "non-configurable index" nonConfigurableIndex (.object root)
    (.error (.malformedIndex 1))

/-- Exact typed fault identity at the codec boundary, including the element index a decode blames. -/
private def testDecodeFaultIdentity : IO Unit := do
  let (root, heap) ← allocateOrFail "boolean pair"
    [some (.primitive (.boolean true)), some (.primitive (.boolean false))]
  checkDecode Bool.codec "boolean pair decodes exactly" heap (.object root) (.ok [true, false])
  checkDecode Bool.codec "primitive" Heap.empty (.primitive .undefined)
    (.error (.shape .expectedObject))
  checkDecode Bool.codec "dangling reference" Heap.empty (.object ⟨0⟩)
    (.error (.shape (.invalidRef ⟨0⟩)))
  let frozen ← orFail "preventExtensions" (heap.preventExtensions root)
  checkDecode Bool.codec "shape fault is wrapped, not swallowed" frozen (.object root)
    (.error (.shape .notExtensible))

  let (mixedRoot, mixedHeap) ← allocateOrFail "array with a non-boolean element"
    [some (.primitive (.boolean true)), some (.primitive .undefined)]
  checkDecode Bool.codec "element fault names the failing index" mixedHeap (.object mixedRoot)
    (.error (.element 1 .expectedBoolean))

  let (bigintRoot, bigintHeap) ← allocateOrFail "bigint pair"
    [some (.primitive (.bigint 1)), some (.primitive (.bigint (-2)))]
  checkDecode BigInt.codec "bigint pair decodes exactly" bigintHeap (.object bigintRoot)
    (.ok [1, -2])
  checkDecode BigInt.codec "bigint element fault" mixedHeap (.object mixedRoot)
    (.error (.element 0 .expectedBigInt))

  let (stringRoot, stringHeap) ← allocateOrFail "string pair"
    [some (.primitive (.string (JSString.ofLeanString ""))),
      some (.primitive (.string (JSString.ofLeanString "array")))]
  checkDecode String.codec "string pair decodes exactly" stringHeap (.object stringRoot)
    (.ok ["", "array"])
  checkDecode String.codec "string element fault" mixedHeap (.object mixedRoot)
    (.error (.element 0 .expectedString))

/-- Encoding, the guard in both directions, and a decode of exactly what encoding produced. -/
private def testEncodeGuardRoundtrip : IO Unit := do
  let natives := #[true, false, true]
  let (value, heap) ← orFail "encode" (Array.encode Bool.codec Heap.empty natives)
  check "encode allocates a root that was invalid before it ran" (!Heap.empty.valueValid value)
  check "encode returns a valid reference" (heap.valueValid value)
  check "guard accepts the encoded array" ((Array.denseShapeGuard heap).check value)
  check "guard rejects the encoded value against the pre-encode heap"
    (!(Array.denseShapeGuard Heap.empty).check value)
  check "guard rejects a primitive" (!(Array.denseShapeGuard heap).check (.primitive .undefined))
  checkShape "encoding produces exactly the encoded elements" heap value
    (.ok [.primitive (.boolean true), .primitive (.boolean false), .primitive (.boolean true)])
  checkDecode Bool.codec "roundtrip returns the original array" heap value
    (.ok [true, false, true])
  match value with
  | .primitive _ => throw (IO.userError "array fixture failed: encode returned a primitive")
  | .object root =>
      match heap.arrayLength root with
      | .ok length => check "encoded length" (length == 3)
      | .error _ => throw (IO.userError "array fixture failed: encoded array has no length")
      match heap.ownPropertyKeys root with
      | .ok keys => check "encoded own keys are exactly dense" (keys == Array.denseKeys 3)
      | .error _ => throw (IO.userError "array fixture failed: encoded array has no own keys")
  let (emptyValue, emptyHeap) ← orFail "encode empty" (Array.encode Bool.codec Heap.empty #[])
  checkShape "the empty array encodes and validates" emptyHeap emptyValue (.ok [])
  checkDecode Bool.codec "the empty array roundtrips" emptyHeap emptyValue (.ok [])
  let (nestedValue, nestedHeap) ← orFail "encode nested"
    (Array.encode Bool.codec heap #[true])
  checkShape "an earlier array survives a later encode" nestedHeap value
    (.ok [.primitive (.boolean true), .primitive (.boolean false), .primitive (.boolean true)])
  checkShape "the later array validates too" nestedHeap nestedValue (.ok [.primitive (.boolean true)])

/-- Arrays of arrays encode, validate and decode. This executes the composition `nested_array_contract`
proves: the inner array codec supplies `Codec.Complete` even though it can never be lawful. -/
private def testNestedArrays : IO Unit := do
  let natives : _root_.Array (_root_.Array Bool) := #[#[true, false], #[], #[true]]
  let (value, heap) ← orFail "nested encode"
    (Array.encode (Array.codec Bool.codec) Heap.empty natives)
  check "nested encode allocates a root that was invalid before it ran"
    (!Heap.empty.valueValid value)
  check "guard accepts the nested array" ((Array.denseShapeGuard heap).check value)
  checkDecode (Array.codec Bool.codec) "nested roundtrip returns the original arrays" heap value
    (.ok [#[true, false], #[], #[true]])
  match Array.inspectDense heap value with
  | .error _ => throw (IO.userError "array fixture failed: the nested outer array was rejected")
  | .ok (_, inner) =>
      check "the outer array holds three inner references" (inner.size == 3)
      for element in inner do
        check "every inner element is itself an exactly dense array"
          (Array.inspectDense heap element).isOk
      match inner[0]?, inner[1]? with
      | some first, some second =>
          checkShape "the first inner array holds exactly its elements" heap first
            (.ok [.primitive (.boolean true), .primitive (.boolean false)])
          checkShape "the empty inner array holds exactly nothing" heap second (.ok [])
      | _, _ => throw (IO.userError "array fixture failed: the nested array lost its elements")

/-- Rejecting a sparse array must cost its own keys, not its declared length. -/
private def testSparseRejection : IO Unit := do
  let (root, heap) ← allocateOrFail "sparse base"
    [some (.primitive (.bigint 0)), some (.primitive (.bigint 1))]
  let sparse ← defineOrFail "sparse length" heap root Heap.lengthPropertyKey
    { value := .present (.primitive (.number (Heap.arrayLengthNumber Heap.maxArrayLength))) }
  match sparse.arrayLength root with
  | .ok length => check "sparse fixture declares the maximum length" (length == Heap.maxArrayLength)
  | .error _ => throw (IO.userError "array fixture failed: sparse array lost its length")
  let ownKeys ← match sparse.ownPropertyKeys root with
    | .ok keys => pure keys.length
    | .error _ => throw (IO.userError "array fixture failed: sparse array lost its keys")
  check "sparse fixture still has its two index keys and length" (ownKeys == 3)
  let start ← IO.monoMsNow
  checkShape "sparse array is rejected on its own keys" sparse (.object root)
    (.error (.unexpectedKeys [Array.indexKey 0, Array.indexKey 1, Heap.lengthPropertyKey]))
  let elapsed := (← IO.monoMsNow) - start
  IO.println s!"array-refinement-sparse declaredLength={Heap.maxArrayLength} ownKeys={ownKeys} rejectMs={elapsed}"
  -- Absolute rather than relative on purpose: the regression this guards is the ~5.4e6 ms cost of
  -- materializing the declared length, and both a bounded rejection here and at any smaller declared
  -- length measure 0 ms, so a ratio between them would be pure timer noise.
  check "sparse rejection is bounded by the actual own-key count" (elapsed < 100)

/-- Doubling the input must roughly double the cost. A quadratic regression shows about 4x, so the
3x + 250ms envelope separates linear from quadratic while tolerating timer noise. -/
private def checkScaling (label : String) (small large : Nat) : IO Unit := do
  IO.println s!"array-refinement-scaling {label} small={small}ms large={large}ms"
  check s!"{label} scales linearly" (large ≤ 3 * small + 250)

private def measureDense (count : Nat) : IO Nat := do
  let elements := (List.range count).map fun index =>
    some (Value.primitive (.bigint (Int.ofNat index)))
  let (root, heap) ← allocateOrFail "dense scale fixture" elements
  check "dense scale fixture allocated one object" (heap.size == 1)
  let start ← IO.monoMsNow
  check "dense scale fixture is accepted" (Array.inspectDense heap (.object root)).isOk
  let elapsed := (← IO.monoMsNow) - start
  IO.println s!"array-refinement-scale elements={count} validateMs={elapsed}"
  pure elapsed

private def measureCodec (count : Nat) : IO (Nat × Nat) := do
  let natives := ((List.range count).map fun index => index % 2 == 0).toArray
  check "codec scale fixture has the requested size" (natives.size == count)
  let encodeStart ← IO.monoMsNow
  let (value, heap) ← orFail "codec scale encode" (Array.encode Bool.codec Heap.empty natives)
  let encodeMs := (← IO.monoMsNow) - encodeStart
  let decodeStart ← IO.monoMsNow
  let decoded ← orFail "codec scale decode" (Array.decode Bool.codec heap value)
  let decodeMs := (← IO.monoMsNow) - decodeStart
  check "codec scale roundtrip returns the original array" (decoded == natives)
  IO.println s!"array-refinement-codec elements={count} encodeMs={encodeMs} decodeMs={decodeMs}"
  pure (encodeMs, decodeMs)

private def testScale : IO Unit := do
  let denseSmall ← measureDense 50000
  let denseLarge ← measureDense 100000
  checkScaling "dense-validation" denseSmall denseLarge
  let (encodeSmall, decodeSmall) ← measureCodec 50000
  let (encodeLarge, decodeLarge) ← measureCodec 100000
  checkScaling "encode" encodeSmall encodeLarge
  checkScaling "decode" decodeSmall decodeLarge

#eval testShapeFaultIdentity
#eval testDecodeFaultIdentity
#eval testEncodeGuardRoundtrip
#eval testNestedArrays
#eval testSparseRejection
#eval testScale

end TSLean.Refinement.Tests
