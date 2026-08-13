import TSLean.Refinement

namespace TSLean.Refinement.Tests

open TSLean.JS

namespace RecordContracts

open TSLean.Refinement.Record

universe u v w

/-- Typed statement of every theorem registered under `TSLean.Refinement.Record.` in
`scripts/refinement-proof-registry.mjs`, in registry order. Each conjunct spells out the proposition
the registry demands, so weakening any registered statement stops this from compiling: the named
theorem no longer inhabits its conjunct. A registry checks names; only this checks meaning.

The remaining registered declarations are this file's own witness theorems below, whose statements
are their contract: each applies the registered production theorems to one concrete schema, so
weakening any of them is visible in the same file a reviewer is already reading. -/
theorem record_contract_inventory {FieldEncodeFault FieldEncodeLabel : Type v}
    {FieldDecodeFault FieldDecodeLabel : Type w} (schema : Schema.{u})
    (codecs : Codecs FieldEncodeFault FieldDecodeFault schema) (native : Native schema)
    (encodeLabel : FieldEncodeFault → FieldEncodeLabel)
    (decodeLabel : FieldDecodeFault → FieldDecodeLabel) :
    -- RecordRel.field_valueValid
    (∀ (heap : Heap) (record : Native schema) (value : Value) (key : JSString),
      RecordRel schema heap record value → key ∈ fieldKeys schema →
      ∃ root encoded, value = .object root ∧
        heap.getOwnProperty root (.string key) =
          .ok (some (.data ⟨encoded, true, true, true⟩)) ∧
        heap.valueValid encoded = true) ∧
    -- RecordRel.recordShape
    (∀ (heap : Heap) (record : Native schema) (value : Value),
      RecordRel schema heap record value → RecordShape (fieldKeys schema) heap value) ∧
    -- RecordRel.root_valueValid
    (∀ (heap : Heap) (record : Native schema) (value : Value),
      RecordRel schema heap record value → heap.valueValid value = true) ∧
    -- RecordRel.stable
    (∀ (old next : Heap) (record : Native schema) (value : Value),
      Refinement.Heap.ExactExtension old next → RecordRel schema old record value →
      RecordRel schema next record value) ∧
    -- codec_complete (field completeness only, so records of records compose)
    (Codecs.Complete schema codecs → ∀ (heap : Heap) (record : Native schema) (value : Value),
      (refinement schema).Rel heap record value →
      (codec schema codecs).decode heap value = .ok record) ∧
    -- codec_lawful (unconditional for a presentable schema, unlike arrays)
    (Codecs.Lawful schema codecs → Codecs.Complete schema codecs →
      ValidKeys (fieldKeys schema) → LawfulCodec (codec schema codecs)) ∧
    -- codec_roundtrip
    (Codecs.Lawful schema codecs → Codecs.Complete schema codecs →
      ValidKeys (fieldKeys schema) → ∀ (heap : Heap) (record : Native schema), heap.WellFormed →
      ∃ value next,
        (codec schema codecs).encode heap record = .ok (value, next) ∧
        Refinement.Heap.ExactExtension heap next ∧
        (refinement schema).Rel next record value ∧
        (codec schema codecs).decode next value = .ok record) ∧
    -- decode_complete (field completeness only)
    (Codecs.Complete schema codecs → ∀ (heap : Heap) (record : Native schema) (value : Value),
      RecordRel schema heap record value → decode schema codecs heap value = .ok record) ∧
    -- decode_exact (field completeness only)
    (Codecs.Complete schema codecs → ∀ (heap : Heap) (value : Value) (record : Native schema),
      (codec schema codecs).decode heap value = .ok record ↔
        (refinement schema).Rel heap record value) ∧
    -- decode_invalidRef
    (∀ (heap : Heap) (ref : RefId) (fault : HeapFault), heap.get? ref = .error fault →
      (codec schema codecs).decode heap (.object ref) = .error (.shape (.invalidRef ref))) ∧
    -- decode_notExtensible
    (∀ (heap : Heap) (ref : RefId) (object : ObjectRecord), heap.get? ref = .ok object →
      object.kind = .ordinary → object.prototype = none → object.extensible = false →
      (codec schema codecs).decode heap (.object ref) = .error (.shape .notExtensible)) ∧
    -- decode_primitive
    (∀ (heap : Heap) (primitive : JS.Primitive),
      (codec schema codecs).decode heap (.primitive primitive) =
        .error (.shape .expectedObject)) ∧
    -- decode_shapeFault
    (∀ (heap : Heap) (value : Value) (fault : ShapeFault),
      inspectRecord (fieldKeys schema) heap value = .error fault →
      (codec schema codecs).decode heap value = .error (.shape fault)) ∧
    -- decode_sound
    (∀ (heap : Heap) (value : Value) (record : Native schema),
      decode schema codecs heap value = .ok record → RecordRel schema heap record value) ∧
    -- decode_wrongKind
    (∀ (heap : Heap) (ref : RefId) (object : ObjectRecord), heap.get? ref = .ok object →
      object.kind ≠ .ordinary →
      (codec schema codecs).decode heap (.object ref) =
        .error (.shape (.wrongKind object.kind.tag))) ∧
    -- decode_wrongPrototype
    (∀ (heap : Heap) (ref : RefId) (object : ObjectRecord) (prototype : RefId),
      heap.get? ref = .ok object → object.kind = .ordinary →
      object.prototype = some prototype →
      (codec schema codecs).decode heap (.object ref) =
        .error (.shape (.wrongPrototype prototype))) ∧
    -- encode_exact
    (∀ (old : Heap) (record : Native schema) (value : Value) (next : Heap), old.WellFormed →
      encode schema codecs old record = .ok (value, next) →
      ∃ root, value = .object root ∧ old.valueValid (.object root) = false ∧
        RecordRel schema next record (.object root)) ∧
    -- encode_invalidSchema
    (∀ (heap : Heap) (record : Native schema) (fault : SchemaFault),
      validateKeys (fieldKeys schema) = .error fault →
      encode schema codecs heap record = .error (.invalidSchema fault)) ∧
    -- encode_sound
    (∀ (old : Heap) (record : Native schema) (value : Value) (next : Heap), old.WellFormed →
      encode schema codecs old record = .ok (value, next) →
      Refinement.Heap.ExactExtension old next ∧ RecordRel schema next record value) ∧
    -- encode_total (field totality and a presentable declared key sequence)
    (Codecs.Lawful schema codecs → ValidKeys (fieldKeys schema) →
      ∀ (heap : Heap) (record : Native schema), heap.WellFormed →
      ∃ value next, encode schema codecs heap record = .ok (value, next)) ∧
    -- fresh_root_distinct
    (∀ (old next : Heap) (prototype : Option RefId) (extensible : Bool) (fresh previous : RefId),
      old.allocate prototype extensible = .ok (fresh, next) →
      old.valueValid (.object previous) = true → fresh ≠ previous) ∧
    -- getOwnProperty_commutes
    (∀ (spec : FieldSpec.{u}) (rest : Schema.{u}) (heap : Heap) (record : Native (spec :: rest))
      (value : Value), RecordRel (spec :: rest) heap record value →
      ∃ root encoded, value = .object root ∧
        heap.getOwnProperty root (.string spec.key) =
          .ok (some (.data ⟨encoded, true, true, true⟩)) ∧
        spec.element.Rel heap record.1 encoded ∧ FieldsRel rest heap root record.2) ∧
    -- inspectRecord_complete
    (∀ (declared : List JSString) (heap : Heap) (value : Value), RecordShape declared heap value →
      ∃ root values, inspectRecord declared heap value = .ok (root, values)) ∧
    -- inspectRecord_sound
    (∀ (declared : List JSString) (heap : Heap) (value : Value) (root : RefId)
      (values : List Value), inspectRecord declared heap value = .ok (root, values) →
      ∃ object,
        value = .object root ∧
        heap.get? root = .ok object ∧
        object.kind = .ordinary ∧
        object.prototype = none ∧
        object.extensible = true ∧
        heap.ownPropertyKeys root = .ok (declared.map .string) ∧
        values.length = declared.length ∧
        (∀ field ∈ declared.zip values, heap.getOwnProperty root (.string field.1) =
          .ok (some (.data ⟨field.2, true, true, true⟩))) ∧
        ∀ key ∈ declared, ∃ encoded, heap.getOwnProperty root (.string key) =
          .ok (some (.data ⟨encoded, true, true, true⟩))) ∧
    -- matchKeys_iff
    (∀ (declared : List JSString) (actual : List PropertyKey),
      matchKeys declared actual = .ok () ↔ actual = declared.map .string) ∧
    -- not_lawful
    (¬ValidKeys (fieldKeys schema) → ¬LawfulCodec (codec schema codecs)) ∧
    -- nodup_of_related
    (∀ (heap : Heap) (record : Native schema) (value : Value), heap.WellFormed →
      RecordRel schema heap record value → (fieldKeys schema).Nodup) ∧
    -- ownPropertyKeys_commutes
    (∀ (heap : Heap) (record : Native schema) (value : Value),
      RecordRel schema heap record value →
      ∃ root, value = .object root ∧ heap.ownPropertyKeys root = .ok (ownKeys schema)) ∧
    -- recordShapeGuard_complete
    (∀ (declared : List JSString) (heap : Heap) (value : Value), RecordShape declared heap value →
      (recordShapeGuard declared heap).check value = true) ∧
    -- recordShapeGuard_sound
    (∀ (declared : List JSString) (heap : Heap) (value : Value),
      (recordShapeGuard declared heap).check value = true → RecordShape declared heap value) ∧
    -- refinement_uniqueDecode
    (UniqueFields schema → (refinement schema).UniqueDecode) ∧
    -- relabel_complete
    (∀ {α : Type u} {element : Refinement α}
      (fieldCodec : Codec α FieldEncodeFault FieldDecodeFault element), fieldCodec.Complete →
      (relabel fieldCodec encodeLabel decodeLabel).Complete) ∧
    -- relabel_lawful
    (∀ {α : Type u} {element : Refinement α}
      (fieldCodec : Codec α FieldEncodeFault FieldDecodeFault element), LawfulCodec fieldCodec →
      LawfulCodec (relabel fieldCodec encodeLabel decodeLabel)) ∧
    -- validateKeys_iff
    (∀ declared : List JSString, validateKeys declared = .ok () ↔ ValidKeys declared) :=
  ⟨fun _ _ _ key related declared => RecordRel.field_valueValid related key declared,
    fun _ _ _ related => related.recordShape,
    fun _ _ _ related => related.root_valueValid,
    fun _ _ _ _ extension related => RecordRel.stable extension related,
    fun complete _ _ _ related => codec_complete complete related,
    fun lawful complete keysValid => codec_lawful lawful complete keysValid,
    fun lawful complete keysValid heap record valid =>
      codec_roundtrip lawful complete keysValid heap record valid,
    fun complete _ _ _ related => decode_complete complete related,
    fun complete heap value record => decode_exact complete heap value record,
    fun heap ref fault missing => decode_invalidRef schema codecs heap ref fault missing,
    fun heap ref object found ordinary prototypeEq frozen =>
      decode_notExtensible schema codecs heap ref object found ordinary prototypeEq frozen,
    fun heap primitive => decode_primitive schema codecs heap primitive,
    fun heap value fault rejected => decode_shapeFault schema codecs heap value fault rejected,
    fun _ _ _ decoded => decode_sound schema codecs decoded,
    fun heap ref object found notOrdinary =>
      decode_wrongKind schema codecs heap ref object found notOrdinary,
    fun heap ref object prototype found ordinary inherits =>
      decode_wrongPrototype schema codecs heap ref object prototype found ordinary inherits,
    fun _ _ _ _ valid encoded => encode_exact schema codecs valid encoded,
    fun heap record fault invalid => encode_invalidSchema schema codecs heap record fault invalid,
    fun _ _ _ _ valid encoded => encode_sound schema codecs valid encoded,
    fun lawful keysValid heap record valid => encode_total lawful keysValid heap record valid,
    fun old next prototype extensible fresh previous allocated previousValid =>
      fresh_root_distinct old next prototype extensible fresh previous allocated previousValid,
    fun _ _ _ _ _ related => getOwnProperty_commutes related,
    fun _ _ _ shape => inspectRecord_complete shape,
    fun _ _ _ _ _ inspected => inspectRecord_sound inspected,
    matchKeys_iff,
    fun invalid => not_lawful schema codecs native invalid,
    fun _ _ _ valid related => nodup_of_related valid related,
    fun _ _ _ related => ownPropertyKeys_commutes related,
    fun declared heap value shape => recordShapeGuard_complete declared heap value shape,
    fun declared heap value accepted => recordShapeGuard_sound declared heap value accepted,
    fun unique => refinement_uniqueDecode unique,
    fun _ complete => relabel_complete complete encodeLabel decodeLabel,
    fun _ lawful => relabel_lawful lawful encodeLabel decodeLabel,
    validateKeys_iff⟩

/-! ## A concrete closed record

Every premise of the record contracts is discharged against this schema: two fields whose Lean
carriers are different types, refined by two different committed codecs. -/

/-- The demonstration record's own property keys. -/
def flagKey : JSString := JSString.ofLeanString "flag"

/-- The second declared key of the demonstration record. -/
def labelKey : JSString := JSString.ofLeanString "label"

/-- A key that is not declared by the demonstration record. -/
def extraKey : JSString := JSString.ofLeanString "extra"

/-- Typed decode faults of the demonstration record's fields: one label per field carrier. -/
inductive FieldFault where
  | boolean (fault : Bool.DecodeFault)
  | text (fault : String.DecodeFault)
  deriving DecidableEq, Repr

/-- `{ flag: boolean; label: string }` as a closed record schema. -/
def demoSchema : Schema.{0} :=
  [⟨flagKey, _root_.Bool, Bool.refinement⟩, ⟨labelKey, _root_.String, String.refinement⟩]

/-- The demonstration record's field codecs, relabelled onto one shared fault type. -/
def demoCodecs : Codecs Empty FieldFault demoSchema :=
  (relabel Bool.codec id FieldFault.boolean, relabel String.codec id FieldFault.text, PUnit.unit)

/-- `{ flag: true, label: "kumo" }`. -/
def demoRecord : Native demoSchema := (true, "kumo", PUnit.unit)

/-- Every field codec of the demonstration record is lawful, hence complete. -/
theorem demo_codecs_lawful : Codecs.Lawful demoSchema demoCodecs :=
  ⟨relabel_lawful Bool.codec_lawful id FieldFault.boolean,
    relabel_lawful String.codec_lawful id FieldFault.text, trivial⟩

/-- Every field codec of the demonstration record decodes its relation completely. -/
theorem demo_codecs_complete : Codecs.Complete demoSchema demoCodecs :=
  ⟨relabel_complete Bool.codec_lawful.complete id FieldFault.boolean,
    relabel_complete String.codec_lawful.complete id FieldFault.text, trivial⟩

/-- Each field of the demonstration record decodes uniquely. -/
theorem demo_unique_fields : UniqueFields demoSchema :=
  ⟨Bool.refinement_uniqueDecode, String.refinement_uniqueDecode, trivial⟩

/-- The demonstration record's declared keys are exactly what ECMAScript own-key order can present in
declaration order. -/
theorem demo_keys_valid : ValidKeys (fieldKeys demoSchema) := by
  refine ⟨?_, ?_⟩ <;> decide

/-- Every premise of the record codec contracts is jointly satisfiable: one encode against two
different committed field codecs discharges heap well-formedness, schema presentability and field
lawfulness at once. Each conjunct below is then produced by applying one registered theorem to that
instance, so none of them is vacuous. -/
theorem record_codec_contract_witness :
    ∃ value next root,
      (codec demoSchema demoCodecs).encode Heap.empty demoRecord = .ok (value, next) ∧
      Refinement.Heap.ExactExtension Heap.empty next ∧
      (refinement demoSchema).Rel next demoRecord value ∧
      (codec demoSchema demoCodecs).decode next value = .ok demoRecord ∧
      value = .object root ∧
      Heap.empty.valueValid (.object root) = false ∧
      next.valueValid value = true ∧
      next.ownPropertyKeys root = .ok (ownKeys demoSchema) ∧
      RecordShape (fieldKeys demoSchema) next value ∧
      (recordShapeGuard (fieldKeys demoSchema) next).check value = true ∧
      (fieldKeys demoSchema).Nodup ∧
      (∃ encoded, next.getOwnProperty root (.string flagKey) =
          .ok (some (.data ⟨encoded, true, true, true⟩)) ∧
        Bool.refinement.Rel next true encoded ∧ next.valueValid encoded = true) ∧
      (∃ values, inspectRecord (fieldKeys demoSchema) next value = .ok (root, values) ∧
        values.length = 2) := by
  obtain ⟨value, next, encoded, extension, related, decoded⟩ :=
    codec_roundtrip demo_codecs_lawful demo_codecs_complete demo_keys_valid Heap.empty demoRecord
      Heap.empty_wellFormed
  obtain ⟨root, valueEq, fresh, _⟩ := encode_exact demoSchema demoCodecs Heap.empty_wellFormed
    (native := demoRecord) (value := value) (next := next) encoded
  obtain ⟨keysRoot, keysValueEq, keysEq⟩ := ownPropertyKeys_commutes related
  obtain ⟨flagRoot, flagEncoded, flagValueEq, flagFound, flagRelated, _⟩ :=
    getOwnProperty_commutes related
  obtain ⟨validRoot, validEncoded, validValueEq, validFound, validValid⟩ :=
    RecordRel.field_valueValid related flagKey (by decide)
  have shape := related.recordShape
  have accepted := recordShapeGuard_complete (fieldKeys demoSchema) next value shape
  obtain ⟨inspectedRoot, values, inspected⟩ :=
    inspectRecord_complete (recordShapeGuard_sound (fieldKeys demoSchema) next value accepted)
  obtain ⟨_, inspectedValueEq, _, _, _, _, _, length, _, _⟩ := inspectRecord_sound inspected
  have rootOf : ∀ other : RefId, value = .object other → other = root := by
    intro other otherEq
    rw [valueEq] at otherEq
    exact (Value.object.inj otherEq).symm
  rw [rootOf keysRoot keysValueEq] at keysEq
  rw [rootOf flagRoot flagValueEq] at flagFound
  rw [rootOf validRoot validValueEq] at validFound
  rw [rootOf inspectedRoot inspectedValueEq] at inspected
  refine ⟨value, next, root, encoded, extension, related, decoded, valueEq, fresh,
    related.root_valueValid, keysEq, shape, accepted,
    nodup_of_related extension.nextWellFormed related,
    ⟨flagEncoded, flagFound, flagRelated, ?_⟩, values, inspected, by simpa using length⟩
  rw [flagFound] at validFound
  have descriptorsEqual := PropertyDescriptor.data.inj (Option.some.inj (Except.ok.inj validFound))
  cases descriptorsEqual
  exact validValid

/-- A schema declaring the same key twice cannot be encoded, and the refusal is justified rather than
conservative: `nodup_of_related` shows no well-formed heap relates any value to it. -/
theorem repeated_key_schema_not_lawful :
    ¬LawfulCodec (codec [⟨flagKey, _root_.Bool, Bool.refinement⟩,
      ⟨flagKey, _root_.Bool, Bool.refinement⟩] (relabel Bool.codec id FieldFault.boolean,
        relabel Bool.codec id FieldFault.boolean, PUnit.unit)) := by
  refine not_lawful _ _ (true, false, PUnit.unit) ?_
  intro valid
  exact absurd valid.1 (by decide)

/-- A schema declaring an integer-index key after a plain one cannot be encoded: ECMAScript own-key
order hoists the index ahead of every other string key, so `["flag", "0"]` is answered as
`["0", "flag"]` and declaration order is not its own-key order.

The witness is deliberately this order rather than `["0", "flag"]`, which the model does present in
declaration order — the refusal there is the conservatism `ValidKeys` documents, not a forced
consequence, so it cannot justify this theorem. -/
theorem index_like_key_schema_not_lawful :
    ¬LawfulCodec (codec [⟨flagKey, _root_.Bool, Bool.refinement⟩,
      ⟨JSString.ofLeanString "0", _root_.Bool, Bool.refinement⟩]
        (relabel Bool.codec id FieldFault.boolean,
          relabel Bool.codec id FieldFault.boolean, PUnit.unit)) := by
  refine not_lawful _ _ (true, false, PUnit.unit) ?_
  intro valid
  exact absurd (valid.2 (JSString.ofLeanString "0") (by decide)) (by decide)

/-- The empty heap witnesses the dangling-reference premise. -/
theorem record_decode_rejects_dangling :
    (codec demoSchema demoCodecs).decode Heap.empty (.object ⟨0⟩) =
      .error (.shape (.invalidRef ⟨0⟩)) :=
  decode_invalidRef demoSchema demoCodecs Heap.empty ⟨0⟩ (.invalidRef ⟨0⟩) rfl

/-- Primitives are rejected in the object domain, whatever the heap. -/
theorem record_decode_rejects_primitive (heap : Heap) (primitive : JS.Primitive) :
    (codec demoSchema demoCodecs).decode heap (.primitive primitive) =
      .error (.shape .expectedObject) :=
  decode_primitive demoSchema demoCodecs heap primitive

/-- A dense array witnesses the wrong-kind premise with a genuinely allocated object. -/
theorem record_decode_rejects_wrong_kind (heap next : Heap) (root : RefId)
    (allocated : heap.allocateArray [] none = .ok (root, next)) :
    ∃ tag, (codec demoSchema demoCodecs).decode next (.object root) =
      .error (.shape (.wrongKind tag)) := by
  obtain ⟨_, kindEq⟩ := Heap.allocateArray_result_fresh_kind heap next [] none root allocated
  unfold Heap.objectKind? at kindEq
  cases found : next.get? root with
  | error fault =>
      rw [found] at kindEq
      simp at kindEq
  | ok object =>
      rw [found] at kindEq
      simp only [Option.some.injEq] at kindEq
      exact ⟨object.kind.tag, decode_wrongKind demoSchema demoCodecs next root object found
        (by rw [kindEq]; simp)⟩

/-- A closed record whose single field is itself a closed record. -/
def nestedSchema : Schema.{0} := [⟨flagKey, Native demoSchema, refinement demoSchema⟩]

/-- The nested record's field codec is the demonstration record's own codec. -/
def nestedCodecs : Codecs (EncodeFault Empty) (DecodeFault FieldFault) nestedSchema :=
  (codec demoSchema demoCodecs, PUnit.unit)

/-- The nested record's field codec decodes its relation completely. -/
theorem nested_codecs_complete : Codecs.Complete nestedSchema nestedCodecs :=
  ⟨codec_complete demo_codecs_complete, trivial⟩

/-- The decode side composes into records of records: the inner record codec supplies
`Codecs.Complete`, and `record_codec_contract_witness` shows that hypothesis is inhabited rather than
merely assumed. -/
theorem nested_record_contract :
    (codec demoSchema demoCodecs).Complete ∧
    (refinement demoSchema).UniqueDecode ∧
    Codecs.Complete nestedSchema nestedCodecs ∧
    ∀ (heap : Heap) (value : Value) (record : Native nestedSchema),
      (codec nestedSchema nestedCodecs).decode heap value = .ok record ↔
        (refinement nestedSchema).Rel heap record value :=
  ⟨codec_complete demo_codecs_complete, refinement_uniqueDecode demo_unique_fields,
    nested_codecs_complete, fun heap value record =>
      decode_exact nested_codecs_complete heap value record⟩

end RecordContracts

open RecordContracts (flagKey labelKey extraKey FieldFault demoSchema demoCodecs demoRecord
  nestedSchema nestedCodecs)

private instance : DecidableEq (Record.Native demoSchema) :=
  inferInstanceAs (DecidableEq (Bool × String × PUnit))

private instance : DecidableEq (Record.Native nestedSchema) :=
  inferInstanceAs (DecidableEq ((Bool × String × PUnit) × PUnit))

private def check (label : String) (condition : Bool) : IO Unit :=
  if condition then pure () else throw (IO.userError s!"record refinement regression: {label}")

private def orFail (label : String) : Except ε β → IO β
  | .ok value => pure value
  | .error _ => throw (IO.userError s!"record fixture failed: {label}")

private def createOrFail (label : String) (heap : Heap) (root : RefId) (key : PropertyKey)
    (value : Value) : IO Heap := do
  match ← orFail label (heap.createDataProperty root key value) with
  | (true, next) => pure next
  | (false, _) => throw (IO.userError s!"record fixture rejected: {label}")

private def defineOrFail (label : String) (heap : Heap) (root : RefId) (key : PropertyKey)
    (update : DescriptorUpdate) : IO Heap := do
  match ← orFail label (heap.defineOwnProperty root key update) with
  | (true, next) => pure next
  | (false, _) => throw (IO.userError s!"record fixture rejected: {label}")

/-- Allocates one ordinary object with a null prototype carrying exactly the given own data
properties, in the given order. This is the same public sequence the record encoder runs. -/
private def allocateRecordOrFail (label : String) (fields : List (PropertyKey × Value))
    (heap : Heap := Heap.empty) (prototype : Option RefId := none) : IO (RefId × Heap) := do
  let (root, allocated) ← orFail label (heap.allocate prototype true)
  let mut current := allocated
  for field in fields do
    current ← createOrFail label current root field.1 field.2
  pure (root, current)

private def flagTrue : Value := .primitive (.boolean true)
private def labelText : Value := .primitive (.string (JSString.ofLeanString "kumo"))

private def demoFields : List (PropertyKey × Value) :=
  [(.string flagKey, flagTrue), (.string labelKey, labelText)]

/-- Compares a shape inspection against the exact expected field values or the exact typed fault. -/
private def shapeIs (declared : List JSString) (heap : Heap) (value : Value)
    (expected : Except Record.ShapeFault (List Value)) : Bool :=
  match (Record.inspectRecord declared heap value).map (·.2), expected with
  | .ok actual, .ok wanted => decide (actual = wanted)
  | .error actual, .error wanted => decide (actual = wanted)
  | _, _ => false

private def checkShape (label : String) (heap : Heap) (value : Value)
    (expected : Except Record.ShapeFault (List Value))
    (declared : List JSString := Record.fieldKeys demoSchema) : IO Unit :=
  check label (shapeIs declared heap value expected)

/-- Compares a record decode against the exact expected record or the exact typed fault. -/
private def checkDecode (label : String) (heap : Heap) (value : Value)
    (expected : Except (Record.DecodeFault FieldFault) (Record.Native demoSchema)) : IO Unit :=
  check label
    (match Record.decode demoSchema demoCodecs heap value, expected with
      | .ok actual, .ok wanted => decide (actual = wanted)
      | .error actual, .error wanted => decide (actual = wanted)
      | _, _ => false)

/-- Exact typed fault identity for every reachable rejection of the closed-record validator. -/
private def testShapeFaultIdentity : IO Unit := do
  let (root, heap) ← allocateRecordOrFail "demo record" demoFields
  checkShape "the declared record is accepted with its exact field values" heap (.object root)
    (.ok [flagTrue, labelText])
  let (emptyRoot, emptyHeap) ← allocateRecordOrFail "empty record" []
  checkShape "a record with no declared field is accepted" emptyHeap (.object emptyRoot) (.ok [])
    (declared := [])

  checkShape "undefined primitive" Heap.empty (.primitive .undefined) (.error .expectedObject)
  checkShape "null primitive" Heap.empty (.primitive .null) (.error .expectedObject)
  checkShape "string primitive" heap (.primitive (.string flagKey)) (.error .expectedObject)

  checkShape "dangling reference into the empty heap" Heap.empty (.object ⟨0⟩)
    (.error (.invalidRef ⟨0⟩))
  checkShape "dangling reference past the frontier" heap (.object ⟨7⟩) (.error (.invalidRef ⟨7⟩))

  let (arrayRoot, arrayHeap) ← orFail "array" (heap.allocateArray [] none)
  checkShape "array object" arrayHeap (.object arrayRoot) (.error (.wrongKind .array))
  let (iteratorRoot, iteratorHeap) ← orFail "array iterator"
    (arrayHeap.allocateArrayIterator arrayRoot none)
  checkShape "array iterator" iteratorHeap (.object iteratorRoot)
    (.error (.wrongKind .arrayIterator))
  let (wrapperRoot, wrapperHeap) ← orFail "primitive wrapper"
    (Heap.empty.allocatePrimitiveWrapper (.boolean true) none)
  checkShape "primitive wrapper" wrapperHeap (.object wrapperRoot)
    (.error (.wrongKind .primitiveWrapper))
  let (functionRoot, functionHeap) ← orFail "function"
    (Heap.empty.allocateFunction ⟨0⟩ .ordinary false none none)
  checkShape "function object" functionHeap (.object functionRoot) (.error (.wrongKind .function))

  let (prototypeRoot, prototypeHeap) ← allocateRecordOrFail "prototype object" []
  let (childRoot, childHeap) ← allocateRecordOrFail "record with a prototype" demoFields
    prototypeHeap (some prototypeRoot)
  checkShape "wrong prototype" childHeap (.object childRoot)
    (.error (.wrongPrototype prototypeRoot))
  -- An inherited declared field is unexhibitable: the relation fixes the prototype at `none`, so the
  -- prototype check rejects before any own key is read. This pins that ordering instead of asserting
  -- an inherited-field fault that cannot occur.
  let prototypeWithFlag ← createOrFail "inherited field" prototypeHeap prototypeRoot
    (.string flagKey) flagTrue
  let (inheritedRoot, inheritedHeap) ← allocateRecordOrFail "record inheriting a field"
    [(.string labelKey, labelText)] prototypeWithFlag (some prototypeRoot)
  checkShape "an inherited field is masked by the prototype fault" inheritedHeap
    (.object inheritedRoot) (.error (.wrongPrototype prototypeRoot))

  let frozen ← orFail "preventExtensions" (heap.preventExtensions root)
  checkShape "non-extensible record" frozen (.object root) (.error .notExtensible)

  let (shortRoot, shortHeap) ← allocateRecordOrFail "record missing its last field"
    [(.string flagKey, flagTrue)]
  checkShape "a missing declared key names the key it wanted" shortHeap (.object shortRoot)
    (.error (.keys (.missingKey 1 labelKey)))
  let (emptyObjectRoot, emptyObjectHeap) ← allocateRecordOrFail "object with no own key" []
  checkShape "an object with no own key is missing the first declared key" emptyObjectHeap
    (.object emptyObjectRoot) (.error (.keys (.missingKey 0 flagKey)))

  let withExtra ← createOrFail "extra own key" heap root (.string extraKey) flagTrue
  checkShape "an extra own key names the first key past the declared ones" withExtra (.object root)
    (.error (.keys (.extraKey 2 (.string extraKey))))
  let (symbolRoot, symbolHeap) ← allocateRecordOrFail "record with a symbol key"
    (demoFields ++ [(.symbol (.allocated 0), flagTrue)])
  checkShape "a symbol own key is rejected as an extra key" symbolHeap (.object symbolRoot)
    (.error (.keys (.extraKey 2 (.symbol (.allocated 0)))))

  let (renamedRoot, renamedHeap) ← allocateRecordOrFail "record with a renamed field"
    [(.string flagKey, flagTrue), (.string extraKey, labelText)]
  checkShape "a renamed field names its position, its expectation and what it found" renamedHeap
    (.object renamedRoot) (.error (.keys (.keyMismatch 1 labelKey (.string extraKey))))
  let (reorderedRoot, reorderedHeap) ← allocateRecordOrFail "record with reordered fields"
    [(.string labelKey, labelText), (.string flagKey, flagTrue)]
  checkShape "declaration order is part of the shape" reorderedHeap (.object reorderedRoot)
    (.error (.keys (.keyMismatch 0 flagKey (.string labelKey))))

  let accessorFlag ← defineOrFail "accessor field" heap root (.string flagKey) {
    get := .present none
    set := .present none
    enumerable := .present true
    configurable := .present true
  }
  checkShape "an accessor at a declared key is one malformed field" accessorFlag (.object root)
    (.error (.malformedField 0 flagKey))
  let nonWritable ← defineOrFail "non-writable field" heap root (.string labelKey)
    { writable := .present false }
  checkShape "a non-writable field is malformed" nonWritable (.object root)
    (.error (.malformedField 1 labelKey))
  let nonEnumerable ← defineOrFail "non-enumerable field" heap root (.string flagKey)
    { enumerable := .present false }
  checkShape "a non-enumerable field is malformed" nonEnumerable (.object root)
    (.error (.malformedField 0 flagKey))
  let nonConfigurable ← defineOrFail "non-configurable field" heap root (.string labelKey)
    { configurable := .present false }
  checkShape "a non-configurable field is malformed" nonConfigurable (.object root)
    (.error (.malformedField 1 labelKey))

/-- Exact typed fault identity at the codec boundary, including the field a decode blames. -/
private def testDecodeFaultIdentity : IO Unit := do
  let (root, heap) ← allocateRecordOrFail "demo record" demoFields
  checkDecode "the declared record decodes exactly" heap (.object root) (.ok demoRecord)
  checkDecode "primitive" Heap.empty (.primitive .undefined) (.error (.shape .expectedObject))
  checkDecode "dangling reference" Heap.empty (.object ⟨0⟩) (.error (.shape (.invalidRef ⟨0⟩)))
  let frozen ← orFail "preventExtensions" (heap.preventExtensions root)
  checkDecode "a shape fault is wrapped, not swallowed" frozen (.object root)
    (.error (.shape .notExtensible))
  let (mistypedRoot, mistypedHeap) ← allocateRecordOrFail "record with a mistyped field"
    [(.string flagKey, flagTrue), (.string labelKey, .primitive (.bigint 7))]
  checkDecode "a field fault names the failing field and keeps its own cause" mistypedHeap
    (.object mistypedRoot) (.error (.field 1 (.text .expectedString)))
  let (headMistypedRoot, headMistypedHeap) ← allocateRecordOrFail "record with a mistyped flag"
    [(.string flagKey, labelText), (.string labelKey, labelText)]
  checkDecode "the first field is blamed at index zero" headMistypedHeap (.object headMistypedRoot)
    (.error (.field 0 (.boolean .expectedBoolean)))

/-- Encoding, the guard in both directions, and a decode of exactly what encoding produced. -/
private def testEncodeGuardRoundtrip : IO Unit := do
  let (value, heap) ← orFail "encode" (Record.encode demoSchema demoCodecs Heap.empty demoRecord)
  let declared := Record.fieldKeys demoSchema
  check "encode allocates a root that was invalid before it ran" (!Heap.empty.valueValid value)
  check "encode returns a valid reference" (heap.valueValid value)
  check "the guard accepts the encoded record" ((Record.recordShapeGuard declared heap).check value)
  check "the guard rejects the encoded value against the pre-encode heap"
    (!(Record.recordShapeGuard declared Heap.empty).check value)
  check "the guard rejects a primitive"
    (!(Record.recordShapeGuard declared heap).check (.primitive .undefined))
  checkShape "encoding produces exactly the encoded field values" heap value
    (.ok [flagTrue, labelText])
  checkDecode "the roundtrip returns the original record" heap value (.ok demoRecord)
  match value with
  | .primitive _ => throw (IO.userError "record fixture failed: encode returned a primitive")
  | .object root =>
      match heap.ownPropertyKeys root with
      | .ok keys => check "own keys are exactly declared" (keys == Record.ownKeys demoSchema)
      | .error _ => throw (IO.userError "record fixture failed: encoded record has no own keys")
  let (laterValue, laterHeap) ←
    orFail "second encode" (Record.encode demoSchema demoCodecs heap (false, "", PUnit.unit))
  checkShape "an earlier record survives a later encode" laterHeap value (.ok [flagTrue, labelText])
  checkShape "the later record validates too" laterHeap laterValue
    (.ok [.primitive (.boolean false), .primitive (.string (JSString.ofLeanString ""))])
  checkDecode "the later record decodes to its own fields" laterHeap laterValue
    (.ok (false, "", PUnit.unit))

/-- Encoding refuses a schema ECMAScript own-key order cannot present, on the keys alone. -/
private def testSchemaRefusal : IO Unit := do
  let duplicateSchema : Record.Schema.{0} :=
    [⟨flagKey, _root_.Bool, Bool.refinement⟩, ⟨flagKey, _root_.Bool, Bool.refinement⟩]
  let duplicateCodecs : Record.Codecs Empty FieldFault duplicateSchema :=
    (Record.relabel Bool.codec id FieldFault.boolean, Record.relabel Bool.codec id FieldFault.boolean, PUnit.unit)
  check "a repeated declared key is refused with the repeated key"
    (match Record.encode duplicateSchema duplicateCodecs Heap.empty (true, false, PUnit.unit) with
      | .error fault => decide (fault = .invalidSchema (.duplicateKey 0 flagKey))
      | .ok _ => false)
  let indexSchema : Record.Schema.{0} :=
    [⟨JSString.ofLeanString "0", _root_.Bool, Bool.refinement⟩]
  let indexCodecs : Record.Codecs Empty FieldFault indexSchema :=
    (Record.relabel Bool.codec id FieldFault.boolean, PUnit.unit)
  check "an integer-index declared key is refused with its parsed index"
    (match Record.encode indexSchema indexCodecs Heap.empty (true, PUnit.unit) with
      | .error fault =>
          decide (fault = .invalidSchema (.indexLikeKey 0 (JSString.ofLeanString "0") 0))
      | .ok _ => false)
  check "the refusal allocates nothing"
    (match Record.encode duplicateSchema duplicateCodecs Heap.empty (true, false, PUnit.unit) with
      | .error _ => true
      | .ok _ => false)

/-- Records of records encode, validate and decode. This executes the composition
`nested_record_contract` proves. -/
private def testNestedRecords : IO Unit := do
  let (value, heap) ←
    orFail "nested encode" (Record.encode nestedSchema nestedCodecs Heap.empty (demoRecord, PUnit.unit))
  check "the nested encode allocates a root that was invalid before it ran"
    (!Heap.empty.valueValid value)
  check "the guard accepts the nested record"
    ((Record.recordShapeGuard (Record.fieldKeys nestedSchema) heap).check value)
  let decoded ← orFail "nested decode" (Record.decode nestedSchema nestedCodecs heap value)
  check "the nested roundtrip returns the original record" (decide (decoded = (demoRecord, PUnit.unit)))
  match Record.inspectRecord (Record.fieldKeys nestedSchema) heap value with
  | .error _ => throw (IO.userError "record fixture failed: the outer record was rejected")
  | .ok (_, inner) =>
      match inner with
      | [innerValue] =>
          checkShape "the inner record holds exactly its own fields" heap innerValue
            (.ok [flagTrue, labelText])
      | _ => throw (IO.userError "record fixture failed: the nested record lost its field")

private def extraKeyAt (index : Nat) : PropertyKey :=
  .string (JSString.ofLeanString s!"extra{index}")

private def recordWithExtras (count : Nat) : IO (RefId × Heap) :=
  allocateRecordOrFail "record with extra keys"
    (demoFields ++ (List.range count).map fun index => (extraKeyAt index, flagTrue))

/-- Rejecting a record with many extra own keys must cost its actual own-key count, and must stop at
the first key past the declared ones rather than searching the declared keys for each of them. -/
private def measureExtraKeyRejection (count : Nat) : IO Nat := do
  let (root, heap) ← recordWithExtras count
  let ownKeys ← match heap.ownPropertyKeys root with
    | .ok keys => pure keys.length
    | .error _ => throw (IO.userError "record fixture failed: extra-key record lost its keys")
  check "the extra-key fixture really carries every extra key" (ownKeys == count + 2)
  let start ← IO.monoMsNow
  checkShape "an extra-key record is rejected at the first undeclared key" heap (.object root)
    (.error (.keys (.extraKey 2 (extraKeyAt 0))))
  let elapsed := (← IO.monoMsNow) - start
  IO.println s!"record-refinement-extra-keys extraKeys={count} ownKeys={ownKeys} rejectMs={elapsed}"
  pure elapsed

/-- Doubling the input must roughly double the cost. A quadratic regression shows about 4x, so the
3x + 250ms envelope separates linear from quadratic while tolerating timer noise. -/
private def checkScaling (label : String) (small large : Nat) : IO Unit := do
  IO.println s!"record-refinement-scaling {label} small={small}ms large={large}ms"
  check s!"{label} scales linearly" (large ≤ 3 * small + 250)

/-- Rejects a record carrying many extra own keys, and pins the position it rejects at.

What this measures, exactly: the whole `inspectRecord` path at 10002 and 20002 own keys. The cost is
dominated by `ownPropertyKeys` materializing every own key, which no implementation of the key
comparison can avoid, so the timings bound absolute cost at that size and say nothing about the
comparison itself.

It deliberately does not claim to guard a quadratic key comparison. An earlier version did, naming a
per-extra-key search of the declared keys -- but that costs `extra * declared`, and `demoSchema`
declares two fields, so it is linear and a naive implementation passes the same envelope (measured:
35 ms and 53 ms against the committed 23 ms and 56 ms). Nor is the regression readily constructible:
this comparison must report the *first* difference, so any form of it short-circuits at the first
undeclared key, and a per-key membership search over an all-matching fixture was not distinguishable
from the streaming form at these sizes either. The functional guarantee is carried by
`Record.matchKeys_iff`, which proves the bounded check accepts exactly the declared sequence; that is
a theorem rather than a timing, and it is the thing worth relying on. -/
private def testBoundedRejection : IO Unit := do
  let small ← measureExtraKeyRejection 10000
  let large ← measureExtraKeyRejection 20000
  check "rejection is bounded by the actual own-key count" (large < 500)
  checkScaling "extra-key-rejection" small large

private def measureRoundtrip (count : Nat) : IO Unit := do
  let start ← IO.monoMsNow
  let mut heap := Heap.empty
  for index in List.range count do
    let (value, next) ←
      orFail "scale encode" (Record.encode demoSchema demoCodecs heap (index % 2 == 0, "", PUnit.unit))
    let decoded ← orFail "scale decode" (Record.decode demoSchema demoCodecs next value)
    check "the scale roundtrip returns the original record"
      (decide (decoded = ((index % 2 == 0), "", PUnit.unit)))
    heap := next
  let elapsed := (← IO.monoMsNow) - start
  IO.println s!"record-refinement-roundtrip records={count} totalMs={elapsed}"

private def testScale : IO Unit := do
  measureRoundtrip 2000

#eval testShapeFaultIdentity
#eval testDecodeFaultIdentity
#eval testEncodeGuardRoundtrip
#eval testSchemaRefusal
#eval testNestedRecords
#eval testBoundedRejection
#eval testScale

end TSLean.Refinement.Tests
