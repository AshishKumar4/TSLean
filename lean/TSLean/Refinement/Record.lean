import TSLean.Refinement.Core
import TSLean.Refinement.Evidence

namespace TSLean.Refinement

open TSLean.JS

namespace Record

universe u v w

/-- One declared field of a closed record: its own property key, the Lean type carried at that key,
and the refinement that type has in the heap. -/
structure FieldSpec : Type (u + 1) where
  key : JSString
  Carrier : Type u
  element : Refinement Carrier

/-- A closed record's declared fields, in declaration order. -/
abbrev Schema := List FieldSpec.{u}

/-- The Lean carrier of a closed record: one component per declared field, in declaration order. A
schema with no field carries no information, so its carrier is `PUnit`. -/
def Native : Schema.{u} → Type u
  | [] => PUnit
  | spec :: rest => spec.Carrier × Native rest

/-- The declared field keys, in declaration order. -/
def fieldKeys (schema : Schema.{u}) : List JSString := schema.map (·.key)

/-- The exact own property keys a closed record presents, in declaration order. -/
def ownKeys (schema : Schema.{u}) : List PropertyKey := (fieldKeys schema).map .string

/-- One codec per declared field, in declaration order. Every field codec reports the same fault
types so that a record fault can name the failing field without erasing its cause. -/
def Codecs (FieldEncodeFault : Type v) (FieldDecodeFault : Type w) :
    Schema.{u} → Type (max u v w)
  | [] => PUnit
  | spec :: rest =>
      Codec spec.Carrier FieldEncodeFault FieldDecodeFault spec.element ×
        Codecs FieldEncodeFault FieldDecodeFault rest

/-- Every field codec decodes its own refinement relation completely. This is the composable half of
lawfulness, exactly as `Codec.Complete` is for a single carrier. -/
def Codecs.Complete {FieldEncodeFault : Type v} {FieldDecodeFault : Type w} :
    (schema : Schema.{u}) → Codecs FieldEncodeFault FieldDecodeFault schema → Prop
  | [], _ => True
  | _ :: rest, codecs => codecs.1.Complete ∧ Codecs.Complete rest codecs.2

/-- Every field codec is lawful. Only the encode-side totality results ask for this. -/
def Codecs.Lawful {FieldEncodeFault : Type v} {FieldDecodeFault : Type w} :
    (schema : Schema.{u}) → Codecs FieldEncodeFault FieldDecodeFault schema → Prop
  | [], _ => True
  | _ :: rest, codecs => LawfulCodec codecs.1 ∧ Codecs.Lawful rest codecs.2

/-- Every field's refinement decodes each JavaScript value to at most one native value. -/
def UniqueFields : Schema.{u} → Prop
  | [] => True
  | spec :: rest => spec.element.UniqueDecode ∧ UniqueFields rest

private theorem nodup_of_map {α β : Type _} (f : α → β) :
    ∀ (values : List α), (values.map f).Nodup → values.Nodup
  | [], _ => by simp
  | head :: tail, nodup => by
      rw [List.map_cons, List.nodup_cons] at nodup
      exact List.nodup_cons.mpr
        ⟨fun member => nodup.1 (List.mem_map_of_mem member), nodup_of_map f tail nodup.2⟩

/-- Relabels a field codec's typed faults. Every field codec in one schema reports the same fault
types while each carrier's committed codec has its own, so listing `Bool.codec` beside `String.codec`
in one schema needs exactly this adapter: the relabelled codec runs the original and renames its
faults, so it carries the original's soundness proofs unchanged. -/
def relabel {α : Type u} {FieldEncodeFault FieldEncodeLabel : Type v}
    {FieldDecodeFault FieldDecodeLabel : Type w} {element : Refinement α}
    (codec : Codec α FieldEncodeFault FieldDecodeFault element)
    (encodeLabel : FieldEncodeFault → FieldEncodeLabel)
    (decodeLabel : FieldDecodeFault → FieldDecodeLabel) :
    Codec α FieldEncodeLabel FieldDecodeLabel element where
  encode heap native := (codec.encode heap native).mapError encodeLabel
  decode heap value := (codec.decode heap value).mapError decodeLabel
  encode_sound := by
    intro old native value next valid encoded
    refine codec.encode_sound valid ?_
    cases result : codec.encode old native with
    | error fault =>
        rw [result] at encoded
        exact absurd encoded (by simp [Except.mapError])
    | ok produced =>
        rw [result] at encoded
        simpa [Except.mapError] using encoded
  decode_sound := by
    intro heap value native decoded
    refine codec.decode_sound ?_
    cases result : codec.decode heap value with
    | error fault =>
        rw [result] at decoded
        exact absurd decoded (by simp [Except.mapError])
    | ok produced =>
        rw [result] at decoded
        simpa [Except.mapError] using decoded

/-- Relabelling faults preserves decode completeness. -/
theorem relabel_complete {α : Type u} {FieldEncodeFault FieldEncodeLabel : Type v}
    {FieldDecodeFault FieldDecodeLabel : Type w} {element : Refinement α}
    {codec : Codec α FieldEncodeFault FieldDecodeFault element} (complete : codec.Complete)
    (encodeLabel : FieldEncodeFault → FieldEncodeLabel)
    (decodeLabel : FieldDecodeFault → FieldDecodeLabel) :
    (relabel codec encodeLabel decodeLabel).Complete := by
  intro heap native value related
  change (codec.decode heap value).mapError decodeLabel = .ok native
  rw [complete related]
  rfl

/-- Relabelling faults preserves codec lawfulness. -/
theorem relabel_lawful {α : Type u} {FieldEncodeFault FieldEncodeLabel : Type v}
    {FieldDecodeFault FieldDecodeLabel : Type w} {element : Refinement α}
    {codec : Codec α FieldEncodeFault FieldDecodeFault element} (lawful : LawfulCodec codec)
    (encodeLabel : FieldEncodeFault → FieldEncodeLabel)
    (decodeLabel : FieldDecodeFault → FieldDecodeLabel) :
    LawfulCodec (relabel codec encodeLabel decodeLabel) where
  encode_total heap native valid := by
    obtain ⟨value, next, encoded⟩ := lawful.encode_total heap native valid
    refine ⟨value, next, ?_⟩
    change (codec.encode heap native).mapError encodeLabel = .ok (value, next)
    rw [encoded]
    rfl
  complete := relabel_complete lawful.complete encodeLabel decodeLabel

/-! ## Bounded own-key validation -/

/-- Typed differences between an object's own keys and a schema's declared field keys. -/
inductive KeyFault where
  | missingKey (index : Nat) (expected : JSString)
  | extraKey (index : Nat) (actual : PropertyKey)
  | keyMismatch (index : Nat) (expected : JSString) (actual : PropertyKey)
  deriving DecidableEq

private def matchKeysFrom (index : Nat) :
    List JSString → List PropertyKey → Except KeyFault Unit
  | [], [] => .ok ()
  | [], actual :: _ => .error (.extraKey index actual)
  | expected :: _, [] => .error (.missingKey index expected)
  | expected :: restExpected, actual :: restActual =>
      if actual == .string expected then matchKeysFrom (index + 1) restExpected restActual
      else .error (.keyMismatch index expected actual)

/-- Decides `actual = declared.map .string` in one pass, stopping at the first difference and naming
it. Comparison is ECMAScript property-key equality (UTF-16 code units, or symbol identity), never
Lean structural equality on a heap representation.

The declared sequence is fixed by the record's own type, so unlike a dense array's declared length it
is not attacker-controlled; the quantity a caller *can* inflate is the object's actual own-key count.
Walking both sequences together keeps the comparison proportional to that count and stops at the
first difference, so an object carrying a million extra keys is rejected after one mismatch instead
of by a membership test against every declared key. -/
def matchKeys (declared : List JSString) (actual : List PropertyKey) : Except KeyFault Unit :=
  matchKeysFrom 0 declared actual

private theorem matchKeysFrom_iff (index : Nat) (declared : List JSString)
    (actual : List PropertyKey) :
    matchKeysFrom index declared actual = .ok () ↔ actual = declared.map .string := by
  induction declared generalizing index actual with
  | nil => cases actual <;> simp [matchKeysFrom]
  | cons expected restExpected ih =>
      cases actual with
      | nil => simp [matchKeysFrom]
      | cons actual restActual =>
          by_cases equal : actual = .string expected
          · subst equal
            simp [matchKeysFrom, ih]
          · simp [matchKeysFrom, equal]

/-- The streamed key comparison accepts exactly the declared own-key sequence. -/
theorem matchKeys_iff (declared : List JSString) (actual : List PropertyKey) :
    matchKeys declared actual = .ok () ↔ actual = declared.map .string :=
  matchKeysFrom_iff 0 declared actual

/-! ## Schema validity -/

/-- Typed reasons a declared field-key sequence cannot be an ECMAScript own-key sequence. -/
inductive SchemaFault where
  | duplicateKey (index : Nat) (key : JSString)
  | indexLikeKey (index : Nat) (key : JSString) (parsed : Nat)
  deriving DecidableEq

private def validateKeysFrom (index : Nat) : List JSString → Except SchemaFault Unit
  | [] => .ok ()
  | key :: rest =>
      match PropertyKey.arrayIndex? key with
      | some parsed => .error (.indexLikeKey index key parsed)
      | none =>
          if rest.any (fun other => other == key) then .error (.duplicateKey index key)
          else validateKeysFrom (index + 1) rest

/-- Declared keys that ECMAScript own-key order can present in declaration order: pairwise distinct,
and none of them an array index.

Both conditions are forced by the model rather than chosen. A well-formed heap answers an ordinary
object's own keys without repetition (`Heap.ordinary_ownPropertyKeys_nodup`), which
`nodup_of_related` turns into the statement that a repeated declared key has no
related value at all. Integer-index keys are hoisted ahead of every other string key in own-key
order, so a schema declaring one cannot in general be read back in declaration order; this slice
refuses every index-like key rather than modelling that hoisting, which also refuses the orders that
would have been presentable. -/
def ValidKeys (declared : List JSString) : Prop :=
  declared.Nodup ∧ ∀ key ∈ declared, PropertyKey.arrayIndex? key = none

private theorem mem_of_any_beq {declared : List JSString} {key : JSString}
    (duplicate : declared.any (fun other => other == key) = true) : key ∈ declared := by
  obtain ⟨other, member, equal⟩ := List.any_eq_true.mp duplicate
  exact beq_iff_eq.mp equal ▸ member

private theorem any_beq_of_mem {declared : List JSString} {key : JSString}
    (member : key ∈ declared) : declared.any (fun other => other == key) = true :=
  List.any_eq_true.mpr ⟨key, member, beq_iff_eq.mpr rfl⟩

private theorem validateKeysFrom_iff (index : Nat) (declared : List JSString) :
    validateKeysFrom index declared = .ok () ↔ ValidKeys declared := by
  induction declared generalizing index with
  | nil => simp [validateKeysFrom, ValidKeys]
  | cons key rest ih =>
      unfold validateKeysFrom
      cases parsed : PropertyKey.arrayIndex? key with
      | some value =>
          constructor
          · intro impossible
            exact absurd impossible (by simp)
          · intro valid
            exact absurd (valid.2 key (by simp)) (by simp [parsed])
      | none =>
          by_cases duplicate : rest.any (fun other => other == key) = true
          · rw [if_pos duplicate]
            constructor
            · intro impossible
              exact absurd impossible (by simp)
            · intro valid
              exact absurd (mem_of_any_beq duplicate) (List.nodup_cons.mp valid.1).1
          · rw [if_neg duplicate, ih]
            constructor
            · intro valid
              refine ⟨List.nodup_cons.mpr ⟨fun member => duplicate (any_beq_of_mem member),
                valid.1⟩, ?_⟩
              intro other member
              rcases List.mem_cons.mp member with rfl | member
              · exact parsed
              · exact valid.2 other member
            · intro valid
              exact ⟨(List.nodup_cons.mp valid.1).2,
                fun other member => valid.2 other (List.mem_cons.mpr (Or.inr member))⟩

/-- Executable schema validation, bounded by the declared field count. -/
def validateKeys (declared : List JSString) : Except SchemaFault Unit := validateKeysFrom 0 declared

/-- Executable schema validation accepts exactly the presentable declared key sequences. -/
theorem validateKeys_iff (declared : List JSString) :
    validateKeys declared = .ok () ↔ ValidKeys declared :=
  validateKeysFrom_iff 0 declared

/-! ## The observable record shape -/

/-- Typed failures produced while validating the closed-record boundary. -/
inductive ShapeFault where
  | expectedObject
  | invalidRef (ref : RefId)
  | wrongKind (actual : ObjectKindTag)
  | wrongPrototype (actual : RefId)
  | notExtensible
  | keys (fault : KeyFault)
  | malformedField (index : Nat) (key : JSString)
  deriving DecidableEq

/-- Reads each declared field as an exact standard data descriptor. Every other own-property
observation at that key, including absence and any accessor, is reported as one malformed field
naming both its position and its key. -/
private def readFields (heap : Heap) (root : RefId) (index : Nat) :
    List JSString → Except ShapeFault (List Value)
  | [] => .ok []
  | key :: rest =>
      match heap.getOwnProperty root (.string key) with
      | .ok (some (.data ⟨value, true, true, true⟩)) =>
          match readFields heap root (index + 1) rest with
          | .error fault => .error fault
          | .ok values => .ok (value :: values)
      | _ => .error (.malformedField index key)

/-- Validates and materializes only the exact closed-record shape this refinement accepts: an
extensible ordinary object with a null prototype whose own keys are exactly the declared field keys
in declaration order, each carrying a standard data descriptor.

The prototype is pinned at null and extensibility at `true` for the same reason the dense-array slice
pins them. A null prototype is the only observation that rules out *inherited* properties outright,
so "no extra keys" can be checked instead of assumed; and `preventExtensions` is irreversible in the
model, so accepting a non-extensible object would accept a value this codec's own encoder can never
produce. Both are decided here, never assumed.

Every step costs the object's actual own-key count: the key check streams against the declared
sequence, and the per-field reads are bounded by the record's own type. -/
def inspectRecord (declared : List JSString) (heap : Heap) (value : Value) :
    Except ShapeFault (RefId × List Value) := do
  let root ← match value with
    | .object ref => pure ref
    | .primitive _ => throw .expectedObject
  let object ← match heap.get? root with
    | .ok object => pure object
    | .error _ => throw (.invalidRef root)
  match object.kind with
    | .ordinary => pure ()
    | actual => throw (.wrongKind actual.tag)
  match object.prototype with
    | some prototype => throw (.wrongPrototype prototype)
    | none => pure ()
  if !object.extensible then throw .notExtensible
  -- `ownPropertyKeys` reads through the same `get?` that already succeeded above for this heap and
  -- root, so its failure branch is unreachable; it repeats that read's fault rather than invent one.
  let keys ← match heap.ownPropertyKeys root with
    | .ok keys => pure keys
    | .error _ => throw (.invalidRef root)
  match matchKeys declared keys with
    | .error fault => throw (.keys fault)
    | .ok () => pure ()
  let values ← readFields heap root 0 declared
  pure (root, values)

/-- The observable shape this refinement accepts, stated in ECMAScript observations rather than as
"the checker returned ok": one extensible ordinary object with a null prototype whose own keys are
exactly the declared field keys and whose every declared key carries a standard data descriptor. -/
def RecordShape (declared : List JSString) (heap : Heap) (value : Value) : Prop :=
  ∃ root object,
    value = .object root ∧
    heap.get? root = .ok object ∧
    object.kind = .ordinary ∧
    object.prototype = none ∧
    object.extensible = true ∧
    heap.ownPropertyKeys root = .ok (declared.map .string) ∧
    ∀ key ∈ declared, ∃ encoded,
      heap.getOwnProperty root (.string key) = .ok (some (.data ⟨encoded, true, true, true⟩))

private theorem readFields_sound (heap : Heap) (root : RefId) :
    ∀ (index : Nat) (declared : List JSString) (values : List Value),
      readFields heap root index declared = .ok values →
      values.length = declared.length ∧
      (∀ pair ∈ declared.zip values, heap.getOwnProperty root (.string pair.1) =
        .ok (some (.data ⟨pair.2, true, true, true⟩))) ∧
      ∀ key ∈ declared, ∃ encoded, heap.getOwnProperty root (.string key) =
        .ok (some (.data ⟨encoded, true, true, true⟩))
  | _, [], values, read => by
      simp only [readFields, Except.ok.injEq] at read
      subst read
      exact ⟨rfl, by simp, by simp⟩
  | index, key :: rest, values, read => by
      unfold readFields at read
      split at read
      · rename_i element found
        split at read
        · exact absurd read (by simp)
        · rename_i restValues restRead
          simp only [Except.ok.injEq] at read
          subst read
          obtain ⟨length, descriptors, fields⟩ :=
            readFields_sound heap root (index + 1) rest restValues restRead
          refine ⟨by simp [length], ?_, ?_⟩
          · intro pair member
            rw [List.zip_cons_cons, List.mem_cons] at member
            rcases member with rfl | member
            · simpa using found
            · exact descriptors pair member
          · intro other member
            rw [List.mem_cons] at member
            rcases member with rfl | member
            · exact ⟨element, by simpa using found⟩
            · exact fields other member
      · exact absurd read (by simp)

private theorem readFields_complete (heap : Heap) (root : RefId) :
    ∀ (index : Nat) (declared : List JSString),
      (∀ key ∈ declared, ∃ encoded, heap.getOwnProperty root (.string key) =
        .ok (some (.data ⟨encoded, true, true, true⟩))) →
      ∃ values, readFields heap root index declared = .ok values
  | _, [], _ => ⟨[], rfl⟩
  | index, key :: rest, present => by
      obtain ⟨encoded, found⟩ := present key (by simp)
      obtain ⟨values, read⟩ :=
        readFields_complete heap root (index + 1) rest
          (fun other member => present other (by simp [member]))
      exact ⟨encoded :: values, by unfold readFields; rw [found, read]⟩

/-- A successful inspection returns the inspected object's exact declared field values. -/
theorem inspectRecord_sound {declared : List JSString} {heap : Heap} {value : Value} {root : RefId}
    {values : List Value} (inspected : inspectRecord declared heap value = .ok (root, values)) :
    ∃ object,
      value = .object root ∧
      heap.get? root = .ok object ∧
      object.kind = .ordinary ∧
      object.prototype = none ∧
      object.extensible = true ∧
      heap.ownPropertyKeys root = .ok (declared.map .string) ∧
      values.length = declared.length ∧
      (∀ pair ∈ declared.zip values, heap.getOwnProperty root (.string pair.1) =
        .ok (some (.data ⟨pair.2, true, true, true⟩))) ∧
      ∀ key ∈ declared, ∃ encoded, heap.getOwnProperty root (.string key) =
        .ok (some (.data ⟨encoded, true, true, true⟩)) := by
  cases value with
  | primitive primitive => simp [inspectRecord, Bind.bind, Except.bind] at inspected
  | object ref =>
      unfold inspectRecord at inspected
      simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at inspected
      split at inspected <;> try (simp at inspected; done)
      rename_i object found
      split at inspected <;> try (simp at inspected; done)
      rename_i kindEq
      split at inspected <;> try (simp at inspected; done)
      rename_i prototypeEq
      split at inspected <;> try (simp at inspected; done)
      rename_i notExtensible
      split at inspected <;> try (simp at inspected; done)
      rename_i keys keysEq
      split at inspected <;> try (simp at inspected; done)
      rename_i matched
      split at inspected <;> try (simp at inspected; done)
      rename_i readValues read
      simp only [Except.ok.injEq, Prod.mk.injEq] at inspected
      obtain ⟨rootEq, valuesEq⟩ := inspected
      subst rootEq
      subst valuesEq
      obtain ⟨length, descriptors, fields⟩ := readFields_sound heap ref 0 declared readValues read
      refine ⟨object, rfl, found, kindEq, prototypeEq, by simpa using notExtensible, ?_, length,
        descriptors, fields⟩
      rw [keysEq]
      exact congrArg Except.ok ((matchKeys_iff declared keys).mp matched)

/-- Every value with the accepted shape is inspected successfully. -/
theorem inspectRecord_complete {declared : List JSString} {heap : Heap} {value : Value}
    (shape : RecordShape declared heap value) :
    ∃ root values, inspectRecord declared heap value = .ok (root, values) := by
  obtain ⟨root, object, rfl, found, kindEq, prototypeEq, extensibleEq, keysEq, fields⟩ := shape
  obtain ⟨values, read⟩ := readFields_complete heap root 0 declared fields
  have matched : matchKeys declared (declared.map .string) = .ok () :=
    (matchKeys_iff declared (declared.map .string)).mpr rfl
  refine ⟨root, values, ?_⟩
  simp [inspectRecord, Bind.bind, Except.bind, Pure.pure, Except.pure, found, kindEq, prototypeEq,
    extensibleEq, keysEq, matched, read]

/-- Executable eligibility guard for the exact closed-record shape.

Passing this guard proves the shape and nothing more. It does not produce a Lean record: no shape
check can, because the fields' Lean values are the field codecs' output, not an observation of the
object. The typed witness comes from the decoder, where `decode_sound` produces the relation and
`decode_exact` makes it exact. -/
def recordShapeGuard (declared : List JSString) (heap : Heap) :
    Guard Value (RecordShape declared heap) :=
  Guard.create "exact closed record shape" (by decide)
    (fun value => (inspectRecord declared heap value).isOk)
    (fun value accepted => by
      cases inspected : inspectRecord declared heap value with
      | error fault =>
          change (inspectRecord declared heap value).isOk = true at accepted
          rw [inspected] at accepted
          contradiction
      | ok result =>
          rcases result with ⟨root, values⟩
          obtain ⟨object, valueEq, found, kindEq, prototypeEq, extensibleEq, keysEq, _, _, fields⟩ :=
            inspectRecord_sound inspected
          exact ⟨root, object, valueEq, found, kindEq, prototypeEq, extensibleEq, keysEq, fields⟩)

/-- Passing the record guard proves the value really has the accepted ECMAScript shape. -/
theorem recordShapeGuard_sound (declared : List JSString) (heap : Heap) (value : Value)
    (accepted : (recordShapeGuard declared heap).check value = true) :
    RecordShape declared heap value :=
  (recordShapeGuard declared heap).sound value accepted

/-- Every value with the accepted shape passes the executable guard. -/
theorem recordShapeGuard_complete (declared : List JSString) (heap : Heap) (value : Value)
    (shape : RecordShape declared heap value) :
    (recordShapeGuard declared heap).check value = true := by
  obtain ⟨root, values, inspected⟩ := inspectRecord_complete shape
  change (inspectRecord declared heap value).isOk = true
  rw [inspected]
  rfl

/-! ## The refinement relation -/

/-- Every declared field is an own standard data descriptor whose value satisfies that field's own
element refinement. -/
def FieldsRel : (schema : Schema.{u}) → Heap → RefId → Native schema → Prop
  | [], _, _, _ => True
  | spec :: rest, heap, root, native =>
      (∃ encoded, heap.getOwnProperty root (.string spec.key) =
          .ok (some (.data ⟨encoded, true, true, true⟩)) ∧
        spec.element.Rel heap native.1 encoded) ∧
      FieldsRel rest heap root native.2

/-- The declared field values, in declaration order, each refining its own field. -/
def FieldsMatch : (schema : Schema.{u}) → Heap → Native schema → List Value → Prop
  | [], _, _, _ => True
  | _ :: _, _, _, [] => False
  | spec :: rest, heap, native, value :: values =>
      spec.element.Rel heap native.1 value ∧ FieldsMatch rest heap native.2 values

/-- A Lean record is represented by one ordinary ECMAScript object with a null prototype whose own
keys are exactly the declared field keys in declaration order. This is structural correspondence
only: heap well-formedness is a hypothesis of the theorems that need it, never part of the
relation. -/
def RecordRel (schema : Schema.{u}) (heap : Heap) (native : Native schema) (value : Value) : Prop :=
  ∃ root object,
    value = .object root ∧
    heap.get? root = .ok object ∧
    object.kind = .ordinary ∧
    object.prototype = none ∧
    object.extensible = true ∧
    heap.ownPropertyKeys root = .ok (ownKeys schema) ∧
    FieldsRel schema heap root native

/-- A record relation always points at a valid root reference. -/
theorem RecordRel.root_valueValid {schema : Schema.{u}} {heap : Heap} {native : Native schema}
    {value : Value} (related : RecordRel schema heap native value) :
    heap.valueValid value = true := by
  obtain ⟨root, object, rfl, found, _⟩ := related
  exact decide_eq_true (Heap.get?_ok_valid heap root object found)

/-- Every declared field of a related record answers a standard data descriptor whose value is valid
in the same heap. -/
private theorem fieldsRel_fields : ∀ (schema : Schema.{u}) (heap : Heap) (root : RefId)
    (native : Native schema), FieldsRel schema heap root native →
    ∀ key ∈ fieldKeys schema, ∃ encoded,
      heap.getOwnProperty root (.string key) = .ok (some (.data ⟨encoded, true, true, true⟩)) ∧
      heap.valueValid encoded = true
  | [], _, _, _, _, key, member => by simp [fieldKeys] at member
  | spec :: rest, heap, root, native, related, key, member => by
      rw [fieldKeys, List.map_cons, List.mem_cons] at member
      rcases member with rfl | member
      · obtain ⟨⟨encoded, found, elementRelated⟩, _⟩ := related
        exact ⟨encoded, found, spec.element.valueValid elementRelated⟩
      · exact fieldsRel_fields rest heap root native.2 related.2 key (by simpa [fieldKeys] using member)

/-- Every field value stored by a related record is valid in the same heap. -/
theorem RecordRel.field_valueValid {schema : Schema.{u}} {heap : Heap} {native : Native schema}
    {value : Value} (related : RecordRel schema heap native value) (key : JSString)
    (declared : key ∈ fieldKeys schema) :
    ∃ root encoded,
      value = .object root ∧
      heap.getOwnProperty root (.string key) = .ok (some (.data ⟨encoded, true, true, true⟩)) ∧
      heap.valueValid encoded = true := by
  obtain ⟨root, object, valueEq, found, kindEq, prototypeEq, extensibleEq, keysEq, fields⟩ := related
  obtain ⟨encoded, descriptor, valid⟩ := fieldsRel_fields schema heap root native fields key declared
  exact ⟨root, encoded, valueEq, descriptor, valid⟩

/-- Every related value really has the ECMAScript shape the guard decides. -/
theorem RecordRel.recordShape {schema : Schema.{u}} {heap : Heap} {native : Native schema}
    {value : Value} (related : RecordRel schema heap native value) :
    RecordShape (fieldKeys schema) heap value := by
  obtain ⟨root, object, valueEq, found, kindEq, prototypeEq, extensibleEq, keysEq, fields⟩ := related
  refine ⟨root, object, valueEq, found, kindEq, prototypeEq, extensibleEq, keysEq, ?_⟩
  intro key member
  obtain ⟨encoded, descriptor, _⟩ := fieldsRel_fields schema heap root native fields key member
  exact ⟨encoded, descriptor⟩

/-- The declared own-key sequence of a related record is exactly its schema's. -/
theorem ownPropertyKeys_commutes {schema : Schema.{u}} {heap : Heap} {native : Native schema}
    {value : Value} (related : RecordRel schema heap native value) :
    ∃ root, value = .object root ∧ heap.ownPropertyKeys root = .ok (ownKeys schema) := by
  obtain ⟨root, object, valueEq, found, kindEq, prototypeEq, extensibleEq, keysEq, fields⟩ := related
  exact ⟨root, valueEq, keysEq⟩

/-- Reading the first declared key of a related record returns a value refining exactly that field,
and leaves the remaining declared fields related to the same object. Iterating it reaches every
field, so this is the complete own-key read correspondence without a positional accessor into the
record's carrier. -/
theorem getOwnProperty_commutes {spec : FieldSpec.{u}} {rest : Schema.{u}} {heap : Heap}
    {native : Native (spec :: rest)} {value : Value}
    (related : RecordRel (spec :: rest) heap native value) :
    ∃ root encoded,
      value = .object root ∧
      heap.getOwnProperty root (.string spec.key) =
        .ok (some (.data ⟨encoded, true, true, true⟩)) ∧
      spec.element.Rel heap native.1 encoded ∧
      FieldsRel rest heap root native.2 := by
  obtain ⟨root, object, valueEq, found, kindEq, prototypeEq, extensibleEq, keysEq, fields⟩ := related
  obtain ⟨⟨encoded, descriptor, elementRelated⟩, restFields⟩ := fields
  exact ⟨root, encoded, valueEq, descriptor, elementRelated, restFields⟩

private theorem fieldsRel_stable : ∀ (schema : Schema.{u}) (old next : Heap) (root : RefId)
    (object : ObjectRecord) (native : Native schema), Heap.ExactExtension old next →
    old.get? root = .ok object → FieldsRel schema old root native →
    FieldsRel schema next root native
  | [], _, _, _, _, _, _, _, _ => trivial
  | spec :: rest, old, next, root, object, native, extension, found, related => by
      obtain ⟨⟨encoded, descriptor, elementRelated⟩, restRelated⟩ := related
      refine ⟨⟨encoded, ?_, spec.element.stable extension elementRelated⟩,
        fieldsRel_stable rest old next root object native.2 extension found restRelated⟩
      rw [extension.preserves_getOwnProperty root object found]
      exact descriptor

/-- Exact heap extension preserves an immutable closed-record snapshot. -/
theorem RecordRel.stable {schema : Schema.{u}} {old next : Heap} {native : Native schema}
    {value : Value} (extension : Heap.ExactExtension old next)
    (related : RecordRel schema old native value) : RecordRel schema next native value := by
  obtain ⟨root, object, valueEq, found, kindEq, prototypeEq, extensibleEq, keysEq, fields⟩ := related
  refine ⟨root, object, valueEq, extension.get_eq root object found, kindEq, prototypeEq,
    extensibleEq, ?_, fieldsRel_stable schema old next root object native extension found fields⟩
  rw [extension.preserves_ownPropertyKeys root object found]
  exact keysEq

/-- Immutable snapshot refinement for closed records: one ordinary ECMAScript object with a null
prototype carrying exactly the declared fields, as `RecordRel` spells out. -/
def refinement (schema : Schema.{u}) : Refinement (Native schema) where
  Rel := RecordRel schema
  valueValid := RecordRel.root_valueValid
  stable := RecordRel.stable

private theorem fieldsRel_unique : ∀ (schema : Schema.{u}) (heap : Heap) (root : RefId)
    (left right : Native schema), UniqueFields schema → FieldsRel schema heap root left →
    FieldsRel schema heap root right → left = right
  | [], _, _, left, right, _, _, _ => rfl
  | spec :: rest, heap, root, left, right, unique, leftRelated, rightRelated => by
      obtain ⟨⟨leftEncoded, leftFound, leftElement⟩, leftRest⟩ := leftRelated
      obtain ⟨⟨rightEncoded, rightFound, rightElement⟩, rightRest⟩ := rightRelated
      rw [leftFound] at rightFound
      have encodedEq : leftEncoded = rightEncoded := by
        have descriptorsEqual :=
          PropertyDescriptor.data.inj (Option.some.inj (Except.ok.inj rightFound))
        cases descriptorsEqual
        rfl
      subst encodedEq
      have headEq : left.1 = right.1 := unique.1 leftElement rightElement
      have tailEq : left.2 = right.2 :=
        fieldsRel_unique rest heap root left.2 right.2 unique.2 leftRest rightRest
      exact Prod.ext headEq tailEq

/-- Closed-record snapshots decode uniquely when every field does. -/
theorem refinement_uniqueDecode {schema : Schema.{u}} (unique : UniqueFields schema) :
    (refinement schema).UniqueDecode := by
  intro heap left right value leftRelated rightRelated
  obtain ⟨leftRoot, leftObject, leftValueEq, leftFound, _, _, _, _, leftFields⟩ := leftRelated
  obtain ⟨rightRoot, rightObject, rightValueEq, rightFound, _, _, _, _, rightFields⟩ := rightRelated
  have rootsEqual : leftRoot = rightRoot := by
    rw [leftValueEq] at rightValueEq
    exact Value.object.inj rightValueEq
  subst rootsEqual
  exact fieldsRel_unique schema heap leftRoot left right unique leftFields rightFields

/-- A repeated declared key has no related value in a well-formed heap: the heap answers an ordinary
object's own keys without repetition, so a repeated key can never be an own-key sequence. This is why
the encoder refuses such a schema instead of allocating an object that merely looks close. -/
theorem nodup_of_related {schema : Schema.{u}} {heap : Heap}
    {native : Native schema} {value : Value} (valid : heap.WellFormed)
    (related : RecordRel schema heap native value) : (fieldKeys schema).Nodup := by
  obtain ⟨root, object, valueEq, found, kindEq, prototypeEq, extensibleEq, keysEq, fields⟩ := related
  refine nodup_of_map PropertyKey.string (fieldKeys schema) ?_
  exact Heap.ordinary_ownPropertyKeys_nodup heap root object (ownKeys schema) valid found kindEq
    keysEq

/-! ## The codec -/

variable {FieldEncodeFault : Type v} {FieldDecodeFault : Type w}

/-- Record-level encoding failures.

`invalidSchema` is pinned by `encode_invalidSchema`. `field` carries the failing field's position and
its own codec's fault; it is unreachable for every field codec committed in this repository — `Bool`,
`BigInt`, `String` and `Float` all encode with `Empty` faults — but it stays because the field codecs
are a parameter, not a fixed set. `allocation` and `rejected` cannot fire for a valid schema in a
well-formed heap, which is what `encode_total` establishes: a fresh extensible ordinary object with a
null prototype accepts each declared key exactly once. -/
inductive EncodeFault (FieldEncodeFault : Type v) where
  | invalidSchema (fault : SchemaFault)
  | field (index : Nat) (fault : FieldEncodeFault)
  | allocation (fault : DefinePropertyFault)
  | rejected (index : Nat) (key : JSString)
  deriving DecidableEq

/-- Record-level decoding distinguishes shape rejection from field rejection. -/
inductive DecodeFault (FieldDecodeFault : Type w) where
  | shape (fault : ShapeFault)
  | field (index : Nat) (fault : FieldDecodeFault)
  deriving DecidableEq

private def encodeFields : (schema : Schema.{u}) →
    Codecs FieldEncodeFault FieldDecodeFault schema → Native schema → Nat → Heap →
    Except (EncodeFault FieldEncodeFault) (List Value × Heap)
  | [], _, _, _, heap => .ok ([], heap)
  | _ :: rest, codecs, native, index, heap =>
      match codecs.1.encode heap native.1 with
      | .error fault => .error (.field index fault)
      | .ok (value, middle) =>
          match encodeFields rest codecs.2 native.2 (index + 1) middle with
          | .error fault => .error fault
          | .ok (values, next) => .ok (value :: values, next)

private theorem fieldsMatch_stable : ∀ (schema : Schema.{u}) (old next : Heap)
    (native : Native schema) (values : List Value), Heap.ExactExtension old next →
    FieldsMatch schema old native values → FieldsMatch schema next native values
  | [], _, _, _, _, _, _ => trivial
  | spec :: rest, old, next, native, values, extension, matched => by
      cases values with
      | nil => exact absurd matched (by simp [FieldsMatch])
      | cons value restValues =>
          exact ⟨spec.element.stable extension matched.1,
            fieldsMatch_stable rest old next native.2 restValues extension matched.2⟩

/-- Sequential field encoding threads one exact extension through the whole declared field list: the
final heap extends the initial one, every field already encoded stays related in it, and every
encoded value is valid there. -/
private theorem encodeFields_sound : ∀ (schema : Schema.{u})
    (codecs : Codecs FieldEncodeFault FieldDecodeFault schema) (native : Native schema)
    (index : Nat) (heap : Heap) (values : List Value) (next : Heap), heap.WellFormed →
    encodeFields schema codecs native index heap = .ok (values, next) →
    Heap.ExactExtension heap next ∧ values.length = schema.length ∧
      FieldsMatch schema next native values ∧ ∀ value ∈ values, next.valueValid value = true
  | [], _, _, _, heap, values, next, valid, encoded => by
      simp only [encodeFields, Except.ok.injEq, Prod.mk.injEq] at encoded
      obtain ⟨rfl, rfl⟩ := encoded
      exact ⟨Heap.ExactExtension.refl heap valid, rfl, trivial, by simp⟩
  | spec :: rest, codecs, native, index, heap, values, next, valid, encoded => by
      unfold encodeFields at encoded
      split at encoded
      · exact absurd encoded (by simp)
      · rename_i value middle fieldEncoded
        split at encoded
        · exact absurd encoded (by simp)
        · rename_i restValues restNext restEncoded
          simp only [Except.ok.injEq, Prod.mk.injEq] at encoded
          obtain ⟨rfl, rfl⟩ := encoded
          obtain ⟨fieldExtension, fieldRelated⟩ := codecs.1.encode_sound valid fieldEncoded
          obtain ⟨extension, length, matched, valuesValid⟩ :=
            encodeFields_sound rest codecs.2 native.2 (index + 1) middle restValues restNext
              fieldExtension.nextWellFormed restEncoded
          have headRelated := spec.element.stable extension fieldRelated
          refine ⟨fieldExtension.trans extension, by simp [length], ⟨headRelated, matched⟩, ?_⟩
          intro other member
          rcases List.mem_cons.mp member with rfl | member
          · exact spec.element.valueValid headRelated
          · exact valuesValid other member

private theorem encodeFields_total : ∀ (schema : Schema.{u})
    (codecs : Codecs FieldEncodeFault FieldDecodeFault schema), Codecs.Lawful schema codecs →
    ∀ (native : Native schema) (index : Nat) (heap : Heap), heap.WellFormed →
    ∃ values next, encodeFields schema codecs native index heap = .ok (values, next)
  | [], _, _, _, _, heap, _ => ⟨[], heap, rfl⟩
  | spec :: rest, codecs, lawful, native, index, heap, valid => by
      obtain ⟨value, middle, fieldEncoded⟩ := lawful.1.encode_total heap native.1 valid
      obtain ⟨extension, _⟩ := codecs.1.encode_sound valid fieldEncoded
      obtain ⟨values, next, restEncoded⟩ :=
        encodeFields_total rest codecs.2 lawful.2 native.2 (index + 1) middle
          extension.nextWellFormed
      exact ⟨value :: values, next, by simp only [encodeFields, fieldEncoded, restEncoded]⟩

/-- A record under construction: the root is an extensible ordinary object with a null prototype
whose own keys are exactly the fields defined so far, each carrying its exact standard data
descriptor. -/
private def Built (heap : Heap) (root : RefId) (fields : List (JSString × Value)) : Prop :=
  (∃ object, heap.get? root = .ok object ∧ object.kind = .ordinary ∧
    object.prototype = none ∧ object.extensible = true) ∧
  heap.ownPropertyKeys root = .ok (fields.map fun field => .string field.1) ∧
  ∀ field ∈ fields, heap.getOwnProperty root (.string field.1) =
    .ok (some (.data ⟨field.2, true, true, true⟩))

private def defineFields (root : RefId) (index : Nat) :
    List (JSString × Value) → Heap → Except (EncodeFault FieldEncodeFault) Heap
  | [], heap => .ok heap
  | field :: rest, heap =>
      match heap.createDataProperty root (.string field.1) field.2 with
      | .error fault => .error (.allocation fault)
      | .ok (false, _) => .error (.rejected index field.1)
      | .ok (true, next) => defineFields root (index + 1) rest next

private theorem string_not_mem_of_key_not_mem {fields : List (JSString × Value)} {key : JSString}
    (absent : key ∉ fields.map (·.1)) :
    PropertyKey.string key ∉ fields.map fun field => PropertyKey.string field.1 := by
  intro member
  obtain ⟨field, fieldMember, keyEq⟩ := List.mem_map.mp member
  exact absent (List.mem_map.mpr ⟨field, fieldMember, PropertyKey.string.inj keyEq⟩)

private theorem symbol_not_mem_strings {fields : List (JSString × Value)} (symbol : SymbolId) :
    PropertyKey.symbol symbol ∉ fields.map fun field => PropertyKey.string field.1 := by
  intro member
  obtain ⟨field, _, keyEq⟩ := List.mem_map.mp member
  exact absurd keyEq (by simp)

/-- Defining the pending fields in order both succeeds and preserves the construction invariant. One
statement carries totality and soundness together, because both need exactly the same invariant: the
root was allocated after `old`, so every reference `old` resolves is left untouched by every
definition, and the root's own keys grow by exactly one declared key at a time. -/
private theorem defineFields_ok (old : Heap) (root : RefId) (rootFresh : old.size ≤ root.value) :
    ∀ (pending defined : List (JSString × Value)) (index : Nat) (current : Heap),
      Heap.ExactExtension old current →
      Built current root defined →
      ((defined ++ pending).map (·.1)).Nodup →
      (∀ key ∈ (defined ++ pending).map (·.1), PropertyKey.arrayIndex? key = none) →
      (∀ field ∈ pending, current.valueValid field.2 = true) →
      ∃ final, defineFields (FieldEncodeFault := FieldEncodeFault) root index pending current =
          .ok final ∧
        Heap.ExactExtension old final ∧ Built final root (defined ++ pending)
  | [], defined, _, current, extension, built, _, _, _ => by
      exact ⟨current, rfl, extension, by simpa using built⟩
  | field :: rest, defined, index, current, extension, built, nodup, nonIndex, valuesValid => by
      obtain ⟨⟨object, found, kindEq, prototypeEq, extensibleEq⟩, currentKeys, descriptors⟩ := built
      have keyDeclared : field.1 ∈ (defined ++ field :: rest).map (·.1) := by simp
      have keyFresh : field.1 ∉ defined.map (·.1) := by
        intro member
        rw [List.map_append, List.map_cons, List.nodup_append] at nodup
        exact nodup.2.2 field.1 member field.1 (by simp) rfl
      obtain ⟨next, created, sizeEq, frame, validity, ⟨nextObject, nextFound, nextKind,
        nextPrototype, nextExtensible⟩, nextKeys, nextDescriptor, otherDescriptors⟩ :=
        Heap.createDataProperty_ordinary_append current root object field.1 field.2
          (defined.map fun entry => .string entry.1) extension.nextWellFormed found kindEq
          extensibleEq (nonIndex field.1 keyDeclared) currentKeys
          (string_not_mem_of_key_not_mem keyFresh) symbol_not_mem_strings
          (valuesValid field (by simp))
      have nextExtension : Heap.ExactExtension old next := by
        refine ⟨extension.oldWellFormed, Heap.createDataProperty_preserves_wellFormed current next
          root (.string field.1) field.2 true extension.nextWellFormed created,
          by rw [sizeEq]; exact extension.size_le, ?_⟩
        intro ref other oldFound
        have refValid : ref.value < old.size := Heap.get?_ok_valid old ref other oldFound
        have different : ref ≠ root := by
          intro equal
          subst equal
          omega
        rw [frame ref different]
        exact extension.get_eq ref other oldFound
      have nextBuilt : Built next root (defined ++ [field]) := by
        refine ⟨⟨nextObject, nextFound, nextKind, nextPrototype.trans prototypeEq,
          nextExtensible⟩, by simpa using nextKeys, ?_⟩
        intro entry member
        rcases List.mem_append.mp member with member | member
        · rw [otherDescriptors (.string entry.1) (by
            intro keyEq
            exact keyFresh (PropertyKey.string.inj keyEq ▸ List.mem_map_of_mem member))]
          exact descriptors entry member
        · rw [show entry = field from by simpa using member]
          exact nextDescriptor
      obtain ⟨final, defineRest, finalExtension, finalBuilt⟩ :=
        defineFields_ok old root rootFresh rest (defined ++ [field]) (index + 1) next nextExtension
          nextBuilt (by simpa using nodup) (by simpa using nonIndex)
          (fun entry member => by rw [validity]; exact valuesValid entry (by simp [member]))
      refine ⟨final, ?_, finalExtension, by simpa using finalBuilt⟩
      unfold defineFields
      rw [created]
      exact defineRest

private theorem map_fst_zip : ∀ (keys : List JSString) (values : List Value),
    values.length = keys.length → (keys.zip values).map (·.1) = keys
  | [], _, _ => by simp
  | key :: rest, values, length => by
      cases values with
      | nil => simp at length
      | cons value restValues =>
          rw [List.zip_cons_cons, List.map_cons, map_fst_zip rest restValues (by simpa using length)]

private theorem map_string_fst_zip (keys : List JSString) (values : List Value)
    (length : values.length = keys.length) :
    ((keys.zip values).map fun field => PropertyKey.string field.1) = keys.map .string := by
  have compEq : (fun field : JSString × Value => PropertyKey.string field.1) =
      PropertyKey.string ∘ (fun field : JSString × Value => field.1) := rfl
  rw [compEq, ← List.map_map, map_fst_zip keys values length]

private theorem mem_zip_right : ∀ (keys : List JSString) (values : List Value)
    (field : JSString × Value), field ∈ keys.zip values → field.2 ∈ values
  | [], _, _, member => by simp at member
  | key :: rest, values, field, member => by
      cases values with
      | nil => simp at member
      | cons value restValues =>
          rw [List.zip_cons_cons, List.mem_cons] at member
          rcases member with rfl | member
          · simp
          · exact List.mem_cons_of_mem value (mem_zip_right rest restValues field member)

private theorem fieldsRel_of_match : ∀ (schema : Schema.{u}) (heap : Heap) (root : RefId)
    (native : Native schema) (values : List Value),
    (∀ field ∈ (fieldKeys schema).zip values, heap.getOwnProperty root (.string field.1) =
      .ok (some (.data ⟨field.2, true, true, true⟩))) →
    FieldsMatch schema heap native values → FieldsRel schema heap root native
  | [], _, _, _, _, _, _ => trivial
  | spec :: rest, heap, root, native, values, descriptors, matched => by
      cases values with
      | nil => exact absurd matched (by simp [FieldsMatch])
      | cons value restValues =>
          refine ⟨⟨value, descriptors (spec.key, value) (by simp [fieldKeys]), matched.1⟩, ?_⟩
          refine fieldsRel_of_match rest heap root native.2 restValues ?_ matched.2
          intro field member
          exact descriptors field (by
            rw [fieldKeys, List.map_cons, List.zip_cons_cons, List.mem_cons]
            exact Or.inr (by simpa [fieldKeys] using member))

/-- Encodes every field through the heap in declaration order, allocates one fresh ordinary object
with a null prototype, then creates exactly the declared own data properties in declaration order.
The declared keys are validated first: a key sequence ECMAScript own-key order cannot present is
refused outright rather than approximated by an object that merely looks close. -/
def encode (schema : Schema.{u}) (codecs : Codecs FieldEncodeFault FieldDecodeFault schema)
    (heap : Heap) (native : Native schema) :
    Except (EncodeFault FieldEncodeFault) (Value × Heap) :=
  match validateKeys (fieldKeys schema) with
  | .error fault => .error (.invalidSchema fault)
  | .ok _ =>
      match encodeFields schema codecs native 0 heap with
      | .error fault => .error fault
      | .ok (values, encodedHeap) =>
          match encodedHeap.allocate none true with
          | .error fault => .error (.allocation (.heap fault))
          | .ok (root, allocatedHeap) =>
              match defineFields root 0 ((fieldKeys schema).zip values) allocatedHeap with
              | .error fault => .error fault
              | .ok next => .ok (.object root, next)

private def decodeFields : (schema : Schema.{u}) →
    Codecs FieldEncodeFault FieldDecodeFault schema → Heap → List Value → Nat →
    Except (DecodeFault FieldDecodeFault) (Native schema)
  -- The shape check returns one value per declared field, so the short-input branch is unreachable;
  -- it repeats the malformed-field fault rather than invent one.
  | [], _, _, _, _ => .ok PUnit.unit
  | spec :: _, _, _, [], index => .error (.shape (.malformedField index spec.key))
  | _ :: rest, codecs, heap, value :: values, index =>
      match codecs.1.decode heap value with
      | .error fault => .error (.field index fault)
      | .ok field =>
          match decodeFields rest codecs.2 heap values (index + 1) with
          | .error fault => .error fault
          | .ok restFields => .ok (field, restFields)

/-- Decodes only an exact closed-record shape, then decodes each declared field in declaration
order. -/
def decode (schema : Schema.{u}) (codecs : Codecs FieldEncodeFault FieldDecodeFault schema)
    (heap : Heap) (value : Value) : Except (DecodeFault FieldDecodeFault) (Native schema) :=
  match inspectRecord (fieldKeys schema) heap value with
  | .error fault => .error (.shape fault)
  | .ok (_, values) => decodeFields schema codecs heap values 0

private theorem decodeFields_sound : ∀ (schema : Schema.{u})
    (codecs : Codecs FieldEncodeFault FieldDecodeFault schema) (heap : Heap) (values : List Value)
    (index : Nat) (native : Native schema),
    decodeFields schema codecs heap values index = .ok native →
    FieldsMatch schema heap native values
  | [], _, _, _, _, _, _ => trivial
  | spec :: rest, codecs, heap, values, index, native, decoded => by
      cases values with
      | nil => simp [decodeFields] at decoded
      | cons value restValues =>
          unfold decodeFields at decoded
          split at decoded
          · exact absurd decoded (by simp)
          · rename_i field fieldDecoded
            split at decoded
            · exact absurd decoded (by simp)
            · rename_i restFields restDecoded
              simp only [Except.ok.injEq] at decoded
              subst decoded
              exact ⟨codecs.1.decode_sound fieldDecoded,
                decodeFields_sound rest codecs.2 heap restValues (index + 1) restFields restDecoded⟩

private theorem decodeFields_complete : ∀ (schema : Schema.{u})
    (codecs : Codecs FieldEncodeFault FieldDecodeFault schema), Codecs.Complete schema codecs →
    ∀ (heap : Heap) (root : RefId) (native : Native schema) (values : List Value) (index : Nat),
      FieldsRel schema heap root native → values.length = schema.length →
      (∀ field ∈ (fieldKeys schema).zip values, heap.getOwnProperty root (.string field.1) =
        .ok (some (.data ⟨field.2, true, true, true⟩))) →
      decodeFields schema codecs heap values index = .ok native
  | [], _, _, _, _, _, _, _, _, _, _ => rfl
  | spec :: rest, codecs, complete, heap, root, native, values, index, related, length,
      descriptors => by
      cases values with
      | nil => simp at length
      | cons value restValues =>
          obtain ⟨⟨encoded, found, elementRelated⟩, restRelated⟩ := related
          have readEq : heap.getOwnProperty root (.string spec.key) =
              .ok (some (.data ⟨value, true, true, true⟩)) :=
            descriptors (spec.key, value) (by simp [fieldKeys])
          rw [found] at readEq
          have valueEq : encoded = value := by
            have descriptorsEqual :=
              PropertyDescriptor.data.inj (Option.some.inj (Except.ok.inj readEq))
            cases descriptorsEqual
            rfl
          subst valueEq
          have fieldDecoded := complete.1 elementRelated
          have restDecoded := decodeFields_complete rest codecs.2 complete.2 heap root native.2
            restValues (index + 1) restRelated (by simpa using length) (by
              intro field member
              exact descriptors field (by
                rw [fieldKeys, List.map_cons, List.zip_cons_cons, List.mem_cons]
                exact Or.inr (by simpa [fieldKeys] using member)))
          have result : decodeFields (spec :: rest) codecs heap (encoded :: restValues) index =
              .ok (native.1, native.2) := by
            simp only [decodeFields, fieldDecoded, restDecoded]
          rw [result]
          rfl

/-- Decoding an exact closed record establishes the refinement relation for the decoded fields. -/
theorem decode_sound (schema : Schema.{u})
    (codecs : Codecs FieldEncodeFault FieldDecodeFault schema) {heap : Heap} {value : Value}
    {native : Native schema} (decoded : decode schema codecs heap value = .ok native) :
    RecordRel schema heap native value := by
  cases inspected : inspectRecord (fieldKeys schema) heap value with
  | error fault => simp [decode, inspected] at decoded
  | ok result =>
      obtain ⟨root, values⟩ := result
      simp only [decode, inspected] at decoded
      obtain ⟨object, valueEq, found, kindEq, prototypeEq, extensibleEq, keysEq, _, descriptors,
        _⟩ := inspectRecord_sound inspected
      exact ⟨root, object, valueEq, found, kindEq, prototypeEq, extensibleEq, keysEq,
        fieldsRel_of_match schema heap root native values descriptors
          (decodeFields_sound schema codecs heap values 0 native decoded)⟩

/-- Every related closed record decodes back to exactly its Lean record. The hypothesis is the field
codecs' completeness alone, never their totality, so this composes into records of records. -/
theorem decode_complete {schema : Schema.{u}}
    {codecs : Codecs FieldEncodeFault FieldDecodeFault schema}
    (complete : Codecs.Complete schema codecs) {heap : Heap} {native : Native schema}
    {value : Value} (related : RecordRel schema heap native value) :
    decode schema codecs heap value = .ok native := by
  obtain ⟨root, values, inspected⟩ := inspectRecord_complete related.recordShape
  obtain ⟨_, valueEq, _, _, _, _, _, length, descriptors, _⟩ := inspectRecord_sound inspected
  obtain ⟨relatedRoot, _, relatedValueEq, _, _, _, _, _, fields⟩ := id related
  have rootEq : relatedRoot = root := by
    rw [relatedValueEq] at valueEq
    exact Value.object.inj valueEq
  subst rootEq
  simp only [decode, inspected]
  exact decodeFields_complete schema codecs complete heap relatedRoot native values 0 fields
    (by simpa [fieldKeys] using length) descriptors

/-- Encoding extends the heap exactly and relates the fresh record object to the encoded Lean
record. -/
theorem encode_sound (schema : Schema.{u}) (codecs : Codecs FieldEncodeFault FieldDecodeFault schema)
    {old : Heap} {native : Native schema} {value : Value} {next : Heap} (valid : old.WellFormed)
    (encoded : encode schema codecs old native = .ok (value, next)) :
    Heap.ExactExtension old next ∧ RecordRel schema next native value := by
  unfold encode at encoded
  split at encoded
  · exact absurd encoded (by simp)
  · rename_i validated
    split at encoded
    · exact absurd encoded (by simp)
    · rename_i values encodedHeap fieldsEncoded
      split at encoded
      · exact absurd encoded (by simp)
      · rename_i root allocatedHeap allocated
        split at encoded
        · exact absurd encoded (by simp)
        · rename_i produced produceEq
          simp only [Except.ok.injEq, Prod.mk.injEq] at encoded
          obtain ⟨valueEq, heapEq⟩ := encoded
          rw [← valueEq, ← heapEq]
          have keysValid : ValidKeys (fieldKeys schema) := (validateKeys_iff _).mp validated
          obtain ⟨fieldsExtension, length, matched, valuesValid⟩ :=
            encodeFields_sound schema codecs native 0 old values encodedHeap valid fieldsEncoded
          have allocationExtension := Heap.allocate_exactExtension encodedHeap allocatedHeap none
            true root fieldsExtension.nextWellFormed allocated
          obtain ⟨allocObject, allocKeys, _⟩ :=
            Heap.allocate_ordinary_observations encodedHeap allocatedHeap true root allocated
          obtain ⟨freshIndex, _⟩ := Heap.allocate_result_fresh_kind encodedHeap allocatedHeap none
            true root allocated
          have zipKeys : ((fieldKeys schema).zip values).map (·.1) = fieldKeys schema :=
            map_fst_zip (fieldKeys schema) values (by simpa [fieldKeys] using length)
          obtain ⟨built, defineOk, finalExtension, finalBuilt⟩ :
              ∃ built, defineFields (FieldEncodeFault := FieldEncodeFault) root 0
                  ((fieldKeys schema).zip values) allocatedHeap = .ok built ∧
                Heap.ExactExtension encodedHeap built ∧
                Built built root ([] ++ (fieldKeys schema).zip values) :=
            defineFields_ok encodedHeap root (Nat.le_of_eq freshIndex.symm)
              ((fieldKeys schema).zip values) [] 0 allocatedHeap allocationExtension
              ⟨allocObject, by simpa using allocKeys, by simp⟩
              (by simpa [zipKeys] using keysValid.1) (by simpa [zipKeys] using keysValid.2)
              (fun field member => allocationExtension.preserves_valueValid field.2
                (valuesValid field.2 (mem_zip_right (fieldKeys schema) values field member)))
          rw [defineOk] at produceEq
          obtain rfl : built = produced := Except.ok.inj produceEq
          obtain ⟨⟨object, found, kindEq, prototypeEq, extensibleEq⟩, builtKeys, descriptors⟩ :=
            finalBuilt
          refine ⟨fieldsExtension.trans finalExtension, root, object, rfl, found, kindEq,
            prototypeEq, extensibleEq, ?_, ?_⟩
          · rw [builtKeys, List.nil_append]
            exact congrArg Except.ok (map_string_fst_zip (fieldKeys schema) values
              (by simpa [fieldKeys] using length))
          · refine fieldsRel_of_match schema built root native values (by
              intro field member
              exact descriptors field (by simpa using member)) ?_
            exact fieldsMatch_stable schema encodedHeap built native values finalExtension matched

/-- Encoding returns exactly one freshly allocated record root: an object reference that was not
valid in the input heap, carrying the complete record relation in the extended heap. -/
theorem encode_exact (schema : Schema.{u}) (codecs : Codecs FieldEncodeFault FieldDecodeFault schema)
    {old : Heap} {native : Native schema} {value : Value} {next : Heap} (valid : old.WellFormed)
    (encoded : encode schema codecs old native = .ok (value, next)) :
    ∃ root, value = .object root ∧ old.valueValid (.object root) = false ∧
      RecordRel schema next native (.object root) := by
  obtain ⟨extension, related⟩ := encode_sound schema codecs valid encoded
  unfold encode at encoded
  split at encoded
  · exact absurd encoded (by simp)
  · split at encoded
    · exact absurd encoded (by simp)
    · rename_i values encodedHeap fieldsEncoded
      split at encoded
      · exact absurd encoded (by simp)
      · rename_i root allocatedHeap allocated
        split at encoded
        · exact absurd encoded (by simp)
        · rename_i produced produceEq
          simp only [Except.ok.injEq, Prod.mk.injEq] at encoded
          obtain ⟨valueEq, heapEq⟩ := encoded
          obtain ⟨fieldsExtension, _⟩ :=
            encodeFields_sound schema codecs native 0 old values encodedHeap valid fieldsEncoded
          obtain ⟨freshIndex, _⟩ := Heap.allocate_result_fresh_kind encodedHeap allocatedHeap none
            true root allocated
          refine ⟨root, valueEq.symm, ?_, by rw [← valueEq] at related; exact related⟩
          have sizeLe := fieldsExtension.size_le
          simp only [Heap.valueValid, decide_eq_false_iff_not, Nat.not_lt]
          omega

/-- Encoding succeeds for every record a well-formed heap can represent: a presentable declared key
sequence and lawful field codecs are the only hypotheses. -/
theorem encode_total {schema : Schema.{u}}
    {codecs : Codecs FieldEncodeFault FieldDecodeFault schema} (lawful : Codecs.Lawful schema codecs)
    (keysValid : ValidKeys (fieldKeys schema)) (heap : Heap) (native : Native schema)
    (valid : heap.WellFormed) :
    ∃ value next, encode schema codecs heap native = .ok (value, next) := by
  obtain ⟨values, encodedHeap, fieldsEncoded⟩ :=
    encodeFields_total schema codecs lawful native 0 heap valid
  obtain ⟨fieldsExtension, length, _, valuesValid⟩ :=
    encodeFields_sound schema codecs native 0 heap values encodedHeap valid fieldsEncoded
  obtain ⟨root, allocatedHeap, allocated⟩ := Heap.allocate_null_prototype_ok encodedHeap true
  have allocationExtension := Heap.allocate_exactExtension encodedHeap allocatedHeap none true root
    fieldsExtension.nextWellFormed allocated
  obtain ⟨allocObject, allocKeys, _⟩ :=
    Heap.allocate_ordinary_observations encodedHeap allocatedHeap true root allocated
  obtain ⟨freshIndex, _⟩ :=
    Heap.allocate_result_fresh_kind encodedHeap allocatedHeap none true root allocated
  have zipKeys : ((fieldKeys schema).zip values).map (·.1) = fieldKeys schema :=
    map_fst_zip (fieldKeys schema) values (by simpa [fieldKeys] using length)
  obtain ⟨finalHeap, defineOk, _, _⟩ :=
    defineFields_ok (FieldEncodeFault := FieldEncodeFault) encodedHeap root
      (Nat.le_of_eq freshIndex.symm) ((fieldKeys schema).zip values) [] 0 allocatedHeap
      allocationExtension ⟨allocObject, by simpa using allocKeys, by simp⟩
      (by simpa [zipKeys] using keysValid.1) (by simpa [zipKeys] using keysValid.2)
      (fun field member => allocationExtension.preserves_valueValid field.2
        (valuesValid field.2 (mem_zip_right (fieldKeys schema) values field member)))
  refine ⟨.object root, finalHeap, ?_⟩
  unfold encode
  rw [(validateKeys_iff (fieldKeys schema)).mpr keysValid]
  simp only [fieldsEncoded, allocated, defineOk]

/-- The encode boundary: a declared key sequence ECMAScript own-key order cannot present is refused
on the keys alone, before any field is encoded and before anything is allocated. -/
theorem encode_invalidSchema (schema : Schema.{u})
    (codecs : Codecs FieldEncodeFault FieldDecodeFault schema) (heap : Heap)
    (native : Native schema) (fault : SchemaFault)
    (invalid : validateKeys (fieldKeys schema) = .error fault) :
    encode schema codecs heap native = .error (.invalidSchema fault) := by
  unfold encode
  rw [invalid]

/-- Closed-record codec: bounded exact-shape validation inbound, one fresh null-prototype ordinary
object outbound. Field lawfulness is not needed to build it, nor to prove it sound or complete; only
the totality results ask for it. -/
def codec (schema : Schema.{u}) (codecs : Codecs FieldEncodeFault FieldDecodeFault schema) :
    Codec (Native schema) (EncodeFault FieldEncodeFault) (DecodeFault FieldDecodeFault)
      (refinement schema) where
  encode := encode schema codecs
  decode := decode schema codecs
  encode_sound valid encoded := encode_sound schema codecs valid encoded
  decode_sound decoded := decode_sound schema codecs decoded

/-- The record codec is complete: every related record decodes back to exactly its Lean record. This
needs only `Codec.Complete` of every field codec, so it holds for records of records, where the full
`LawfulCodec` hypothesis would be refutable by `not_lawful` for an unpresentable schema. -/
theorem codec_complete {schema : Schema.{u}}
    {codecs : Codecs FieldEncodeFault FieldDecodeFault schema}
    (complete : Codecs.Complete schema codecs) {heap : Heap} {native : Native schema}
    {value : Value} (related : (refinement schema).Rel heap native value) :
    (codec schema codecs).decode heap value = .ok native :=
  decode_complete complete related

/-- Decoding accepts exactly the values the refinement relates to the decoded record. Field
completeness is the only hypothesis, so this also holds for records of records. -/
theorem decode_exact {schema : Schema.{u}}
    {codecs : Codecs FieldEncodeFault FieldDecodeFault schema}
    (complete : Codecs.Complete schema codecs) (heap : Heap) (value : Value)
    (native : Native schema) :
    (codec schema codecs).decode heap value = .ok native ↔
      (refinement schema).Rel heap native value :=
  ⟨decode_sound schema codecs, decode_complete complete⟩

/-- Full composition: a presentable record encodes to a fresh ordinary object in an exactly extended
heap, and decoding that exact pair returns the original Lean record. -/
theorem codec_roundtrip {schema : Schema.{u}}
    {codecs : Codecs FieldEncodeFault FieldDecodeFault schema} (lawful : Codecs.Lawful schema codecs)
    (complete : Codecs.Complete schema codecs) (keysValid : ValidKeys (fieldKeys schema))
    (heap : Heap) (native : Native schema) (valid : heap.WellFormed) :
    ∃ value next,
      (codec schema codecs).encode heap native = .ok (value, next) ∧
      Heap.ExactExtension heap next ∧
      (refinement schema).Rel next native value ∧
      (codec schema codecs).decode next value = .ok native := by
  obtain ⟨value, next, encoded⟩ := encode_total lawful keysValid heap native valid
  obtain ⟨extension, related⟩ := (codec schema codecs).encode_sound valid encoded
  exact ⟨value, next, encoded, extension, related, codec_complete complete related⟩

/-- Record encoding cannot be lawful for every schema, because `encode` refuses any schema outside
`ValidKeys` rather than allocating something close to it.

The two refusals differ in strength, and `ValidKeys` records which is which. A repeated key is
impossible: `nodup_of_related` derives it from the model, so no well-formed heap relates any value to
such a schema. An index-like key is refused wholesale, which is deliberate conservatism — own-key
order hoists an index ahead of every other string key, so some declared orders genuinely cannot be
read back, but others (`["0", "flag"]`) could have been and are refused anyway. -/
theorem not_lawful (schema : Schema.{u})
    (codecs : Codecs FieldEncodeFault FieldDecodeFault schema) (native : Native schema)
    (invalid : ¬ValidKeys (fieldKeys schema)) : ¬LawfulCodec (codec schema codecs) := by
  refine LawfulCodec.not_of_encode_always_errors (codec schema codecs) native ?_
  intro heap other
  cases validated : validateKeys (fieldKeys schema) with
  | ok accepted => exact absurd ((validateKeys_iff _).mp validated) invalid
  | error fault =>
      exact ⟨.invalidSchema fault, encode_invalidSchema schema codecs heap other fault validated⟩

/-- A root returned by `Heap.allocate` differs from every reference valid before it ran. -/
theorem fresh_root_distinct (old next : Heap) (prototype : Option RefId) (extensible : Bool)
    (fresh previous : RefId) (allocated : old.allocate prototype extensible = .ok (fresh, next))
    (previousValid : old.valueValid (.object previous) = true) : fresh ≠ previous := by
  obtain ⟨freshIndex, _⟩ :=
    Heap.allocate_result_fresh_kind old next prototype extensible fresh allocated
  exact Heap.fresh_distinct_of_oldValid old fresh previous (Nat.le_of_eq freshIndex.symm)
    previousValid

/-- Decoding rejects every primitive with the object-domain shape fault. -/
theorem decode_primitive (schema : Schema.{u})
    (codecs : Codecs FieldEncodeFault FieldDecodeFault schema) (heap : Heap)
    (primitive : JS.Primitive) :
    (codec schema codecs).decode heap (.primitive primitive) =
      .error (.shape .expectedObject) := rfl

/-- Decoding rejects dangling object references with the exact reference that failed. -/
theorem decode_invalidRef (schema : Schema.{u})
    (codecs : Codecs FieldEncodeFault FieldDecodeFault schema) (heap : Heap) (ref : RefId)
    (fault : HeapFault) (missing : heap.get? ref = .error fault) :
    (codec schema codecs).decode heap (.object ref) = .error (.shape (.invalidRef ref)) := by
  change decode schema codecs heap (.object ref) = _
  simp [decode, inspectRecord, Bind.bind, Except.bind, Pure.pure, Except.pure, missing]

/-- Decoding rejects references to objects of any other kind with their exact kind tag. -/
theorem decode_wrongKind (schema : Schema.{u})
    (codecs : Codecs FieldEncodeFault FieldDecodeFault schema) (heap : Heap) (ref : RefId)
    (object : ObjectRecord) (found : heap.get? ref = .ok object)
    (notOrdinary : object.kind ≠ .ordinary) :
    (codec schema codecs).decode heap (.object ref) =
      .error (.shape (.wrongKind object.kind.tag)) := by
  change decode schema codecs heap (.object ref) = _
  cases kindEq : object.kind with
  | ordinary => exact absurd kindEq notOrdinary
  | array slots => simp [decode, inspectRecord, Bind.bind, Except.bind, Pure.pure, Except.pure,
      found, kindEq]
  | function slots => simp [decode, inspectRecord, Bind.bind, Except.bind, Pure.pure, Except.pure,
      found, kindEq]
  | arrayIterator slots => simp [decode, inspectRecord, Bind.bind, Except.bind, Pure.pure,
      Except.pure, found, kindEq]
  | primitiveWrapper slots => simp [decode, inspectRecord, Bind.bind, Except.bind, Pure.pure,
      Except.pure, found, kindEq]

/-- Decoding rejects an ordinary object that inherits from anything, naming its exact prototype. A
null prototype is what makes "no extra keys" an observation instead of an assumption, so a record
that inherits is refused rather than read through its prototype chain. -/
theorem decode_wrongPrototype (schema : Schema.{u})
    (codecs : Codecs FieldEncodeFault FieldDecodeFault schema) (heap : Heap) (ref : RefId)
    (object : ObjectRecord) (prototype : RefId) (found : heap.get? ref = .ok object)
    (ordinary : object.kind = .ordinary) (inherits : object.prototype = some prototype) :
    (codec schema codecs).decode heap (.object ref) =
      .error (.shape (.wrongPrototype prototype)) := by
  change decode schema codecs heap (.object ref) = _
  simp [decode, inspectRecord, Bind.bind, Except.bind, Pure.pure, Except.pure, found, ordinary,
    inherits]

/-- Decoding rejects a non-extensible ordinary object. `preventExtensions` is irreversible in the
model, so such an object can never be produced by this codec's own encoder. -/
theorem decode_notExtensible (schema : Schema.{u})
    (codecs : Codecs FieldEncodeFault FieldDecodeFault schema) (heap : Heap) (ref : RefId)
    (object : ObjectRecord) (found : heap.get? ref = .ok object)
    (ordinary : object.kind = .ordinary) (prototypeEq : object.prototype = none)
    (frozen : object.extensible = false) :
    (codec schema codecs).decode heap (.object ref) = .error (.shape .notExtensible) := by
  change decode schema codecs heap (.object ref) = _
  simp [decode, inspectRecord, Bind.bind, Except.bind, Pure.pure, Except.pure, found, ordinary,
    prototypeEq, frozen]

/-- A record codec over a presentable schema is lawful outright.

This is where records differ from arrays. `Array.not_lawful` refutes `LawfulCodec` for *every* element
codec, because a Lean array has no length bound while ECMAScript caps one at `2^32 - 1`. A record has
no such gap: `Native schema` has exactly as many fields as the schema declares, so once the declared
keys are presentable (`ValidKeys`) and every field codec is lawful and complete, encoding is total and
decoding is complete. Packaging it here is what lets records nest without each caller re-deriving
lawfulness from `encode_total` and `codec_complete`. -/
theorem codec_lawful {schema : Schema.{u}}
    {codecs : Codecs FieldEncodeFault FieldDecodeFault schema} (lawful : Codecs.Lawful schema codecs)
    (complete : Codecs.Complete schema codecs) (keysValid : ValidKeys (fieldKeys schema)) :
    LawfulCodec (codec schema codecs) where
  encode_total heap native valid := encode_total lawful keysValid heap native valid
  complete := codec_complete complete

/-- Every shape rejection reaches the caller as its own typed fault, unchanged.

This is the theorem-level pin for the three fault classes that have no dedicated theorem above --
missing key, extra key and malformed descriptor -- and for the key-mismatch position. Stating it at
the `inspectRecord` boundary covers all of `ShapeFault` uniformly rather than one constructor at a
time, and it is what makes those positions observable to a caller instead of internal to the checker:
`matchKeys` distinguishes missing, extra and mismatched keys by index, `readFields` names both the
index and the key of a field that is not a standard data descriptor, and both survive into the
`DecodeFault` the caller sees. -/
theorem decode_shapeFault (schema : Schema.{u})
    (codecs : Codecs FieldEncodeFault FieldDecodeFault schema) (heap : Heap) (value : Value)
    (fault : ShapeFault) (rejected : inspectRecord (fieldKeys schema) heap value = .error fault) :
    (codec schema codecs).decode heap value = .error (.shape fault) := by
  change decode schema codecs heap value = _
  simp [decode, rejected]

/-- A field that fails to decode is reported against its own position rather than the record as a
whole, so a caller learns which field was rejected and by which field codec.

Stated for the leading declared field, which is where attribution is decided: `decodeFields` walks
the declared list carrying an index, so the head case is the one that fixes the correspondence between
position and reported index. Deeper positions are covered by the executable fault-identity tests. -/
theorem decode_field_head (spec : FieldSpec.{u}) (rest : Schema.{u})
    (codecs : Codecs FieldEncodeFault FieldDecodeFault (spec :: rest)) (heap : Heap) (value : Value)
    (root : RefId) (values : List Value) (fieldValue : Value) (fault : FieldDecodeFault)
    (inspected : inspectRecord (fieldKeys (spec :: rest)) heap value = .ok (root, fieldValue :: values))
    (failed : codecs.1.decode heap fieldValue = .error fault) :
    (codec (spec :: rest) codecs).decode heap value = .error (.field 0 fault) := by
  change decode (spec :: rest) codecs heap value = _
  simp [decode, decodeFields, inspected, failed]

end Record

end TSLean.Refinement
