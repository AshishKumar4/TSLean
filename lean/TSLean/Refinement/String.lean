import TSLean.Refinement.Core
import TSLean.Refinement.Evidence
import TSLean.JS.Equality
import TSLean.JS.PrimitiveOperators

namespace TSLean.Refinement

open TSLean.JS

namespace String

/-- Typed failures produced while decoding a JavaScript string value. -/
inductive DecodeFault where
  | expectedString
  | invalidUTF16
  deriving DecidableEq, Repr

/-- Lean strings refine their exact ECMAScript UTF-16 primitive encodings. -/
def refinement : Refinement _root_.String where
  Rel _ native value := value = .primitive (.string (JSString.ofLeanString native))
  valueValid related := by cases related; rfl
  stable _ related := related

/-- The string refinement is exact and independent of the heap. -/
theorem refinement_rel_iff (heap : Heap) (native : _root_.String) (value : Value) :
    refinement.Rel heap native value ↔
      value = .primitive (.string (JSString.ofLeanString native)) := Iff.rfl

/-- The exact string refinement has a unique native decoding. -/
theorem refinement_uniqueDecode : refinement.UniqueDecode := by
  intro heap left right value leftRelated rightRelated
  simp only [refinement] at leftRelated rightRelated
  rw [leftRelated] at rightRelated
  exact JSString.ofLeanString_injective
    (JS.Primitive.string.inj (Value.primitive.inj rightRelated))

/-- Encodes a Lean string as its exact UTF-16 primitive without changing the heap. -/
def encode (heap : Heap) (native : _root_.String) : Except Empty (Value × Heap) :=
  .ok (.primitive (.string (JSString.ofLeanString native)), heap)

/-- Decodes string primitives only when their UTF-16 code units form Unicode scalar values. -/
def decode (_ : Heap) (value : Value) : Except DecodeFault _root_.String :=
  match value with
  | .primitive (.string encoded) =>
      match encoded.toLeanString? with
      | some native => .ok native
      | none => .error .invalidUTF16
  | _ => .error .expectedString

/-- Total heap-neutral encoding and strict UTF-16 decoding for string primitives. -/
def codec : Codec _root_.String Empty DecodeFault refinement where
  encode := encode
  decode := decode
  encode_sound := by
    intro old native value next valid encoded
    simp only [encode, Except.ok.injEq, Prod.mk.injEq] at encoded
    rcases encoded with ⟨rfl, rfl⟩
    exact ⟨Heap.ExactExtension.refl old valid, rfl⟩
  decode_sound := by
    intro heap value native decoded
    cases value with
    | object ref => simp [decode] at decoded
    | primitive primitive =>
        cases primitive <;> simp [decode] at decoded
        rename_i encoded
        split at decoded
        next actual decodedString =>
          cases decoded
          exact congrArg (Value.primitive ∘ JS.Primitive.string)
            (JSString.ofLeanString_toLeanString? decodedString).symm
        next => contradiction

/-- String encoding returns the exact primitive and original heap. -/
theorem encode_exact (heap : Heap) (native : _root_.String) :
    codec.encode heap native =
      .ok (.primitive (.string (JSString.ofLeanString native)), heap) := rfl

/-- Every encoded Lean string decodes exactly. -/
theorem decode_exact (heap : Heap) (native : _root_.String) :
    codec.decode heap (.primitive (.string (JSString.ofLeanString native))) = .ok native := by
  simp [codec, decode, JSString.toLeanString?_ofLeanString]

/-- A successful string decode implies exact UTF-16 re-encoding. -/
theorem decode_reencode {heap : Heap} {encoded : JSString} {native : _root_.String}
    (decoded : codec.decode heap (.primitive (.string encoded)) = .ok native) :
    JSString.ofLeanString native = encoded := by
  simp only [codec, decode] at decoded
  split at decoded
  next actual decodedString =>
    cases decoded
    exact JSString.ofLeanString_toLeanString? decodedString
  next => contradiction

/-- Malformed UTF-16 string primitives fail with a typed decode fault. -/
theorem decode_invalidUTF16 (heap : Heap) (encoded : JSString)
    (invalid : encoded.toLeanString? = none) :
    codec.decode heap (.primitive (.string encoded)) = .error .invalidUTF16 := by
  simp [codec, decode, invalid]

/-- Non-string values fail with the string-domain decode fault. -/
theorem decode_nonstring (heap : Heap) (value : Value)
    (notString : ∀ encoded, value ≠ .primitive (.string encoded)) :
    codec.decode heap value = .error .expectedString := by
  cases value with
  | object ref => rfl
  | primitive primitive => cases primitive <;> simp_all [codec, decode]

/-- The string codec is total and complete for exact UTF-16 encodings. -/
theorem codec_lawful : LawfulCodec codec where
  encode_total heap native valid :=
    ⟨.primitive (.string (JSString.ofLeanString native)), heap, rfl⟩
  complete := by
    intro heap native value related
    cases related
    exact decode_exact heap native

/-- String codec roundtrip includes exact value and heap preservation. -/
theorem codec_roundtrip (heap : Heap) (native : _root_.String) (valid : heap.WellFormed) :
    ∃ value next,
      codec.encode heap native = .ok (value, next) ∧
      value = .primitive (.string (JSString.ofLeanString native)) ∧
      next = heap ∧
      codec.decode next value = .ok native := by
  refine ⟨.primitive (.string (JSString.ofLeanString native)), heap,
    encode_exact heap native, rfl, rfl, ?_⟩
  exact codec_lawful.roundtrip valid (encode_exact heap native)

/-- Exact UTF-16 encoding commutes with Lean string append. -/
theorem append_commutes (left right : _root_.String) :
    (JSString.ofLeanString left).append (JSString.ofLeanString right) =
      JSString.ofLeanString (left ++ right) :=
  (JSString.ofLeanString_append left right).symm

/-- Primitive string addition commutes with Lean string append. -/
theorem add_commutes (left right : _root_.String) :
    JS.Primitive.add (.string (JSString.ofLeanString left))
      (.string (JSString.ofLeanString right)) =
      .ok (.primitive (.string (JSString.ofLeanString (left ++ right)))) := by
  change Except.ok (Value.primitive (JS.Primitive.string
    ((JSString.ofLeanString left).append (JSString.ofLeanString right)))) = _
  rw [append_commutes]

/-- Exact UTF-16 encoding equality is exactly Lean string equality. -/
theorem encoded_eq_iff (left right : _root_.String) :
    JSString.ofLeanString left = JSString.ofLeanString right ↔ left = right :=
  ⟨fun equal => JSString.ofLeanString_injective equal,
    congrArg JSString.ofLeanString⟩

/-- Exact UTF-16 code-unit equality is exactly Lean string equality. -/
theorem codeUnits_eq_iff (left right : _root_.String) :
    (JSString.ofLeanString left).codeUnits = (JSString.ofLeanString right).codeUnits ↔
      left = right := by
  constructor
  · intro equal
    apply JSString.ofLeanString_injective
    exact congrArg JSString.mk equal
  · intro equal
    cases equal
    rfl

/-- JavaScript strict equality on encoded strings is Lean string equality. -/
theorem strictEqual_commutes (left right : _root_.String) :
    strictEqual (.primitive (.string (JSString.ofLeanString left)))
      (.primitive (.string (JSString.ofLeanString right))) = (left == right) := by
  change (JSString.ofLeanString left).equal (JSString.ofLeanString right) = (left == right)
  apply Bool.eq_iff_iff.mpr
  simp only [JSString.equal, decide_eq_true_eq, beq_iff_eq]
  exact codeUnits_eq_iff left right

/-- JavaScript SameValue on encoded strings is Lean string equality. -/
theorem sameValue_commutes (left right : _root_.String) :
    sameValue (.primitive (.string (JSString.ofLeanString left)))
      (.primitive (.string (JSString.ofLeanString right))) = (left == right) := by
  change (JSString.ofLeanString left).equal (JSString.ofLeanString right) = (left == right)
  exact strictEqual_commutes left right

/-- JavaScript SameValueZero on encoded strings is Lean string equality. -/
theorem sameValueZero_commutes (left right : _root_.String) :
    sameValueZero (.primitive (.string (JSString.ofLeanString left)))
      (.primitive (.string (JSString.ofLeanString right))) = (left == right) := by
  change (JSString.ofLeanString left).equal (JSString.ofLeanString right) = (left == right)
  exact strictEqual_commutes left right

/-- Primitive string/string loose equality is Lean string equality. -/
theorem looseEqual_commutes (left right : _root_.String) :
    (JS.Primitive.string (JSString.ofLeanString left)).looseEqual
      (.string (JSString.ofLeanString right)) = (left == right) := by
  change (JSString.ofLeanString left).equal (JSString.ofLeanString right) = (left == right)
  exact strictEqual_commutes left right

/-- Empty Lean strings encode to the empty UTF-16 sequence. -/
theorem empty_commutes : JSString.ofLeanString "" = ⟨[]⟩ := rfl

/-- Encoded strings are code-unit empty exactly when their Lean strings are empty. -/
theorem isEmpty_iff (native : _root_.String) :
    (JSString.ofLeanString native).isEmpty = true ↔ native = "" := by
  constructor
  · intro empty
    cases encoded : JSString.ofLeanString native with
    | mk units =>
        cases units with
        | nil =>
            apply JSString.ofLeanString_injective
            exact encoded.trans empty_commutes.symm
        | cons unit rest => simp [encoded, JSString.isEmpty] at empty
  · intro empty
    subst native
    rfl

/-- JavaScript string truthiness is exactly Lean non-emptiness. -/
theorem toBoolean_commutes (native : _root_.String) :
    (Value.primitive (.string (JSString.ofLeanString native))).toBoolean = (native != "") := by
  by_cases isEmpty : native = ""
  · subst native
    rfl
  · have encodedNonempty : JSString.ofLeanString native ≠ JSString.ofLeanString "" := by
      intro equal
      exact isEmpty (JSString.ofLeanString_injective equal)
    cases encoded : JSString.ofLeanString native with
    | mk units =>
        cases units with
        | nil => exact False.elim (encodedNonempty (encoded.trans empty_commutes.symm))
        | cons unit rest =>
            simp [Value.toBoolean, JS.Primitive.toBoolean, JSString.isEmpty, isEmpty]

/-- Primitive ToString is the identity on encoded string primitives. -/
theorem toString_commutes (native : _root_.String) :
    (JS.Primitive.string (JSString.ofLeanString native)).toString =
      .ok (JSString.ofLeanString native) := rfl

/-- A JavaScript code-unit sequence is valid UTF-16 when it decodes to a Lean string. -/
def ValidUTF16 (encoded : JSString) : Prop :=
  ∃ native, encoded.toLeanString? = some native

/-- Executable UTF-16 validation backed by the strict decoder. -/
def validUTF16Guard : Guard JSString ValidUTF16 :=
  Guard.create "UTF-16 decodes without unpaired surrogates" (by decide)
    (fun encoded => encoded.toLeanString?.isSome)
    (fun encoded accepted => by
      cases decoded : encoded.toLeanString? with
      | none => simp [decoded] at accepted
      | some native => exact ⟨native, decoded⟩)

/-- Passing the UTF-16 guard provides a specific decoded string. -/
theorem validUTF16Guard_sound (encoded : JSString)
    (accepted : validUTF16Guard.check encoded = true) :
    ∃ native, encoded.toLeanString? = some native :=
  validUTF16Guard.sound encoded accepted

/-- Every successfully decoded UTF-16 value passes the executable guard. -/
theorem validUTF16Guard_complete {encoded : JSString} {native : _root_.String}
    (decoded : encoded.toLeanString? = some native) :
    validUTF16Guard.check encoded = true := by
  change encoded.toLeanString?.isSome = true
  simp [decoded]

/-- A specific successful decode is preserved by exact re-encoding. -/
theorem validUTF16Guard_specific {encoded : JSString} {native : _root_.String}
    (decoded : encoded.toLeanString? = some native) :
    JSString.ofLeanString native = encoded :=
  JSString.ofLeanString_toLeanString? decoded

/-- Guard evidence proves that some Lean string exactly refines the accepted UTF-16 input. -/
def guardedRelationExistsEvidence (heap : Heap) (encoded : JSString)
    (accepted : validUTF16Guard.check encoded = true) :
    Evidence (∃ native, refinement.Rel heap native (.primitive (.string encoded))) :=
  (Evidence.ofGuard validUTF16Guard encoded accepted).map fun ⟨native, decoded⟩ =>
    ⟨native, congrArg (Value.primitive ∘ JS.Primitive.string)
      (validUTF16Guard_specific decoded).symm⟩

/-- A specific successful decode proves its exact refinement relation without guard provenance. -/
def decodedRelationEvidence (heap : Heap) (encoded : JSString) (native : _root_.String)
    (decoded : encoded.toLeanString? = some native) :
    Evidence (refinement.Rel heap native (.primitive (.string encoded))) :=
  Evidence.proved (congrArg (Value.primitive ∘ JS.Primitive.string)
    (validUTF16Guard_specific decoded).symm)

/-- Appending valid UTF-16 strings preserves their decoded concatenation. -/
theorem decode_append {left right : JSString} {leftNative rightNative : _root_.String}
    (leftDecoded : left.toLeanString? = some leftNative)
    (rightDecoded : right.toLeanString? = some rightNative) :
    (left.append right).toLeanString? = some (leftNative ++ rightNative) := by
  rw [← JSString.ofLeanString_toLeanString? leftDecoded,
    ← JSString.ofLeanString_toLeanString? rightDecoded,
    ← JSString.ofLeanString_append]
  exact JSString.toLeanString?_ofLeanString _

/-- The executable UTF-16 guard is closed under append. -/
theorem validUTF16Guard_append {left right : JSString}
    (leftValid : validUTF16Guard.check left = true)
    (rightValid : validUTF16Guard.check right = true) :
    validUTF16Guard.check (left.append right) = true := by
  obtain ⟨leftNative, leftDecoded⟩ := validUTF16Guard.sound left leftValid
  obtain ⟨rightNative, rightDecoded⟩ := validUTF16Guard.sound right rightValid
  change (left.append right).toLeanString?.isSome = true
  simp [decode_append leftDecoded rightDecoded]

/-- Lean strings whose characters all fit one UTF-16 code unit. -/
def BMPString (native : _root_.String) : Prop :=
  ∀ character, character ∈ native.toList → character.toNat ≤ 0xffff

/-- Executable validation for the BMP-only string boundary. -/
def bmpStringGuard : Guard _root_.String BMPString :=
  Guard.create "every Unicode scalar is in the BMP" (by decide)
    (fun native => native.toList.all fun character => decide (character.toNat ≤ 0xffff))
    (fun native accepted character member => by
      exact of_decide_eq_true
        (List.all_eq_true.mp accepted character member))

/-- Passing the BMP guard proves every character fits one UTF-16 code unit. -/
theorem bmpStringGuard_sound (native : _root_.String)
    (accepted : bmpStringGuard.check native = true) : BMPString native :=
  bmpStringGuard.sound native accepted

/-- Every BMP string passes the executable BMP guard. -/
theorem bmpStringGuard_complete (native : _root_.String) (bmp : BMPString native) :
    bmpStringGuard.check native = true := by
  change native.toList.all (fun character => decide (character.toNat ≤ 0xffff)) = true
  apply List.all_eq_true.mpr
  intro character member
  exact decide_eq_true (bmp character member)

/-- Under the BMP guard, JavaScript code-unit length equals Lean character length. -/
theorem bmp_length (native : _root_.String) (bmp : BMPString native) :
    (JSString.ofLeanString native).length = native.length := by
  simp [JSString.length, JSString.ofLeanString_codeUnits_of_bmp native bmp,
    String.length_toList]

/-- Under the BMP guard, each in-bounds code-unit index is the matching Lean character. -/
theorem bmp_codeUnit_at (native : _root_.String) (bmp : BMPString native) (index : Nat)
    (inBounds : index < native.length) :
    (JSString.ofLeanString native).codeUnits[index]? =
      some (UInt16.ofNat native.toList[index].toNat) := by
  rw [JSString.ofLeanString_codeUnits_of_bmp native bmp, List.getElem?_map,
    List.getElem?_eq_getElem (by simpa [String.length_toList] using inBounds)]
  rfl

end String

end TSLean.Refinement
