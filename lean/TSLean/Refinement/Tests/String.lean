import TSLean.Refinement

namespace TSLean.Refinement.Tests

open TSLean.JS

namespace StringContracts

theorem string_contract_inventory :
    (∀ value : _root_.String,
      (JSString.ofLeanString value).toLeanString? = some value) ∧
    (∀ ⦃left right : _root_.String⦄,
      JSString.ofLeanString left = JSString.ofLeanString right → left = right) ∧
    (∀ (value : JSString) (native : _root_.String), value.toLeanString? = some native →
      JSString.ofLeanString native = value) ∧
    String.refinement.UniqueDecode ∧
    LawfulCodec String.codec ∧
    (∀ (encoded : JSString), String.validUTF16Guard.check encoded = true →
      ∃ native, encoded.toLeanString? = some native) ∧
    (∀ (native : _root_.String), String.BMPString native →
      (JSString.ofLeanString native).length = native.length) ∧
    ∀ (native : _root_.String) (_bmp : String.BMPString native) (index : Nat)
      (inBounds : index < native.length),
      (JSString.ofLeanString native).codeUnits[index]? =
        some (UInt16.ofNat (native.toList.get ⟨index,
          show index < native.toList.length from inBounds⟩).toNat) := by
  exact ⟨JSString.toLeanString?_ofLeanString, JSString.ofLeanString_injective,
    fun _ _ => JSString.ofLeanString_toLeanString?, String.refinement_uniqueDecode,
    String.codec_lawful, String.validUTF16Guard_sound, String.bmp_length,
    String.bmp_codeUnit_at⟩

example (value : _root_.String) :
    (JSString.ofLeanString value).toLeanString? = some value :=
  JSString.toLeanString?_ofLeanString value

example : ∀ ⦃left right : _root_.String⦄,
    JSString.ofLeanString left = JSString.ofLeanString right → left = right :=
  JSString.ofLeanString_injective

example {value : JSString} {native : _root_.String}
    (decoded : value.toLeanString? = some native) :
    JSString.ofLeanString native = value :=
  JSString.ofLeanString_toLeanString? decoded

example (heap : Heap) (native : _root_.String) (value : Value) :
    String.refinement.Rel heap native value ↔
      value = .primitive (.string (JSString.ofLeanString native)) :=
  String.refinement_rel_iff heap native value

example : String.refinement.UniqueDecode := String.refinement_uniqueDecode

example (heap : Heap) (native : _root_.String) :
    String.codec.encode heap native =
      .ok (.primitive (.string (JSString.ofLeanString native)), heap) :=
  String.encode_exact heap native

example (heap : Heap) (native : _root_.String) :
    String.codec.decode heap (.primitive (.string (JSString.ofLeanString native))) = .ok native :=
  String.decode_exact heap native

example {heap : Heap} {encoded : JSString} {native : _root_.String}
    (decoded : String.codec.decode heap (.primitive (.string encoded)) = .ok native) :
    JSString.ofLeanString native = encoded :=
  String.decode_reencode decoded

example : LawfulCodec String.codec := String.codec_lawful

example (heap : Heap) (native : _root_.String) (valid : heap.WellFormed) :
    ∃ value next,
      String.codec.encode heap native = .ok (value, next) ∧
      value = .primitive (.string (JSString.ofLeanString native)) ∧
      next = heap ∧
      String.codec.decode next value = .ok native :=
  String.codec_roundtrip heap native valid

example (left right : _root_.String) :
    (JSString.ofLeanString left).append (JSString.ofLeanString right) =
      JSString.ofLeanString (left ++ right) :=
  String.append_commutes left right

example (left right : _root_.String) :
    strictEqual (.primitive (.string (JSString.ofLeanString left)))
      (.primitive (.string (JSString.ofLeanString right))) = (left == right) :=
  String.strictEqual_commutes left right

example (left right : _root_.String) :
    sameValue (.primitive (.string (JSString.ofLeanString left)))
      (.primitive (.string (JSString.ofLeanString right))) = (left == right) :=
  String.sameValue_commutes left right

example (left right : _root_.String) :
    sameValueZero (.primitive (.string (JSString.ofLeanString left)))
      (.primitive (.string (JSString.ofLeanString right))) = (left == right) :=
  String.sameValueZero_commutes left right

example (left right : _root_.String) :
    (JS.Primitive.string (JSString.ofLeanString left)).looseEqual
      (.string (JSString.ofLeanString right)) = (left == right) :=
  String.looseEqual_commutes left right

example (left right : _root_.String) :
    (JSString.ofLeanString left).codeUnits = (JSString.ofLeanString right).codeUnits ↔
      left = right :=
  String.codeUnits_eq_iff left right

example (native : _root_.String) :
    (JSString.ofLeanString native).isEmpty = true ↔ native = "" :=
  String.isEmpty_iff native

example (native : _root_.String) :
    (Value.primitive (.string (JSString.ofLeanString native))).toBoolean = (native != "") :=
  String.toBoolean_commutes native

example (native : _root_.String) :
    (JS.Primitive.string (JSString.ofLeanString native)).toString =
      .ok (JSString.ofLeanString native) :=
  String.toString_commutes native

example (encoded : JSString) (accepted : String.validUTF16Guard.check encoded = true) :
    ∃ native, encoded.toLeanString? = some native :=
  String.validUTF16Guard_sound encoded accepted

example {encoded : JSString} {native : _root_.String}
    (decoded : encoded.toLeanString? = some native) :
    String.validUTF16Guard.check encoded = true :=
  String.validUTF16Guard_complete decoded

example (heap : Heap) (encoded : JSString)
    (accepted : String.validUTF16Guard.check encoded = true) :
    Evidence (∃ native,
      String.refinement.Rel heap native (.primitive (.string encoded))) :=
  String.guardedRelationExistsEvidence heap encoded accepted

example (heap : Heap) (encoded : JSString)
    (accepted : String.validUTF16Guard.check encoded = true) :
    ∃ native, String.refinement.Rel heap native (.primitive (.string encoded)) := by
  cases status : (String.guardedRelationExistsEvidence heap encoded accepted).proof? with
  | none =>
      simp [String.guardedRelationExistsEvidence, Evidence.proof?, Evidence.map,
        Evidence.ofGuard] at status
  | some proof => exact proof

example (heap : Heap) (encoded : JSString) (native : _root_.String)
    (decoded : encoded.toLeanString? = some native) :
    Evidence (String.refinement.Rel heap native (.primitive (.string encoded))) :=
  String.decodedRelationEvidence heap encoded native decoded

example (heap : Heap) (encoded : JSString) (native : _root_.String)
    (decoded : encoded.toLeanString? = some native) :
    String.refinement.Rel heap native (.primitive (.string encoded)) := by
  cases status : (String.decodedRelationEvidence heap encoded native decoded).proof? with
  | none =>
      simp [String.decodedRelationEvidence, Evidence.proof?, Evidence.proved] at status
  | some proof => exact proof

example {left right : JSString}
    (leftValid : String.validUTF16Guard.check left = true)
    (rightValid : String.validUTF16Guard.check right = true) :
    String.validUTF16Guard.check (left.append right) = true :=
  String.validUTF16Guard_append leftValid rightValid

example (native : _root_.String) (bmp : String.BMPString native) :
    (JSString.ofLeanString native).length = native.length :=
  String.bmp_length native bmp

example (native : _root_.String) (accepted : String.bmpStringGuard.check native = true) :
    String.BMPString native :=
  String.bmpStringGuard_sound native accepted

example (native : _root_.String) (bmp : String.BMPString native) :
    String.bmpStringGuard.check native = true :=
  String.bmpStringGuard_complete native bmp

example (native : _root_.String) (bmp : String.BMPString native) (index : Nat)
    (inBounds : index < native.length) :
    (JSString.ofLeanString native).codeUnits[index]? =
      some (UInt16.ofNat native.toList[index].toNat) :=
  String.bmp_codeUnit_at native bmp index inBounds

end StringContracts

private def stringDecodeIs (value : Value)
    (expected : Except String.DecodeFault _root_.String) : Bool :=
  match String.decode Heap.empty value, expected with
  | .ok actual, .ok wanted => decide (actual = wanted)
  | .error actual, .error wanted => decide (actual = wanted)
  | _, _ => false

private def testStringBoundaries : IO Unit := do
  let samples := [
    String.mk [Char.ofNat 0x00],
    String.mk [Char.ofNat 0x7f],
    String.mk [Char.ofNat 0x80],
    String.mk [Char.ofNat 0xd7ff],
    String.mk [Char.ofNat 0xe000],
    String.mk [Char.ofNat 0xffff],
    String.mk [Char.ofNat 0x10000],
    String.mk [Char.ofNat 0x10ffff],
    String.mk [Char.ofNat 0x65, Char.ofNat 0x301]]
  for native in samples do
    let encoded := JSString.ofLeanString native
    assert! encoded.toLeanString? == some native
    assert! String.validUTF16Guard.check encoded
    assert! stringDecodeIs (.primitive (.string encoded)) (.ok native)
    match String.encode Heap.empty native with
    | .error fault => nomatch fault
    | .ok (value, next) =>
        assert! decide (value = Value.primitive (.string encoded))
        assert! next.size == Heap.empty.size

private def testMalformedUTF16 : IO Unit := do
  let astralMax := String.mk [Char.ofNat 0x10ffff]
  let maxPair : JSString := ⟨[UInt16.ofNat 0xdbff, UInt16.ofNat 0xdfff]⟩
  assert! maxPair.toLeanString? == some astralMax
  assert! String.validUTF16Guard.check maxPair
  let malformed : List JSString := [
    ⟨[UInt16.ofNat 0xd800]⟩,
    ⟨[UInt16.ofNat 0xdc00]⟩,
    ⟨[UInt16.ofNat 0xd800, UInt16.ofNat 0x61]⟩,
    ⟨[UInt16.ofNat 0xd800, UInt16.ofNat 0xd800]⟩,
    ⟨[UInt16.ofNat 0xdc00, UInt16.ofNat 0xd800]⟩,
    ⟨[UInt16.ofNat 0x61, UInt16.ofNat 0xd800]⟩,
    ⟨[UInt16.ofNat 0xd800, UInt16.ofNat 0xdc00, UInt16.ofNat 0xd800]⟩,
    ⟨[UInt16.ofNat 0xd800, UInt16.ofNat 0xdc00, UInt16.ofNat 0xdc00]⟩]
  for encoded in malformed do
    assert! encoded.toLeanString?.isNone
    assert! stringDecodeIs (.primitive (.string encoded)) (.error .invalidUTF16)
    assert! !String.validUTF16Guard.check encoded
  assert! stringDecodeIs (.primitive (.boolean true)) (.error .expectedString)

private def testStringLaws : IO Unit := do
  let left := "A"
  let right := String.mk [Char.ofNat 0x10000]
  let leftEncoded := JSString.ofLeanString left
  let rightEncoded := JSString.ofLeanString right
  assert! leftEncoded.append rightEncoded == JSString.ofLeanString (left ++ right)
  assert! strictEqual (.primitive (.string leftEncoded)) (.primitive (.string leftEncoded))
  assert! !strictEqual (.primitive (.string leftEncoded)) (.primitive (.string rightEncoded))
  assert! sameValue (.primitive (.string leftEncoded)) (.primitive (.string leftEncoded))
  assert! sameValueZero (.primitive (.string leftEncoded)) (.primitive (.string leftEncoded))
  assert! (JS.Primitive.string leftEncoded).looseEqual (.string leftEncoded)
  assert! !(Value.primitive (.string (JSString.ofLeanString ""))).toBoolean
  assert! (Value.primitive (.string leftEncoded)).toBoolean
  assert! String.validUTF16Guard.check leftEncoded
  assert! String.validUTF16Guard.check rightEncoded
  assert! String.validUTF16Guard.check (leftEncoded.append rightEncoded)
  let guardedEvidence := String.guardedRelationExistsEvidence Heap.empty leftEncoded
    (String.validUTF16Guard_complete (JSString.toLeanString?_ofLeanString left))
  let provedEvidence := String.decodedRelationEvidence Heap.empty leftEncoded left
    (JSString.toLeanString?_ofLeanString left)
  assert! guardedEvidence.kind == .guarded
  assert! provedEvidence.kind == .proved

private def testBMPBoundary : IO Unit := do
  let bmp := String.mk [Char.ofNat 0x00, Char.ofNat 0xffff]
  let astral := String.mk [Char.ofNat 0x10000]
  let bmpEncoded := JSString.ofLeanString bmp
  let astralEncoded := JSString.ofLeanString astral
  let emptyEncoded := JSString.ofLeanString ""
  assert! String.bmpStringGuard.check bmp
  assert! String.bmpStringGuard.check ""
  assert! !String.bmpStringGuard.check astral
  assert! bmpEncoded.length == bmp.length
  assert! bmpEncoded.codeUnits[0]? == some (UInt16.ofNat 0x00)
  assert! bmpEncoded.codeUnits[1]? == some (UInt16.ofNat 0xffff)
  assert! bmpEncoded.codeUnits[bmp.length]? == none
  assert! bmpEncoded.codeUnits[bmp.length + 1]? == none
  assert! emptyEncoded.length == 0
  assert! emptyEncoded.codeUnits[0]? == none
  assert! astralEncoded.toLeanString? == some astral
  assert! astralEncoded.length == 2
  assert! astral.length == 1
  assert! astralEncoded.length != astral.length

#eval testStringBoundaries
#eval testMalformedUTF16
#eval testStringLaws
#eval testBMPBoundary

end TSLean.Refinement.Tests
