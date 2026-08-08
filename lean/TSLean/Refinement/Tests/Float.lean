import TSLean.Refinement

namespace TSLean.Refinement.Tests

open TSLean.JS

namespace FloatContracts

variable (bridge : Float.BridgeSameValueRoundtrip)
  (add : Float.Add) (subtract : Float.Subtract) (multiply : Float.Multiply)
  (divide : Float.Divide) (lessThan : Float.LessThan)
  (lessThanOrEqual : Float.LessThanOrEqual) (strictEqual : Float.StrictEqual)

theorem float_contract_inventory :
    (∀ (heap : Heap) (native : _root_.Float), heap.WellFormed →
      ∃ value next decoded,
        (Float.codec bridge).encode heap native = .ok (value, next) ∧
        value = .primitive (.number (JSNumber.ofFloatCanonical native)) ∧
        next = heap ∧
        (Float.codec bridge).decode next value = .ok decoded ∧
        Float.refinement.Rel next native value ∧ Float.refinement.Rel next decoded value) ∧
    (∀ left right, Float.refinement.Rel Heap.empty (Float.remainder left right)
      (.primitive (.number (JSNumber.remainder (JSNumber.ofFloatCanonical left)
        (JSNumber.ofFloatCanonical right))))) ∧
    Float.runtimeAssumptionRegistry.length = 8 := by
  exact ⟨fun heap native => Float.codec_observational_roundtrip bridge heap native,
    Float.remainder_commutes bridge, rfl⟩

example : (Float.provedAdd add).kind = .proved := rfl

example (left right : _root_.Float) :
    Float.refinement.Rel Heap.empty (_root_.Float.add left right)
      (.primitive (.number (JSNumber.add (JSNumber.ofFloatCanonical left)
        (JSNumber.ofFloatCanonical right)))) := Float.add_commutes add left right

end FloatContracts

private def decodeBits (value : Value) : Except Float.DecodeFault UInt64 :=
  (Float.decode Heap.empty value).map _root_.Float.toBits

private def decodeBitsIs (value : Value) (expected : Except Float.DecodeFault UInt64) : Bool :=
  match decodeBits value, expected with
  | .ok actual, .ok wanted => actual == wanted
  | .error actual, .error wanted => actual == wanted
  | _, _ => false

private def decodeIs (value : Value) (expected : Except Float.DecodeFault _root_.Float) : Bool :=
  match Float.decode Heap.empty value, expected with
  | .ok actual, .ok wanted => actual.toBits == wanted.toBits
  | .error actual, .error wanted => actual == wanted
  | _, _ => false

private def testFloatCodecBoundaries : IO Unit := do
  let samples : List UInt64 := [
    0x0000000000000000,
    0x8000000000000000,
    0x7ff0000000000000,
    0xfff0000000000000,
    0x0000000000000001,
    0x8000000000000001,
    0x7fefffffffffffff,
    0xffefffffffffffff,
    0x3ff0000000000000]
  for bits in samples do
    let native := _root_.Float.ofBits bits
    let encoded := JSNumber.ofFloatCanonical native
    assert! encoded.bits = bits
    assert! decodeBitsIs (.primitive (.number encoded)) (.ok bits)
    match Float.encode Heap.empty native with
    | .error fault => nomatch fault
    | .ok (value, next) =>
        assert! value = .primitive (.number encoded)
        assert! next.size = Heap.empty.size
  let nanBits : List UInt64 := [
    0x7ff0000000000001,
    0x7ff8000000000000,
    0x7fffffffffffffff,
    0xfff0000000000001,
    0xfff8000000000000,
    0xffffffffffffffff]
  for bits in nanBits do
    let raw : JSNumber := ⟨bits⟩
    match Float.decode Heap.empty (.primitive (.number raw)) with
    | .error fault => throw (IO.userError s!"unexpected Float decode fault: {repr fault}")
    | .ok decoded =>
        let canonical := JSNumber.ofFloatCanonical decoded
        assert! canonical.bits = JSNumber.canonicalNaN.bits
        assert! JSNumber.sameValue canonical raw
  assert! decodeBitsIs (.primitive (.number JSNumber.positiveZero))
    (.ok JSNumber.positiveZero.bits)
  assert! decodeBitsIs (.primitive (.number JSNumber.negativeZero))
    (.ok JSNumber.negativeZero.bits)

private def testFloatDecodeFaults : IO Unit := do
  assert! decodeIs (.primitive .undefined) (.error .expectedNumber)
  assert! decodeIs (.primitive .null) (.error .expectedNumber)
  assert! decodeIs (.primitive (.boolean true)) (.error .expectedNumber)
  assert! decodeIs (.primitive (.string (JSString.ofLeanString "1"))) (.error .expectedNumber)
  assert! decodeIs (.primitive (.bigint 1)) (.error .expectedNumber)
  assert! decodeIs (.object ⟨0⟩) (.error .expectedNumber)

/-- Binary64 boundary corpus used to execute every Float runtime law over all 225 ordered pairs. -/
private def floatMatrix : List JSNumber := [
  ⟨0x0000000000000000⟩,
  ⟨0x8000000000000000⟩,
  ⟨0x3ff0000000000000⟩,
  ⟨0xbff0000000000000⟩,
  ⟨0x0000000000000001⟩,
  ⟨0x000fffffffffffff⟩,
  ⟨0x0010000000000000⟩,
  ⟨0x7fefffffffffffff⟩,
  ⟨0xffefffffffffffff⟩,
  ⟨0x7ff0000000000000⟩,
  ⟨0xfff0000000000000⟩,
  ⟨0x7ff0000000000001⟩,
  ⟨0x7ff8000000000000⟩,
  ⟨0xfff0000000000001⟩,
  ⟨0xfff8000000000000⟩]

private def testFloatOperationMatrix : IO Unit := do
  let start ← IO.monoMsNow
  assert! floatMatrix.length = 15
  for rawLeft in floatMatrix do
    let nativeLeft := rawLeft.toFloat
    let left := JSNumber.ofFloatCanonical nativeLeft
    assert! JSNumber.sameValue left rawLeft
    for rawRight in floatMatrix do
      let nativeRight := rawRight.toFloat
      let right := JSNumber.ofFloatCanonical nativeRight
      assert! JSNumber.sameValue
        (JSNumber.ofFloatCanonical (_root_.Float.add nativeLeft nativeRight))
        (JSNumber.add left right)
      assert! JSNumber.sameValue
        (JSNumber.ofFloatCanonical (_root_.Float.sub nativeLeft nativeRight))
        (JSNumber.subtract left right)
      assert! JSNumber.sameValue
        (JSNumber.ofFloatCanonical (_root_.Float.mul nativeLeft nativeRight))
        (JSNumber.multiply left right)
      assert! JSNumber.sameValue
        (JSNumber.ofFloatCanonical (_root_.Float.div nativeLeft nativeRight))
        (JSNumber.divide left right)
      assert! decide (nativeLeft < nativeRight) == JSNumber.lessThan left right
      assert! decide (nativeLeft ≤ nativeRight) ==
        (!JSNumber.lessThan right left && !left.isNaN && !right.isNaN)
      assert! _root_.Float.beq nativeLeft nativeRight == JSNumber.strictEqual left right
      let remainder := JSNumber.remainder left right
      assert! JSNumber.sameValue (JSNumber.ofFloatCanonical remainder.toFloat) remainder
      assert! JSNumber.sameValue
        (JSNumber.ofFloatCanonical (Float.remainder nativeLeft nativeRight)) remainder
  let elapsed := (← IO.monoMsNow) - start
  assert! elapsed < 30000

private def testFloatObservations : IO Unit := do
  let positiveZero := _root_.Float.ofBits JSNumber.positiveZero.bits
  let negativeZero := _root_.Float.ofBits JSNumber.negativeZero.bits
  let nan := _root_.Float.ofBits 0xfff0000000000001
  assert! !(Value.primitive (.number (JSNumber.ofFloatCanonical positiveZero))).toBoolean
  assert! !(Value.primitive (.number (JSNumber.ofFloatCanonical negativeZero))).toBoolean
  assert! !(Value.primitive (.number (JSNumber.ofFloatCanonical nan))).toBoolean
  assert! !sameValue (.primitive (.number (JSNumber.ofFloatCanonical positiveZero)))
    (.primitive (.number (JSNumber.ofFloatCanonical negativeZero)))
  assert! sameValueZero (.primitive (.number (JSNumber.ofFloatCanonical positiveZero)))
    (.primitive (.number (JSNumber.ofFloatCanonical negativeZero)))
  assert! sameValue (.primitive (.number (JSNumber.ofFloatCanonical nan)))
    (.primitive (.number JSNumber.canonicalNaN))

private def assumedHasNoProof (evidence : Evidence claim) : Bool :=
  evidence.kind == .assumed && match evidence.proof? with
    | .none => true
    | .some _ => false

private def testFloatAssumptionMetadata : IO Unit := do
  assert! Float.runtimeAssumptionRegistry.length = 8
  let ids := Float.runtimeAssumptionRegistry.map (·.id)
  assert! ids.eraseDups.length = ids.length
  assert! assumedHasNoProof Float.bridgeSameValueRoundtripEvidence
  assert! assumedHasNoProof Float.addEvidence
  assert! assumedHasNoProof Float.subtractEvidence
  assert! assumedHasNoProof Float.multiplyEvidence
  assert! assumedHasNoProof Float.divideEvidence
  assert! assumedHasNoProof Float.lessThanEvidence
  assert! assumedHasNoProof Float.lessThanOrEqualEvidence
  assert! assumedHasNoProof Float.strictEqualEvidence

private def testFloatRefinement : IO Unit := do
  testFloatCodecBoundaries
  testFloatDecodeFaults
  testFloatOperationMatrix
  testFloatObservations
  testFloatAssumptionMetadata

#eval testFloatRefinement

end TSLean.Refinement.Tests
