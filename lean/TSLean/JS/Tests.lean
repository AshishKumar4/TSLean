import TSLean.JS.Conversion
import TSLean.JS.Equality
import TSLean.JS.PropertyKey

namespace TSLean.JS.Tests

private def primitive (value : Primitive) : Value := .primitive value

private def testTruthiness : IO Unit := do
  assert! !(primitive .undefined).toBoolean
  assert! !(primitive .null).toBoolean
  assert! !(primitive (.boolean false)).toBoolean
  assert! (primitive (.boolean true)).toBoolean
  assert! !(primitive (.number JSNumber.positiveZero)).toBoolean
  assert! !(primitive (.number JSNumber.negativeZero)).toBoolean
  assert! !(primitive (.number JSNumber.canonicalNaN)).toBoolean
  assert! (primitive (.number ⟨0x3ff0000000000000⟩)).toBoolean
  assert! (primitive (.number JSNumber.positiveInfinity)).toBoolean
  assert! !(primitive (.string (JSString.ofLeanString ""))).toBoolean
  assert! (primitive (.string (JSString.ofLeanString "x"))).toBoolean
  assert! !(primitive (.bigint 0)).toBoolean
  assert! (primitive (.bigint 1)).toBoolean
  assert! (primitive (.bigint (-1))).toBoolean
  assert! (primitive (.symbol (.allocated 1))).toBoolean
  -- Empty object and array literals are distinct heap objects, but both are truthy.
  assert! (Value.object ⟨100⟩).toBoolean
  assert! (Value.object ⟨101⟩).toBoolean

private def testPrimitiveEqualityMatrices : IO Unit := do
  let samples : List (Primitive × Nat) :=
    [(.undefined, 0), (.null, 1), (.boolean true, 2),
      (.number ⟨0x3ff0000000000000⟩, 3),
      (.string (JSString.ofLeanString "x"), 4), (.bigint 1, 5),
      (.symbol (.allocated 1), 6)]
  for leftSample in samples do
    let (left, leftTag) := leftSample
    for rightSample in samples do
      let (right, rightTag) := rightSample
      let expected := leftTag == rightTag
      assert! strictEqual (primitive left) (primitive right) == expected
      assert! sameValue (primitive left) (primitive right) == expected
      assert! sameValueZero (primitive left) (primitive right) == expected
  let unequalSameConstructors :=
    [(.boolean true, .boolean false),
      (.number ⟨0x3ff0000000000000⟩, .number ⟨0x4000000000000000⟩),
      (.string (JSString.ofLeanString "x"), .string (JSString.ofLeanString "y")),
      (.bigint 1, .bigint 2),
      (.symbol (.allocated 1), .symbol (.allocated 2))]
  for pair in unequalSameConstructors do
    let (left, right) := pair
    assert! !strictEqual (primitive left) (primitive right)
    assert! !sameValue (primitive left) (primitive right)
    assert! !sameValueZero (primitive left) (primitive right)

private def testIdentityEquality : IO Unit := do
  let undefined := primitive .undefined
  let null := primitive .null
  assert! !strictEqual undefined null
  assert! !strictEqual null undefined

  let arrayOne := Value.object ⟨1⟩
  let arrayTwo := Value.object ⟨2⟩
  -- Recovered corpus: `[] === []` allocates two references.
  assert! !strictEqual arrayOne arrayTwo
  assert! !sameValue arrayOne arrayTwo
  assert! !sameValueZero arrayOne arrayTwo
  assert! strictEqual arrayOne arrayOne
  assert! sameValue arrayOne arrayOne
  assert! sameValueZero arrayOne arrayOne

  let symbolOne := primitive (.symbol (.allocated 1))
  let symbolOneAgain := primitive (.symbol (.allocated 1))
  let symbolTwo := primitive (.symbol (.allocated 2))
  assert! strictEqual symbolOne symbolOneAgain
  assert! sameValue symbolOne symbolOneAgain
  assert! sameValueZero symbolOne symbolOneAgain
  assert! !strictEqual symbolOne symbolTwo
  assert! !sameValue symbolOne symbolTwo
  assert! !sameValueZero symbolOne symbolTwo
  assert! strictEqual
    (primitive (.symbol (.wellKnown .dispose)))
    (primitive (.symbol (.wellKnown .dispose)))
  assert! !strictEqual
    (primitive (.symbol (.wellKnown .dispose)))
    (primitive (.symbol (.wellKnown .asyncDispose)))

  assert! PropertyKey.equal (.symbol (.allocated 1)) (.symbol (.allocated 1))
  assert! !PropertyKey.equal (.symbol (.allocated 1)) (.symbol (.allocated 2))
  assert! PropertyKey.equal
    (.string (JSString.ofLeanString "key"))
    (.string (JSString.ofLeanString "key"))
  assert! !PropertyKey.equal
    (.string (JSString.ofLeanString "key"))
    (.symbol (.allocated 1))

private def testNumbers : IO Unit := do
  let signaling : JSNumber := ⟨0x7ff0000000000001⟩
  let negativeSignaling : JSNumber := ⟨0xfff0000000000001⟩
  let payload : JSNumber := ⟨0x7ff8000000000042⟩
  let negativePayload : JSNumber := ⟨0xfff8000000000042⟩
  let nans := [JSNumber.canonicalNaN, signaling, negativeSignaling, payload, negativePayload]
  for left in nans do
    assert! left.isNaN
    assert! !JSNumber.strictEqual left left
    for right in nans do
      assert! JSNumber.sameValue left right
      assert! JSNumber.sameValueZero left right
      assert! !strictEqual (primitive (.number left)) (primitive (.number right))
      assert! sameValue (primitive (.number left)) (primitive (.number right))
      assert! sameValueZero (primitive (.number left)) (primitive (.number right))
  assert! !signaling.sign
  assert! negativeSignaling.sign
  assert! !payload.sign
  assert! negativePayload.sign

  assert! JSNumber.strictEqual JSNumber.positiveZero JSNumber.negativeZero
  assert! !JSNumber.sameValue JSNumber.positiveZero JSNumber.negativeZero
  assert! JSNumber.sameValueZero JSNumber.positiveZero JSNumber.negativeZero
  assert! strictEqual
    (primitive (.number JSNumber.positiveZero))
    (primitive (.number JSNumber.negativeZero))
  assert! !sameValue
    (primitive (.number JSNumber.positiveZero))
    (primitive (.number JSNumber.negativeZero))
  assert! sameValueZero
    (primitive (.number JSNumber.positiveZero))
    (primitive (.number JSNumber.negativeZero))

  assert! JSNumber.positiveInfinity.isInfinite
  assert! JSNumber.negativeInfinity.isInfinite
  assert! !JSNumber.positiveInfinity.isNaN
  assert! JSNumber.strictEqual JSNumber.positiveInfinity JSNumber.positiveInfinity
  assert! !JSNumber.strictEqual JSNumber.positiveInfinity JSNumber.negativeInfinity
  assert! !JSNumber.positiveInfinity.sign
  assert! JSNumber.negativeInfinity.sign

  let nonNaNBits : List UInt64 :=
    [0x0000000000000000, 0x8000000000000000,
      0x0000000000000001, 0x000fffffffffffff,
      0x0010000000000000, 0x3ff0000000000000,
      0x7fefffffffffffff, 0x7ff0000000000000,
      0xfff0000000000000]
  for bits in nonNaNBits do
    assert! (JSNumber.executableRoundtripCanonicalizingNaN ⟨bits⟩).bits == bits
  for nan in nans do
    assert! (JSNumber.executableRoundtripCanonicalizingNaN nan).bits ==
      JSNumber.canonicalNaN.bits
    assert! (JSNumber.add nan ⟨0x3ff0000000000000⟩).bits ==
      JSNumber.canonicalNaN.bits
    assert! (JSNumber.add ⟨0x3ff0000000000000⟩ nan).bits ==
      JSNumber.canonicalNaN.bits
  assert! (JSNumber.add JSNumber.positiveInfinity JSNumber.negativeInfinity).bits ==
    JSNumber.canonicalNaN.bits
  assert! (JSNumber.add ⟨0x3ff0000000000000⟩ ⟨0x3ff0000000000000⟩).bits ==
    0x4000000000000000

private def testUTF16 : IO Unit := do
  let nul := JSString.ofLeanString (String.ofList [Char.ofNat 0x0000])
  let bmpBeforeSurrogates := JSString.ofLeanString (String.ofList [Char.ofNat 0xd7ff])
  let bmpAfterSurrogates := JSString.ofLeanString (String.ofList [Char.ofNat 0xe000])
  let bmpMax := JSString.ofLeanString (String.ofList [Char.ofNat 0xffff])
  assert! nul.equal ⟨[UInt16.ofNat 0x0000]⟩
  assert! bmpBeforeSurrogates.equal ⟨[UInt16.ofNat 0xd7ff]⟩
  assert! bmpAfterSurrogates.equal ⟨[UInt16.ofNat 0xe000]⟩
  assert! bmpMax.equal ⟨[UInt16.ofNat 0xffff]⟩

  let astralMinLean := String.ofList [Char.ofNat 0x10000]
  let astralMaxLean := String.ofList [Char.ofNat 0x10ffff]
  let astralMin := JSString.ofLeanString astralMinLean
  let astralMax := JSString.ofLeanString astralMaxLean
  assert! astralMin.equal ⟨[UInt16.ofNat 0xd800, UInt16.ofNat 0xdc00]⟩
  assert! astralMax.equal ⟨[UInt16.ofNat 0xdbff, UInt16.ofNat 0xdfff]⟩
  assert! astralMin.toLeanString? == some astralMinLean
  assert! astralMax.toLeanString? == some astralMaxLean

  let scalars := [0x0000, 0x007f, 0x0080, 0xd7ff, 0xe000, 0xffff,
    0x10000, 0x1f600, 0x10ffff]
  let valid := String.ofList (scalars.map Char.ofNat)
  assert! (JSString.ofLeanString valid).toLeanString? == some valid

  let malformed : List JSString :=
    [⟨[UInt16.ofNat 0xd800]⟩,
      ⟨[UInt16.ofNat 0xdc00]⟩,
      ⟨[UInt16.ofNat 0xd800, UInt16.ofNat 0x0061]⟩,
      ⟨[UInt16.ofNat 0xd800, UInt16.ofNat 0xd800]⟩,
      ⟨[UInt16.ofNat 0xdc00, UInt16.ofNat 0xd800]⟩,
      ⟨[UInt16.ofNat 0x0061, UInt16.ofNat 0xd800]⟩]
  for value in malformed do
    assert! value.toLeanString?.isNone

  let loneHigh : JSString := ⟨[UInt16.ofNat 0xd800]⟩
  let loneLow : JSString := ⟨[UInt16.ofNat 0xdc00]⟩
  assert! (loneHigh.append loneLow).equal astralMin
  assert! (loneHigh.append loneLow).toLeanString? == some astralMinLean

private def testTypeof : IO Unit := do
  match Primitive.typeof .undefined with | .undefined => pure () | _ => assert! false
  match Primitive.typeof .null with | .object => pure () | _ => assert! false
  match Primitive.typeof (.boolean false) with | .boolean => pure () | _ => assert! false
  match Primitive.typeof (.number JSNumber.positiveZero) with | .number => pure () | _ => assert! false
  match Primitive.typeof (.string (JSString.ofLeanString "")) with | .string => pure () | _ => assert! false
  match Primitive.typeof (.bigint 0) with | .bigint => pure () | _ => assert! false
  match Primitive.typeof (.symbol (.allocated 0)) with | .symbol => pure () | _ => assert! false

private def run : IO Unit := do
  testTruthiness
  testPrimitiveEqualityMatrices
  testIdentityEquality
  testNumbers
  testUTF16
  testTypeof

#eval run

end TSLean.JS.Tests
