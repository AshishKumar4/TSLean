import TSLean.Refinement

namespace TSLean.Refinement.Tests

open TSLean.JS

namespace MathContracts

theorem math_contract_inventory (bridge : Float.BridgeSameValueRoundtrip) (root : Math.Sqrt) :
    (JSNumber.Math.PI.bits = 0x400921fb54442d18 ∧
      JSNumber.Math.E.bits = 0x4005bf0a8b145769 ∧
      JSNumber.Math.LN2.bits = 0x3fe62e42fefa39ef ∧
      JSNumber.Math.LN10.bits = 0x40026bb1bbb55516 ∧
      JSNumber.Math.SQRT2.bits = 0x3ff6a09e667f3bcd ∧
      JSNumber.Math.SQRT1_2.bits = 0x3fe6a09e667f3bcd) ∧
    JSNumber.Math.max JSNumber.one JSNumber.canonicalNaN = JSNumber.canonicalNaN ∧
    JSNumber.Math.min JSNumber.canonicalNaN JSNumber.one = JSNumber.canonicalNaN ∧
    JSNumber.Math.max JSNumber.positiveZero JSNumber.negativeZero =
      JSNumber.Math.max JSNumber.negativeZero JSNumber.positiveZero ∧
    JSNumber.Math.min JSNumber.positiveZero JSNumber.negativeZero =
      JSNumber.Math.min JSNumber.negativeZero JSNumber.positiveZero ∧
    (JSNumber.Math.max JSNumber.positiveZero JSNumber.negativeZero = JSNumber.positiveZero ∧
      JSNumber.Math.max JSNumber.negativeZero JSNumber.positiveZero = JSNumber.positiveZero ∧
      JSNumber.Math.max JSNumber.positiveZero JSNumber.positiveZero = JSNumber.positiveZero ∧
      JSNumber.Math.max JSNumber.negativeZero JSNumber.negativeZero = JSNumber.negativeZero) ∧
    (JSNumber.Math.min JSNumber.positiveZero JSNumber.negativeZero = JSNumber.negativeZero ∧
      JSNumber.Math.min JSNumber.negativeZero JSNumber.positiveZero = JSNumber.negativeZero ∧
      JSNumber.Math.min JSNumber.positiveZero JSNumber.positiveZero = JSNumber.positiveZero ∧
      JSNumber.Math.min JSNumber.negativeZero JSNumber.negativeZero = JSNumber.negativeZero) ∧
    JSNumber.Math.sign JSNumber.negativeInfinity =
      (if JSNumber.negativeInfinity.sign then JSNumber.negativeOne else JSNumber.one) ∧
    (JSNumber.Math.sign JSNumber.positiveZero = JSNumber.positiveZero ∧
      JSNumber.Math.sign JSNumber.negativeZero = JSNumber.negativeZero) ∧
    (JSNumber.Math.abs JSNumber.positiveZero = JSNumber.positiveZero ∧
      JSNumber.Math.abs JSNumber.negativeZero = JSNumber.positiveZero) ∧
    (JSNumber.Math.round ⟨0xbfe0000000000000⟩ = JSNumber.negativeZero ∧
      JSNumber.Math.round ⟨0x3fe0000000000000⟩ = ⟨0x3ff0000000000000⟩ ∧
      JSNumber.Math.round ⟨0xbff8000000000000⟩ = JSNumber.negativeOne ∧
      JSNumber.Math.round ⟨0x4004000000000000⟩ = ⟨0x4008000000000000⟩) ∧
    (JSNumber.Math.trunc ⟨0x3fe0000000000000⟩ = JSNumber.positiveZero ∧
      JSNumber.Math.trunc ⟨0xbfe0000000000000⟩ = JSNumber.negativeZero ∧
      JSNumber.Math.floor ⟨0x3fe0000000000000⟩ = JSNumber.positiveZero ∧
      JSNumber.Math.floor ⟨0xbfe0000000000000⟩ = JSNumber.negativeOne ∧
      JSNumber.Math.ceil ⟨0x3fe0000000000000⟩ = JSNumber.one ∧
      JSNumber.Math.ceil ⟨0xbfe0000000000000⟩ = JSNumber.negativeZero) ∧
    (JSNumber.Math.trunc JSNumber.positiveInfinity = JSNumber.positiveInfinity ∧
      JSNumber.Math.floor JSNumber.negativeInfinity = JSNumber.negativeInfinity ∧
      JSNumber.Math.ceil JSNumber.negativeInfinity = JSNumber.negativeInfinity ∧
      JSNumber.Math.round JSNumber.positiveInfinity = JSNumber.positiveInfinity ∧
      JSNumber.Math.abs JSNumber.negativeInfinity = JSNumber.positiveInfinity ∧
      JSNumber.Math.sign JSNumber.negativeInfinity = JSNumber.negativeOne ∧
      JSNumber.Math.max JSNumber.positiveInfinity JSNumber.negativeInfinity =
        JSNumber.positiveInfinity ∧
      JSNumber.Math.min JSNumber.positiveInfinity JSNumber.negativeInfinity =
        JSNumber.negativeInfinity) ∧
    (Float.refinement.Rel Heap.empty Math.PI (.primitive (.number JSNumber.Math.PI)) ∧
      Float.refinement.Rel Heap.empty Math.E (.primitive (.number JSNumber.Math.E)) ∧
      Float.refinement.Rel Heap.empty Math.LN2 (.primitive (.number JSNumber.Math.LN2)) ∧
      Float.refinement.Rel Heap.empty Math.LN10 (.primitive (.number JSNumber.Math.LN10)) ∧
      Float.refinement.Rel Heap.empty Math.SQRT2 (.primitive (.number JSNumber.Math.SQRT2)) ∧
      Float.refinement.Rel Heap.empty Math.SQRT1_2
        (.primitive (.number JSNumber.Math.SQRT1_2))) ∧
    (∀ value, Float.refinement.Rel Heap.empty (Math.abs value)
      (.primitive (.number (JSNumber.Math.abs (JSNumber.ofFloatCanonical value))))) ∧
    (∀ value, Float.refinement.Rel Heap.empty (Math.sign value)
      (.primitive (.number (JSNumber.Math.sign (JSNumber.ofFloatCanonical value))))) ∧
    (∀ value, Float.refinement.Rel Heap.empty (Math.trunc value)
      (.primitive (.number (JSNumber.Math.trunc (JSNumber.ofFloatCanonical value))))) ∧
    (∀ value, Float.refinement.Rel Heap.empty (Math.floor value)
      (.primitive (.number (JSNumber.Math.floor (JSNumber.ofFloatCanonical value))))) ∧
    (∀ value, Float.refinement.Rel Heap.empty (Math.ceil value)
      (.primitive (.number (JSNumber.Math.ceil (JSNumber.ofFloatCanonical value))))) ∧
    (∀ value, Float.refinement.Rel Heap.empty (Math.round value)
      (.primitive (.number (JSNumber.Math.round (JSNumber.ofFloatCanonical value))))) ∧
    (∀ left right, Float.refinement.Rel Heap.empty (Math.max left right)
      (.primitive (.number (JSNumber.Math.max (JSNumber.ofFloatCanonical left)
        (JSNumber.ofFloatCanonical right))))) ∧
    (∀ left right, Float.refinement.Rel Heap.empty (Math.min left right)
      (.primitive (.number (JSNumber.Math.min (JSNumber.ofFloatCanonical left)
        (JSNumber.ofFloatCanonical right))))) ∧
    (∀ value, Float.refinement.Rel Heap.empty (_root_.Float.sqrt value)
      (.primitive (.number (JSNumber.Math.sqrt (JSNumber.ofFloatCanonical value))))) ∧
    Math.runtimeAssumptionRegistry.length = 1 := by
  exact ⟨Math.constants_exact,
    Math.max_nan JSNumber.one JSNumber.canonicalNaN (by decide),
    Math.min_nan JSNumber.canonicalNaN JSNumber.one (by decide),
    Math.max_comm JSNumber.positiveZero JSNumber.negativeZero,
    Math.min_comm JSNumber.positiveZero JSNumber.negativeZero,
    Math.max_signedZero, Math.min_signedZero,
    Math.sign_nonzero JSNumber.negativeInfinity (by decide) (by decide),
    Math.sign_signedZero, Math.abs_signedZero, Math.round_halves, Math.integral_halves,
    Math.infinities, Math.constants_commute bridge,
    Math.abs_commutes bridge, Math.sign_commutes bridge, Math.trunc_commutes bridge,
    Math.floor_commutes bridge, Math.ceil_commutes bridge, Math.round_commutes bridge,
    Math.max_commutes bridge, Math.min_commutes bridge, Math.sqrt_commutes root, rfl⟩

end MathContracts

/-- Binary64 boundary corpus used to execute every Math operation over all ordered pairs. -/
private def mathMatrix : List JSNumber := [
  ⟨0x0000000000000000⟩,
  ⟨0x8000000000000000⟩,
  ⟨0x3ff0000000000000⟩,
  ⟨0xbff0000000000000⟩,
  ⟨0x3fe0000000000000⟩,
  ⟨0xbfe0000000000000⟩,
  ⟨0x3ff8000000000000⟩,
  ⟨0xbff8000000000000⟩,
  ⟨0x4004000000000000⟩,
  ⟨0xc004000000000000⟩,
  ⟨0x3fdfffffffffffff⟩,
  ⟨0x0000000000000001⟩,
  ⟨0x8000000000000001⟩,
  ⟨0x000fffffffffffff⟩,
  ⟨0x0010000000000000⟩,
  ⟨0x4330000000000000⟩,
  ⟨0x432fffffffffffff⟩,
  ⟨0xc32fffffffffffff⟩,
  ⟨0x7fefffffffffffff⟩,
  ⟨0xffefffffffffffff⟩,
  ⟨0x7ff0000000000000⟩,
  ⟨0xfff0000000000000⟩,
  ⟨0x7ff8000000000000⟩,
  ⟨0xfff8000000000000⟩]

private def roundtripsThroughFloat (value : JSNumber) : Bool :=
  JSNumber.sameValue (JSNumber.ofFloatCanonical value.toFloat) value

private def isIntegral (value : JSNumber) : Bool :=
  value.isNaN || value.isInfinite || (value.toInteger?).isSome

/-- Every integral rounding lands on an integer, keeps NaN and the infinities, and
survives the executable Float bridge that the native carriers cross. -/
private def testIntegralRounding : IO Unit := do
  for value in mathMatrix do
    for rounded in [JSNumber.Math.trunc value, JSNumber.Math.floor value,
        JSNumber.Math.ceil value, JSNumber.Math.round value] do
      assert! isIntegral rounded
      assert! rounded.isNaN = value.isNaN
      assert! rounded.isInfinite = value.isInfinite
      assert! roundtripsThroughFloat rounded
      assert! rounded.sign = value.sign || rounded.isNaN
    assert! JSNumber.Math.trunc (JSNumber.Math.trunc value) = JSNumber.Math.trunc value
    assert! JSNumber.Math.floor (JSNumber.Math.floor value) = JSNumber.Math.floor value
    assert! JSNumber.Math.ceil (JSNumber.Math.ceil value) = JSNumber.Math.ceil value
    assert! JSNumber.Math.round (JSNumber.Math.round value) = JSNumber.Math.round value
    if !value.isNaN then
      assert! !JSNumber.Math.orderedLess (JSNumber.Math.trunc value) (JSNumber.Math.floor value)
      assert! !JSNumber.Math.orderedLess (JSNumber.Math.ceil value) (JSNumber.Math.trunc value)

/-- `Math.abs` clears the sign and `Math.sign` reports it, both preserving NaN. -/
private def testAbsAndSign : IO Unit := do
  for value in mathMatrix do
    let magnitude := JSNumber.Math.abs value
    assert! magnitude.isNaN = value.isNaN
    assert! magnitude.sign = false
    assert! magnitude.isZero = value.isZero
    assert! roundtripsThroughFloat magnitude
    let direction := JSNumber.Math.sign value
    assert! direction.isNaN = value.isNaN
    assert! direction.isZero = value.isZero
    assert! direction.isNaN || direction.isZero ||
      direction = (if value.sign then JSNumber.negativeOne else JSNumber.one)
    assert! roundtripsThroughFloat direction

/-- `Math.max` and `Math.min` select an operand, poison on NaN, and agree with the
Float-primitive ordering wherever that ordering is defined. -/
private def testSelectionMatrix : IO Unit := do
  for left in mathMatrix do
    for right in mathMatrix do
      let greatest := JSNumber.Math.max left right
      let least := JSNumber.Math.min left right
      assert! greatest = JSNumber.Math.max right left
      assert! least = JSNumber.Math.min right left
      if left.isNaN || right.isNaN then
        assert! greatest = JSNumber.canonicalNaN
        assert! least = JSNumber.canonicalNaN
      else
        assert! greatest.bits = left.bits || greatest.bits = right.bits
        assert! least.bits = left.bits || least.bits = right.bits
        assert! !JSNumber.Math.orderedLess greatest left
        assert! !JSNumber.Math.orderedLess greatest right
        assert! !JSNumber.Math.orderedLess left least
        assert! !JSNumber.Math.orderedLess right least
        assert! JSNumber.Math.orderedLess left right = JSNumber.lessThan left right ||
          (left.isZero && right.isZero)
      assert! roundtripsThroughFloat greatest
      assert! roundtripsThroughFloat least

/-- The one assumed Math law is executed over the boundary corpus. -/
private def testSqrtBridge : IO Unit := do
  for value in mathMatrix do
    let root := JSNumber.Math.sqrt value
    assert! roundtripsThroughFloat root
    assert! JSNumber.sameValue
      (JSNumber.ofFloatCanonical (Float.sqrt value.toFloat)) root
    assert! root.isNaN = (value.isNaN || (value.sign && !value.isZero))
    if !root.isNaN then
      assert! root.sign = value.sign

/-- The native carriers agree with the committed Number operations they bridge. -/
private def testNativeCarriers : IO Unit := do
  for value in mathMatrix do
    let native := value.toFloat
    assert! JSNumber.sameValue (JSNumber.ofFloatCanonical (Math.abs native))
      (JSNumber.Math.abs (JSNumber.ofFloatCanonical native))
    assert! JSNumber.sameValue (JSNumber.ofFloatCanonical (Math.sign native))
      (JSNumber.Math.sign (JSNumber.ofFloatCanonical native))
    assert! JSNumber.sameValue (JSNumber.ofFloatCanonical (Math.trunc native))
      (JSNumber.Math.trunc (JSNumber.ofFloatCanonical native))
    assert! JSNumber.sameValue (JSNumber.ofFloatCanonical (Math.floor native))
      (JSNumber.Math.floor (JSNumber.ofFloatCanonical native))
    assert! JSNumber.sameValue (JSNumber.ofFloatCanonical (Math.ceil native))
      (JSNumber.Math.ceil (JSNumber.ofFloatCanonical native))
    assert! JSNumber.sameValue (JSNumber.ofFloatCanonical (Math.round native))
      (JSNumber.Math.round (JSNumber.ofFloatCanonical native))
    for other in mathMatrix do
      assert! JSNumber.sameValue (JSNumber.ofFloatCanonical (Math.max native other.toFloat))
        (JSNumber.Math.max (JSNumber.ofFloatCanonical native)
          (JSNumber.ofFloatCanonical other.toFloat))
      assert! JSNumber.sameValue (JSNumber.ofFloatCanonical (Math.min native other.toFloat))
        (JSNumber.Math.min (JSNumber.ofFloatCanonical native)
          (JSNumber.ofFloatCanonical other.toFloat))
  assert! JSNumber.ofFloatCanonical Math.PI = JSNumber.Math.PI
  assert! JSNumber.ofFloatCanonical Math.E = JSNumber.Math.E
  assert! JSNumber.ofFloatCanonical Math.LN2 = JSNumber.Math.LN2
  assert! JSNumber.ofFloatCanonical Math.LN10 = JSNumber.Math.LN10
  assert! JSNumber.ofFloatCanonical Math.SQRT2 = JSNumber.Math.SQRT2
  assert! JSNumber.ofFloatCanonical Math.SQRT1_2 = JSNumber.Math.SQRT1_2

/-- Exactly one Math law is assumed, and it carries no proof. -/
private def testMathAssumptionMetadata : IO Unit := do
  assert! Math.runtimeAssumptionRegistry.length = 1
  let ids := Math.runtimeAssumptionRegistry.map (·.id)
  assert! ids.eraseDups.length = ids.length
  assert! Math.sqrtEvidence.kind == .assumed
  assert! match Math.sqrtEvidence.proof? with
    | .none => true
    | .some _ => false

private def testMathRefinement : IO Unit := do
  assert! mathMatrix.length = 24
  testIntegralRounding
  testAbsAndSign
  testSelectionMatrix
  testSqrtBridge
  testNativeCarriers
  testMathAssumptionMetadata

#eval testMathRefinement

end TSLean.Refinement.Tests
