import TSLean.JS.PrimitiveOperators

namespace TSLean.JS.PrimitiveScaleTests

private def asciiUnit (value : Nat) : UInt16 := UInt16.ofNat value

private def run : IO Unit := do
  let hugeInteger : JSString := ⟨List.replicate 100000 (asciiUnit 0x39)⟩
  assert! (JSNumber.parse hugeInteger).bits = JSNumber.positiveInfinity.bits

  let hugeExponent : JSString :=
    ⟨asciiUnit 0x31 :: asciiUnit 0x65 :: List.replicate 100000 (asciiUnit 0x39)⟩
  assert! (JSNumber.parse hugeExponent).bits = JSNumber.positiveInfinity.bits

  let cancellingExponent : JSString :=
    ⟨asciiUnit 0x31 :: List.replicate 100000 (asciiUnit 0x30) ++
      [asciiUnit 0x65, asciiUnit 0x2d] ++ (JSString.ofLeanString "100000").codeUnits⟩
  assert! (JSNumber.parse cancellingExponent).bits = JSNumber.one.bits

  let whitespace : JSString := ⟨List.replicate 100000 (asciiUnit 0x3000)⟩
  assert! (JSNumber.parse whitespace).bits = JSNumber.positiveZero.bits

  let malformedUTF16 : JSString := ⟨List.replicate 100000 (asciiUnit 0xd800)⟩
  assert! (JSNumber.parse malformedUTF16).bits = JSNumber.canonicalNaN.bits

  let bigintZeros : JSString := ⟨List.replicate 100000 (asciiUnit 0x30)⟩
  assert! bigintZeros.parseBigInt? = some 0

  let bigintStart ← IO.monoMsNow
  let decimalSource : JSString := ⟨List.replicate 10000 (asciiUnit 0x39)⟩
  let radixSource : JSString :=
    ⟨[asciiUnit 0x30, asciiUnit 0x78] ++ List.replicate 10000 (asciiUnit 0x66)⟩
  let some decimal := decimalSource.parseBigInt? | assert! false
  let some radix := radixSource.parseBigInt? | assert! false
  assert! decimal > 0
  assert! radix > 0
  let product := decimal * radix
  assert! product.tdiv decimal = radix
  assert! product.tmod decimal = 0
  match Numeric.add (.bigint decimal) (.bigint radix) with
  | .ok (.bigint sum) => assert! sum > decimal && sum > radix
  | _ => assert! false
  let bigintMs := (← IO.monoMsNow) - bigintStart
  assert! bigintMs < 30000
  IO.println s!"primitive-bigint-scale digits=10000 ms={bigintMs}"

#eval run

end TSLean.JS.PrimitiveScaleTests
