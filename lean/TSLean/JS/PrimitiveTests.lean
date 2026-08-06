import TSLean.JS.PrimitiveTheorems

namespace TSLean.JS.PrimitiveTests

private def text (value : String) : JSString := JSString.ofLeanString value

private def testParsingAndFormatting : IO Unit := do
  let cases : List (String × UInt64) :=
    [("", 0), ("  \n", 0), ("-0", 0x8000000000000000), ("0x10", 0x4030000000000000),
      ("0o10", 0x4020000000000000), ("0b10", 0x4000000000000000),
      ("1e309", 0x7ff0000000000000), ("5e-324", 1),
      ("2.2250738585072011e-308", 0x000fffffffffffff)]
  for (source, expected) in cases do assert! (JSNumber.parse (text source)).bits = expected
  for malformed in ["+", "1e", "+0x1", "0o8", "1x"] do
    assert! (JSNumber.parse (text malformed)).bits = JSNumber.canonicalNaN.bits
  assert! (JSNumber.format ⟨0x3e7ad7f29abcaf48⟩).equal (text "1e-7")
  assert! (JSNumber.format ⟨0x3eb0c6f7a0b5ed8d⟩).equal (text "0.000001")
  assert! (JSNumber.format ⟨0x444b1ae4d6e2ef50⟩).equal (text "1e+21")
  assert! (JSNumber.format ⟨1⟩).equal (text "5e-324")

private def testConversionsAndOperators : IO Unit := do
  match Primitive.toNumber .undefined with
  | .ok value => assert! value.bits = JSNumber.canonicalNaN.bits
  | .error _ => assert! false
  match Primitive.toNumber (.bigint 1) with
  | .error .bigintToNumber => pure ()
  | _ => assert! false
  match Primitive.toNumeric (.bigint 9007199254740993) with
  | .ok (.bigint 9007199254740993) => pure ()
  | _ => assert! false
  match Primitive.toNumeric (.string (text "1.5")) with
  | .ok (.number value) => assert! value.bits = 0x3ff8000000000000
  | _ => assert! false
  match Primitive.toString (.symbol (.allocated 1)) with
  | .error .symbolToString => pure ()
  | _ => assert! false
  match Primitive.toPropertyKey (.symbol (.allocated 7)) with
  | .ok (.symbol (.allocated 7)) => pure ()
  | _ => assert! false
  match Primitive.add (.string (text "x")) (.bigint 2) with
  | .ok (.primitive (.string value)) => assert! value.equal (text "x2")
  | _ => assert! false
  match Primitive.add (.bigint 1) (.number JSNumber.one) with
  | .error .mixedNumericTypes => pure ()
  | _ => assert! false
  match Primitive.add (.bigint 1) (.bigint 2) with
  | .ok (.primitive (.bigint 3)) => pure ()
  | _ => assert! false
  match Primitive.divide (.bigint (-5)) (.bigint 2) with
  | .ok (.primitive (.bigint (-2))) => pure ()
  | _ => assert! false
  match Primitive.remainder (.bigint (-5)) (.bigint 2) with
  | .ok (.primitive (.bigint (-1))) => pure ()
  | _ => assert! false
  match Primitive.divide (.bigint 1) (.bigint 0) with
  | .error .bigintDivisionByZero => pure ()
  | _ => assert! false
  match Primitive.lessThan (.string (text "a")) (.string (text "b")) with
  | .ok true => pure ()
  | _ => assert! false
  match Primitive.lessThan (.number ⟨0x4340000000000000⟩) (.bigint 9007199254740993) with
  | .ok true => pure ()
  | _ => assert! false
  match Primitive.greaterThan (.number ⟨0x3ff8000000000000⟩) (.bigint 1) with
  | .ok true => pure ()
  | _ => assert! false
  match Primitive.lessThan (.string (text "1.5")) (.bigint 2) with
  | .ok false => pure ()
  | _ => assert! false
  match CoercionFault.symbolToNumber.toAbrupt with
  | .thrown (.primitive (.string value)) =>
      assert! value.equal (text "TypeError: cannot convert Symbol to Number")
  | _ => assert! false

private def testLooseEquality : IO Unit := do
  let two53 : JSNumber := ⟨0x4340000000000000⟩
  assert! Primitive.looseEqual .null .undefined
  assert! Primitive.looseEqual (.boolean true) (.string (text "1"))
  assert! Primitive.looseEqual (.string (text "0x10")) (.bigint 16)
  assert! Primitive.looseEqual (.number two53) (.bigint 9007199254740992)
  assert! !Primitive.looseEqual (.number two53) (.bigint 9007199254740993)
  assert! !Primitive.looseEqual (.number ⟨0x3ff8000000000000⟩) (.bigint 1)
  assert! !Primitive.looseEqual (.number JSNumber.positiveInfinity) (.bigint 0)

private def testExactNumberBigIntComparison : IO Unit := do
  let two53 : JSNumber := ⟨0x4340000000000000⟩
  let aboveTwo53 : JSNumber := ⟨0x4340000000000001⟩
  let negativeTwo53 : JSNumber := ⟨0xc340000000000000⟩
  let positiveSubnormal : JSNumber := ⟨1⟩
  let negativeSubnormal : JSNumber := ⟨0x8000000000000001⟩
  assert! two53.compareBigInt 9007199254740992 = some .eq
  assert! two53.lessThanBigInt 9007199254740993
  assert! aboveTwo53.compareBigInt 9007199254740993 = some .gt
  assert! negativeTwo53.compareBigInt (-9007199254740993) = some .gt
  assert! (JSNumber.one.compareBigInt (2 ^ 1000)) = some .lt
  assert! (JSNumber.one.compareBigInt (-(2 ^ 1000))) = some .gt
  assert! positiveSubnormal.compareBigInt 0 = some .gt
  assert! negativeSubnormal.compareBigInt 0 = some .lt
  assert! (⟨0x3ff8000000000000⟩ : JSNumber).compareBigInt 1 = some .gt
  assert! JSNumber.positiveInfinity.compareBigInt (2 ^ 1000) = some .gt
  assert! JSNumber.negativeInfinity.compareBigInt (-(2 ^ 1000)) = some .lt
  assert! JSNumber.canonicalNaN.compareBigInt 0 = none

private structure ExecutableAssumption where
  name : String
  check : Bool

private def executableAssumptions : List ExecutableAssumption :=
  [{ name := "Float.ofBits/toBits preserves finite encodings", check :=
      (JSNumber.executableRoundtripCanonicalizingNaN ⟨0x3ff8000000000000⟩).bits = 0x3ff8000000000000 },
    { name := "Float arithmetic executes binary64 addition", check :=
      (JSNumber.add JSNumber.one JSNumber.one).bits = 0x4000000000000000 },
    { name := "Float arithmetic executes binary64 multiplication", check :=
      (JSNumber.multiply ⟨0x4000000000000000⟩ ⟨0x4008000000000000⟩).bits = 0x4018000000000000 },
    { name := "Float arithmetic executes binary64 subtraction", check :=
      (JSNumber.subtract ⟨0x4000000000000000⟩ JSNumber.one).bits = JSNumber.one.bits },
    { name := "Float arithmetic executes binary64 division", check :=
      (JSNumber.divide JSNumber.one ⟨0x4000000000000000⟩).bits = 0x3fe0000000000000 },
    { name := "Float comparison orders finite operands", check :=
      JSNumber.lessThan JSNumber.one ⟨0x4000000000000000⟩ },
    { name := "Float.ofScientific candidates are corrected at known boundaries", check :=
      (JSNumber.parse (text "2.2250738585072011e-308")).bits = 0x000fffffffffffff }]

private def testExecutableAssumptionLedger : IO Unit := do
  for assumption in executableAssumptions do
    if !assumption.check then throw (IO.userError assumption.name)

private def run : IO Unit := do
  testParsingAndFormatting
  testConversionsAndOperators
  testLooseEquality
  testExactNumberBigIntComparison
  testExecutableAssumptionLedger

#eval run

end TSLean.JS.PrimitiveTests
