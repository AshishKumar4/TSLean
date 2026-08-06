import Init.Data.Float
import Init.Data.UInt
import TSLean.JS.String

namespace TSLean.JS

/-- An ECMAScript Number represented by its exact IEEE-754 binary64 encoding. -/
structure JSNumber where
  bits : UInt64
  deriving DecidableEq

namespace JSNumber

private def exponentMask : UInt64 := 0x7ff0000000000000
private def fractionMask : UInt64 := 0x000fffffffffffff
private def signMask : UInt64 := 0x8000000000000000

/-- Positive zero. -/
def positiveZero : JSNumber := ⟨0x0000000000000000⟩

/-- Negative zero. -/
def negativeZero : JSNumber := ⟨0x8000000000000000⟩

/-- Positive infinity. -/
def positiveInfinity : JSNumber := ⟨0x7ff0000000000000⟩

/-- Negative infinity. -/
def negativeInfinity : JSNumber := ⟨0xfff0000000000000⟩

/-- The canonical quiet NaN used when this model must produce a NaN. -/
def canonicalNaN : JSNumber := ⟨0x7ff8000000000000⟩

/-- The Number value one. -/
def one : JSNumber := ⟨0x3ff0000000000000⟩

/-- Reports whether the encoding is any positive or negative zero. -/
def isZero (value : JSNumber) : Bool :=
  (value.bits &&& ~~~signMask) == 0

/-- Reports whether the encoding is positive or negative infinity. -/
def isInfinite (value : JSNumber) : Bool :=
  (value.bits &&& exponentMask) == exponentMask &&
    (value.bits &&& fractionMask) == 0

/-- Reports whether the encoding is any quiet or signaling NaN. -/
def isNaN (value : JSNumber) : Bool :=
  (value.bits &&& exponentMask) == exponentMask &&
    (value.bits &&& fractionMask) != 0

/-- Returns the IEEE-754 sign bit, including for zero and NaN encodings. -/
def sign (value : JSNumber) : Bool := (value.bits &&& signMask) != 0

/-- ECMAScript strict numeric equality. NaN differs from everything and the two zeros agree. -/
def strictEqual (left right : JSNumber) : Bool :=
  if left.isNaN || right.isNaN then false
  else if left.isZero && right.isZero then true
  else left.bits == right.bits

/-- Strict Number equality is symmetric. -/
theorem strictEqual_symm (left right : JSNumber) : strictEqual left right = strictEqual right left := by
  unfold strictEqual
  rw [Bool.or_comm, Bool.and_comm]
  apply congrArg (fun result => if right.isNaN || left.isNaN then false
    else if right.isZero && left.isZero then true else result)
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  exact eq_comm

/-- ECMAScript SameValue numeric equality. NaNs agree and signed zeros differ. -/
def sameValue (left right : JSNumber) : Bool :=
  if left.isNaN && right.isNaN then true else left.bits == right.bits

/-- ECMAScript SameValueZero numeric equality. NaNs and signed zeros each agree. -/
def sameValueZero (left right : JSNumber) : Bool :=
  if left.isNaN && right.isNaN then true
  else if left.isZero && right.isZero then true
  else left.bits == right.bits

/-!
`Float.toBits`, `Float.ofBits`, arithmetic, comparison, and `Float.ofScientific` are
executable runtime primitives. Decimal parsing checks the `Float.ofScientific`
candidate against bounded exact integer rounding because the runtime bridge differs
at known binary64 boundaries. Formatting is an integer algorithm and does not call
`Float.toString`. No theorem in this model assigns ECMAScript semantics or roundtrip
laws to any Float primitive.
-/

private def ofFloat (value : Float) : JSNumber := ⟨value.toBits⟩

private def toFloat (value : JSNumber) : Float := Float.ofBits value.bits

private def canonicalize (value : Float) : JSNumber :=
  let result := ofFloat value
  if result.isNaN then canonicalNaN else result

/--
Passes a number through Lean's executable Float representation. NaNs are
deterministically replaced by `canonicalNaN`; non-NaN preservation is a trusted
runtime property checked by executable boundary tests, not a theorem.
-/
def executableRoundtripCanonicalizingNaN (value : JSNumber) : JSNumber :=
  if value.isNaN then canonicalNaN else ofFloat value.toFloat

/--
Executes addition through Lean's Float primitive. Any NaN input or result is
deterministically replaced by `canonicalNaN`.
-/
def add (left right : JSNumber) : JSNumber :=
  if left.isNaN || right.isNaN then
    canonicalNaN
  else
    canonicalize (Float.add left.toFloat right.toFloat)

/-- Executes subtraction through Lean's binary64 runtime primitive and canonicalizes NaN. -/
def subtract (left right : JSNumber) : JSNumber :=
  if left.isNaN || right.isNaN then canonicalNaN
  else canonicalize (Float.sub left.toFloat right.toFloat)

/-- Executes multiplication through Lean's binary64 runtime primitive and canonicalizes NaN. -/
def multiply (left right : JSNumber) : JSNumber :=
  if left.isNaN || right.isNaN then canonicalNaN
  else canonicalize (Float.mul left.toFloat right.toFloat)

/-- Executes division through Lean's binary64 runtime primitive and canonicalizes NaN. -/
def divide (left right : JSNumber) : JSNumber :=
  if left.isNaN || right.isNaN then canonicalNaN
  else canonicalize (Float.div left.toFloat right.toFloat)

/-- ECMAScript numeric less-than for two Number values. -/
def lessThan (left right : JSNumber) : Bool :=
  if left.isNaN || right.isNaN then false else decide (left.toFloat < right.toFloat)

private def ascii (value : String) : JSString := JSString.ofLeanString value

private def exactUnits (units : List UInt16) (value : String) : Bool :=
  units = (ascii value).codeUnits

private structure SignificantDigits where
  mantissa : Nat := 0
  count : Nat := 0
  kept : Nat := 0
  seenNonzero : Bool := false
  discardedNonzero : Bool := false

/- Binary64 rounding boundaries have terminating decimals within 1075 places. Keeping
1100 significant digits plus a sticky digit distinguishes either side of every boundary. -/
private def maxParserDigits : Nat := 1100

private def collectSignificant (units : List UInt16) : SignificantDigits :=
  units.foldl (fun state unit =>
    let digit := unit.toNat - 0x30
    if !state.seenNonzero && digit = 0 then state
    else if state.kept < maxParserDigits then
      { state with
        mantissa := state.mantissa * 10 + digit
        count := state.count + 1
        kept := state.kept + 1
        seenNonzero := true }
    else
      { state with
        count := state.count + 1
        seenNonzero := true
        discardedNonzero := state.discardedNonzero || digit != 0 })
    {}

private def decimalDigits (units : List UInt16) : List UInt16 × List UInt16 :=
  units.span fun unit => JSString.asciiDigitValue? 10 unit |>.isSome

private def parseExponent? (cap : Nat) (units : List UInt16) : Option Int :=
  let (negative, digits) :=
    match units with
    | unit :: rest =>
        if unit.toNat = 0x2b then (false, rest)
        else if unit.toNat = 0x2d then (true, rest)
        else (false, units)
    | [] => (false, [])
  if digits.isEmpty then none
  else do
    let magnitude ← digits.foldlM (fun value unit => do
      let digit ← JSString.asciiDigitValue? 10 unit
      pure (min cap (value * 10 + digit))) 0
    pure (if negative then -Int.ofNat magnitude else Int.ofNat magnitude)

private structure DecimalParts where
  negative : Bool
  digits : List UInt16
  fractionalCount : Nat
  exponent : Int

private def parseDecimalParts? (units : List UInt16) : Option DecimalParts := do
  let (negative, body) :=
    match units with
    | unit :: rest =>
        if unit.toNat = 0x2b then (false, rest)
        else if unit.toNat = 0x2d then (true, rest)
        else (false, units)
    | [] => (false, [])
  let (integerDigits, afterInteger) := decimalDigits body
  let (fractionDigits, afterFraction) :=
    match afterInteger with
    | dot :: rest => if dot.toNat = 0x2e then decimalDigits rest else ([], afterInteger)
    | [] => ([], [])
  if integerDigits.isEmpty && fractionDigits.isEmpty then none else pure ()
  let exponent ←
    match afterFraction with
    | marker :: rest =>
        if marker.toNat = 0x45 || marker.toNat = 0x65 then
          parseExponent? (units.length + 400) rest
        else none
    | [] => some 0
  let digits := integerDigits ++ fractionDigits
  pure (DecimalParts.mk negative digits fractionDigits.length exponent)

private def signedFloat (negative : Bool) (value : Float) : JSNumber :=
  canonicalize (if negative then Float.neg value else value)

private def nonnegativeBinaryExponent
    (numerator : Nat) (scaled exponent : Nat) : Nat → Nat
  | 0 => exponent
  | fuel + 1 =>
      if numerator < scaled * 2 then exponent
      else nonnegativeBinaryExponent numerator (scaled * 2) (exponent + 1) fuel

private def negativeBinaryExponent
    (denominator : Nat) (scaled exponent : Nat) : Nat → Nat
  | 0 => exponent
  | fuel + 1 =>
      if scaled ≥ denominator then exponent
      else negativeBinaryExponent denominator (scaled * 2) (exponent + 1) fuel

private def ratioBinaryExponent (numerator denominator : Nat) : Int :=
  if numerator ≥ denominator then
    Int.ofNat (nonnegativeBinaryExponent numerator denominator 0 1024)
  else
    Int.neg (Int.ofNat (negativeBinaryExponent denominator (numerator * 2) 1 1075))

private def roundedQuotient (numerator denominator : Nat) : Nat :=
  let quotient := numerator / denominator
  let remainder := numerator % denominator
  if remainder * 2 < denominator then quotient
  else if remainder * 2 > denominator then quotient + 1
  else if quotient % 2 = 0 then quotient else quotient + 1

private def exactPositiveRatio (negative : Bool) (numerator denominator : Nat) : JSNumber :=
  if numerator = 0 then if negative then negativeZero else positiveZero
  else
    let exponent := ratioBinaryExponent numerator denominator
    let magnitude :=
      if exponent < -1022 then
        let significand := roundedQuotient (numerator * 2 ^ 1074) denominator
        if significand = 0 then positiveZero
        else ⟨UInt64.ofNat significand⟩
      else
        let shift := 52 - exponent
        let significand :=
          if shift < 0 then roundedQuotient numerator (denominator * 2 ^ shift.natAbs)
          else roundedQuotient (numerator * 2 ^ shift.natAbs) denominator
        let (significand, exponent) :=
          if significand = 2 ^ 53 then (2 ^ 52, exponent + 1)
          else (significand, exponent)
        if exponent > 1023 then positiveInfinity
        else
          let biasedExponent := (exponent + 1023).natAbs
          ⟨UInt64.ofNat (biasedExponent * 2 ^ 52 + significand - 2 ^ 52)⟩
    if negative then ⟨magnitude.bits ||| signMask⟩ else magnitude

private def roundedDecimal
    (negative : Bool) (mantissa : Nat) (decimalExponent : Int) : JSNumber :=
  let bridge := signedFloat negative
    (Float.ofScientific mantissa (decimalExponent < 0) decimalExponent.natAbs)
  let exact :=
    if decimalExponent < 0 then
      exactPositiveRatio negative mantissa (10 ^ decimalExponent.natAbs)
    else
      exactPositiveRatio negative (mantissa * 10 ^ decimalExponent.natAbs) 1
  if bridge.bits = exact.bits then bridge else exact

private def decimalNumber (parts : DecimalParts) : JSNumber :=
  let significant := collectSignificant parts.digits
  if !significant.seenNonzero then
    if parts.negative then negativeZero else positiveZero
  else
    let netExponent := parts.exponent - Int.ofNat parts.fractionalCount
    let adjustedExponent := netExponent + Int.ofNat significant.count - 1
    if adjustedExponent > 308 then
      if parts.negative then negativeInfinity else positiveInfinity
    else if adjustedExponent < -325 then
      if parts.negative then negativeZero else positiveZero
    else
      let discarded := significant.count - significant.kept
      let (mantissa, decimalExponent) :=
        if significant.discardedNonzero then
          (significant.mantissa * 10 + 1, netExponent + Int.ofNat discarded - 1)
        else
          (significant.mantissa, netExponent + Int.ofNat discarded)
      roundedDecimal parts.negative mantissa decimalExponent

private def radixNumber? (radix : Nat) (units : List UInt16) : Option JSNumber := do
  if units.isEmpty then none else pure ()
  let (valid, value, significantCount) := units.foldl (fun (valid, value, count) unit =>
    match JSString.asciiDigitValue? radix unit with
    | none => (false, value, count)
    | some digit =>
        if !valid then (false, value, count)
        else if count = 0 && digit = 0 then (true, value, 0)
        else if count < maxParserDigits then (true, value * radix + digit, count + 1)
        else (true, value, count + 1)) (true, 0, 0)
  if !valid then none
  else if significantCount > maxParserDigits then some positiveInfinity
  else some (roundedDecimal false value 0)

/-- ECMAScript StringNumericValue parsing over exact UTF-16 code units. -/
def parse (input : JSString) : JSNumber :=
  let units := input.trim.codeUnits
  if units.isEmpty then positiveZero
  else if exactUnits units "Infinity" || exactUnits units "+Infinity" then positiveInfinity
  else if exactUnits units "-Infinity" then negativeInfinity
  else
    match units with
    | zero :: marker :: rest =>
        if zero.toNat = 0x30 then
          let radix := match marker.toNat with
            | 0x58 | 0x78 => some 16
            | 0x4f | 0x6f => some 8
            | 0x42 | 0x62 => some 2
            | _ => none
          match radix with
          | some base => (radixNumber? base rest).getD canonicalNaN
          | none => (parseDecimalParts? units).map decimalNumber |>.getD canonicalNaN
        else
          (parseDecimalParts? units).map decimalNumber |>.getD canonicalNaN
    | _ => (parseDecimalParts? units).map decimalNumber |>.getD canonicalNaN

private def finiteRatio (value : JSNumber) : Nat × Nat :=
  let rawExponent := ((value.bits &&& exponentMask) >>> 52).toNat
  let fraction := (value.bits &&& fractionMask).toNat
  let significand := if rawExponent = 0 then fraction else 2 ^ 52 + fraction
  let binaryExponent : Int :=
    if rawExponent = 0 then -1074 else Int.ofNat rawExponent - 1075
  if binaryExponent < 0 then (significand, 2 ^ binaryExponent.natAbs)
  else (significand * 2 ^ binaryExponent.natAbs, 1)

/-- ECMAScript Number remainder, computed exactly from binary64 rationals before final rounding. -/
def remainder (left right : JSNumber) : JSNumber :=
  if left.isNaN || right.isNaN || left.isInfinite || right.isZero then canonicalNaN
  else if left.isZero || right.isInfinite then left
  else
    let (leftNumerator, leftDenominator) := finiteRatio left
    let (rightNumerator, rightDenominator) := finiteRatio right
    let quotient :=
      (leftNumerator * rightDenominator) / (leftDenominator * rightNumerator)
    let numerator := leftNumerator * rightDenominator -
      quotient * leftDenominator * rightNumerator
    exactPositiveRatio left.sign numerator (leftDenominator * rightDenominator)

/-- Returns the exact mathematical integer represented by a finite integral Number. -/
def toInteger? (value : JSNumber) : Option Int :=
  if value.isNaN || value.isInfinite then none
  else
    let (numerator, denominator) := finiteRatio value
    if numerator % denominator != 0 then none
    else
      let magnitude := Int.ofNat (numerator / denominator)
      some (if value.sign then -magnitude else magnitude)

/-- Exact mathematical ordering between a Number and a BigInt; NaN is unordered. -/
def compareBigInt (number : JSNumber) (bigint : Int) : Option Ordering :=
  if number.isNaN then none
  else if number.isInfinite then some (if number.sign then .lt else .gt)
  else if number.isZero then
    some (if bigint < 0 then .gt else if bigint = 0 then .eq else .lt)
  else
    let (numerator, denominator) := finiteRatio number
    if number.sign then
      if bigint ≥ 0 then some .lt
      else some (compare (bigint.natAbs * denominator) numerator)
    else
      if bigint < 0 then some .gt
      else some (compare numerator (bigint.natAbs * denominator))

/-- Exact mathematical equality between a Number and a BigInt. -/
def equalsBigInt (number : JSNumber) (bigint : Int) : Bool :=
  number.compareBigInt bigint == some .eq

/-- Exact Number-less-than-BigInt comparison. NaN is false. -/
def lessThanBigInt (number : JSNumber) (bigint : Int) : Bool :=
  number.compareBigInt bigint == some .lt

/-- Exact BigInt-less-than-Number comparison. NaN is false. -/
def bigIntLessThan (bigint : Int) (number : JSNumber) : Bool :=
  number.compareBigInt bigint == some .gt

private def nonnegativeDecimalExponent
    (numerator : Nat) : Nat → Nat → Nat → Nat
  | _, exponent, 0 => exponent
  | scaled, exponent, fuel + 1 =>
      if numerator < scaled * 10 then exponent
      else nonnegativeDecimalExponent numerator (scaled * 10) (exponent + 1) fuel

private def negativeDecimalExponent
    (denominator : Nat) : Nat → Nat → Nat → Nat
  | _, exponent, 0 => exponent
  | scaled, exponent, fuel + 1 =>
      if scaled ≥ denominator then exponent
      else negativeDecimalExponent denominator (scaled * 10) (exponent + 1) fuel

private def decimalExponent (numerator denominator : Nat) : Int :=
  if numerator ≥ denominator then
    Int.ofNat (nonnegativeDecimalExponent numerator denominator 0 309)
  else
    -(Int.ofNat (negativeDecimalExponent denominator (numerator * 10) 1 325))

private def roundedSignificand
    (numerator denominator : Nat) (exponent : Int) (digits : Nat) : Nat × Int :=
  let power := Int.ofNat (digits - 1) - exponent
  let rounded :=
    if power < 0 then roundedQuotient numerator (denominator * 10 ^ power.natAbs)
    else roundedQuotient (numerator * 10 ^ power.natAbs) denominator
  (rounded, exponent - Int.ofNat (digits - 1))

private def candidateNumber (significand : Nat) (exponent : Int) : JSNumber :=
  roundedDecimal false significand exponent

private def shortestDecimal (value : JSNumber) : Nat × Int :=
  let (numerator, denominator) := finiteRatio value
  let exponent := decimalExponent numerator denominator
  let rec loop (digits : Nat) : Nat → Nat × Int
    | 0 => roundedSignificand numerator denominator exponent 17
    | fuel + 1 =>
        let (significand, decimalPower) :=
          roundedSignificand numerator denominator exponent digits
        let candidates := [significand, significand - 1, significand + 1]
        match candidates.find? fun candidate =>
          (candidateNumber candidate decimalPower).bits = (value.bits &&& ~~~signMask) with
        | some candidate => (candidate, decimalPower)
        | none => loop (digits + 1) fuel
  loop 1 17

private def normalizeDecimal (significand : Nat) (power : Int) : Nat × Int :=
  let rec loop : Nat → Int → Nat → Nat × Int
    | value, exponent, 0 => (value, exponent)
    | value, exponent, fuel + 1 =>
        if value % 10 = 0 then loop (value / 10) (exponent + 1) fuel
        else (value, exponent)
  loop significand power 17

private def zeros (count : Nat) : String := String.ofList (List.replicate count '0')

private def renderFinite (value : JSNumber) : String :=
  let (rawSignificand, rawDecimalPower) := shortestDecimal value
  let (significand, decimalPower) := normalizeDecimal rawSignificand rawDecimalPower
  let digits := significand.repr
  let exponent := decimalPower + Int.ofNat digits.length - 1
  let body :=
    if exponent ≥ 0 && exponent ≤ 20 then
      let integerDigits := exponent.natAbs + 1
      if digits.length ≤ integerDigits then digits ++ zeros (integerDigits - digits.length)
      else (digits.take integerDigits).toString ++ "." ++ digits.drop integerDigits
    else if exponent < 0 && exponent ≥ -6 then
      "0." ++ zeros (exponent.natAbs - 1) ++ digits
    else
      let fraction := if digits.length = 1 then "" else "." ++ digits.drop 1
      let exponentSign := if exponent < 0 then "-" else "+"
      (digits.take 1).toString ++ fraction ++ "e" ++ exponentSign ++ exponent.natAbs.repr
  if value.sign then "-" ++ body else body

/-- ECMAScript Number::toString in radix 10. Signed zero is rendered as `0`. -/
def format (value : JSNumber) : JSString :=
  if value.isNaN then ascii "NaN"
  else if value.isInfinite then ascii (if value.sign then "-Infinity" else "Infinity")
  else if value.isZero then ascii "0"
  else ascii (renderFinite value)

end JSNumber
end TSLean.JS
