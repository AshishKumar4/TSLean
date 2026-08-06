import TSLean.JS.Equality
import TSLean.JS.PrimitiveOperators

namespace TSLean.JS

namespace Primitive

/-- Undefined converts to the canonical model NaN. -/
theorem toNumber_undefined : toNumber .undefined = .ok JSNumber.canonicalNaN := rfl

/-- Null converts to positive zero. -/
theorem toNumber_null : toNumber .null = .ok JSNumber.positiveZero := rfl

/-- Boolean false converts to positive zero. -/
theorem toNumber_false : toNumber (.boolean false) = .ok JSNumber.positiveZero := rfl

/-- Boolean true converts to one. -/
theorem toNumber_true : toNumber (.boolean true) = .ok JSNumber.one := rfl

/-- ToNumber preserves every Number encoding exactly. -/
theorem toNumber_number (value : JSNumber) : toNumber (.number value) = .ok value := rfl

/-- String ToNumber is exactly StringNumericValue parsing. -/
theorem toNumber_string (value : JSString) : toNumber (.string value) = .ok (JSNumber.parse value) := rfl

/-- BigInt ToNumber returns its typed TypeError fault. -/
theorem toNumber_bigint (value : Int) : toNumber (.bigint value) = .error .bigintToNumber := rfl

/-- Symbol ToNumber returns its typed TypeError fault. -/
theorem toNumber_symbol (id : SymbolId) : toNumber (.symbol id) = .error .symbolToNumber := rfl

/-- Undefined ToNumeric is canonical NaN in the Number domain. -/
theorem toNumeric_undefined : toNumeric .undefined = .ok (.number JSNumber.canonicalNaN) := rfl

/-- Null ToNumeric is positive zero in the Number domain. -/
theorem toNumeric_null : toNumeric .null = .ok (.number JSNumber.positiveZero) := rfl

/-- Boolean ToNumeric uses its exact Number conversion. -/
theorem toNumeric_boolean (value : Bool) :
    toNumeric (.boolean value) = .ok (.number (if value then JSNumber.one else JSNumber.positiveZero)) := by
  cases value <;> rfl

/-- Number ToNumeric preserves its exact encoding. -/
theorem toNumeric_number (value : JSNumber) : toNumeric (.number value) = .ok (.number value) := rfl

/-- String ToNumeric uses StringNumericValue in the Number domain. -/
theorem toNumeric_string (value : JSString) :
    toNumeric (.string value) = .ok (.number (JSNumber.parse value)) := rfl

/-- BigInt ToNumeric preserves the arbitrary-size integer. -/
theorem toNumeric_bigint (value : Int) : toNumeric (.bigint value) = .ok (.bigint value) := rfl

/-- Symbol ToNumeric returns its typed TypeError fault. -/
theorem toNumeric_symbol (id : SymbolId) : toNumeric (.symbol id) = .error .symbolToNumber := rfl

/-- ToString preserves every ECMAScript string code unit exactly. -/
theorem toString_string (value : JSString) : toString (.string value) = .ok value := rfl

/-- Undefined has its standard primitive string spelling. -/
theorem toString_undefined : toString .undefined = .ok (JSString.ofLeanString "undefined") := rfl

/-- Null has its standard primitive string spelling. -/
theorem toString_null : toString .null = .ok (JSString.ofLeanString "null") := rfl

/-- Boolean false has its standard primitive string spelling. -/
theorem toString_false : toString (.boolean false) = .ok (JSString.ofLeanString "false") := rfl

/-- Boolean true has its standard primitive string spelling. -/
theorem toString_true : toString (.boolean true) = .ok (JSString.ofLeanString "true") := rfl

/-- Number ToString delegates exactly to the Number formatter. -/
theorem toString_number (value : JSNumber) : toString (.number value) = .ok value.format := rfl

/-- BigInt ToString is signed decimal integer rendering. -/
theorem toString_bigint (value : Int) :
    toString (.bigint value) = .ok (JSString.ofLeanString value.repr) := rfl

/-- Symbol ToString returns its typed TypeError fault. -/
theorem toString_symbol (id : SymbolId) : toString (.symbol id) = .error .symbolToString := rfl

/-- Primitive ToPropertyKey preserves symbol identity. -/
theorem toPropertyKey_symbol (id : SymbolId) :
    toPropertyKey (.symbol id) = .ok (.symbol id) := rfl

/-- Primitive ToPropertyKey stringifies every non-symbol primitive. -/
theorem toPropertyKey_nonsymbol (value : Primitive)
    (notSymbol : ∀ id, value ≠ .symbol id) :
    toPropertyKey value = value.toString.map .string := by
  cases value <;> simp_all [toPropertyKey]

/-- Primitive loose equality is symmetric. -/
theorem looseEqual_symm (left right : Primitive) : left.looseEqual right = right.looseEqual left := by
  cases left <;> cases right <;> simp only [looseEqual]
  · apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    exact eq_comm

  · exact JSNumber.strictEqual_symm _ _
  · exact JSString.equal_symm _ _
  · apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    exact eq_comm
  · apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact eq_comm

/-- Primitive BigInt addition returns an exact BigInt value. -/
theorem add_bigint (left right : Int) :
    add (.bigint left) (.bigint right) = .ok (.primitive (.bigint (left + right))) := rfl

/-- String/BigInt relational comparison uses exact StringToBigInt grammar. -/
theorem relational_string_bigint (left : JSString) (right : Int) :
    abstractRelationalComparison (.string left) (.bigint right) =
      .ok (left.parseBigInt?.map (· < right)) := rfl

end Primitive

namespace Numeric

/-- BigInt addition is exact integer addition. -/
theorem add_bigint (left right : Int) :
    add (.bigint left) (.bigint right) = .ok (.bigint (left + right)) := rfl

/-- BigInt subtraction is exact integer subtraction. -/
theorem subtract_bigint (left right : Int) :
    subtract (.bigint left) (.bigint right) = .ok (.bigint (left - right)) := rfl

/-- BigInt multiplication is exact integer multiplication. -/
theorem multiply_bigint (left right : Int) :
    multiply (.bigint left) (.bigint right) = .ok (.bigint (left * right)) := rfl

/-- Nonzero BigInt division is truncating integer division. -/
theorem divide_bigint (left right : Int) (nonzero : right ≠ 0) :
    divide (.bigint left) (.bigint right) = .ok (.bigint (left.tdiv right)) := by
  cases right <;> simp_all [divide]

/-- Nonzero BigInt remainder is truncating integer remainder. -/
theorem remainder_bigint (left right : Int) (nonzero : right ≠ 0) :
    remainder (.bigint left) (.bigint right) = .ok (.bigint (left.tmod right)) := by
  cases right <;> simp_all [remainder]

/-- BigInt division by zero returns the typed RangeError fault. -/
theorem divide_bigint_zero (value : Int) :
    divide (.bigint value) (.bigint 0) = .error .bigintDivisionByZero := rfl

/-- BigInt remainder by zero returns the typed RangeError fault. -/
theorem remainder_bigint_zero (value : Int) :
    remainder (.bigint value) (.bigint 0) = .error .bigintDivisionByZero := rfl

/-- Number and BigInt arithmetic domains cannot be mixed. -/
theorem add_mixed (number : JSNumber) (bigint : Int) :
    add (.number number) (.bigint bigint) = .error .mixedNumericTypes := rfl

/-- BigInt relational comparison is exact integer ordering. -/
theorem lessThan?_bigint (left right : Int) :
    lessThan? (.bigint left) (.bigint right) = some (decide (left < right)) := rfl

end Numeric

namespace JSNumber

/-- Canonical NaN has the standard Number string spelling. -/
theorem format_canonicalNaN : format canonicalNaN = JSString.ofLeanString "NaN" := rfl

/-- Positive infinity has the standard Number string spelling. -/
theorem format_positiveInfinity : format positiveInfinity = JSString.ofLeanString "Infinity" := rfl

/-- Negative infinity has the standard Number string spelling. -/
theorem format_negativeInfinity : format negativeInfinity = JSString.ofLeanString "-Infinity" := rfl

/-- Positive zero formats without a sign. -/
theorem format_positiveZero : format positiveZero = JSString.ofLeanString "0" := rfl

/-- Negative zero also formats without a sign. -/
theorem format_negativeZero : format negativeZero = JSString.ofLeanString "0" := rfl

/-- Canonical NaN is unordered with every BigInt. -/
theorem compareBigInt_canonicalNaN (value : Int) : compareBigInt canonicalNaN value = none := by
  have nan : canonicalNaN.isNaN = true := by decide
  simp [compareBigInt, nan]

/-- Positive infinity is greater than every BigInt. -/
theorem compareBigInt_positiveInfinity (value : Int) :
    compareBigInt positiveInfinity value = some .gt := by
  have notNaN : positiveInfinity.isNaN = false := by decide
  have infinite : positiveInfinity.isInfinite = true := by decide
  have positive : positiveInfinity.sign = false := by decide
  simp [compareBigInt, notNaN, infinite, positive]

/-- Positive zero equals BigInt zero. -/
theorem compareBigInt_zero : compareBigInt positiveZero 0 = some .eq := by decide

end JSNumber

namespace JSString

/-- Trimming an empty UTF-16 sequence is empty. -/
theorem trim_empty : trim ⟨[]⟩ = ⟨[]⟩ := rfl

/-- Signed hexadecimal digit parsing is exact. -/
theorem parseSignedRadix_hex :
    parseSignedRadix? 16 (ofLeanString "-ff").codeUnits = some (-255) := by decide

/-- StringToBigInt accepts unsigned binary prefix grammar. -/
theorem parseBigInt_binary : parseBigInt? (ofLeanString "0b101") = some 5 := by decide

/-- StringToBigInt rejects fractional decimal grammar. -/
theorem parseBigInt_fraction : parseBigInt? (ofLeanString "1.0") = none := by decide

end JSString
end TSLean.JS
