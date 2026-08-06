import TSLean.JS.Completion
import TSLean.JS.Conversion
import TSLean.JS.PropertyKey

namespace TSLean.JS

/-- Typed failures from primitive coercions that ECMAScript specifies to throw TypeError. -/
inductive CoercionFault where
  | bigintToNumber
  | symbolToNumber
  | symbolToString
  | mixedNumericTypes
  | bigintDivisionByZero
  deriving DecidableEq

/-- An ECMAScript numeric value after ToNumeric. -/
inductive Numeric where
  | number (value : JSNumber)
  | bigint (value : Int)
  deriving DecidableEq

namespace CoercionFault

private def message : CoercionFault → String
  | .bigintToNumber => "TypeError: cannot convert BigInt to Number"
  | .symbolToNumber => "TypeError: cannot convert Symbol to Number"
  | .symbolToString => "TypeError: cannot convert Symbol to String"
  | .mixedNumericTypes => "TypeError: cannot mix BigInt and Number"
  | .bigintDivisionByZero => "RangeError: BigInt division by zero"

/-- Maps a typed coercion failure to its JavaScript thrown completion payload. -/
def toAbrupt (fault : CoercionFault) : Abrupt :=
  .thrown (.primitive (.string (JSString.ofLeanString fault.message)))

end CoercionFault

namespace Primitive

/-- Primitive ToNumber, including typed TypeErrors for BigInt and Symbol. -/
def toNumber : Primitive → Except CoercionFault JSNumber
  | .undefined => .ok JSNumber.canonicalNaN
  | .null => .ok JSNumber.positiveZero
  | .boolean false => .ok JSNumber.positiveZero
  | .boolean true => .ok JSNumber.one
  | .number value => .ok value
  | .string value => .ok (JSNumber.parse value)
  | .bigint _ => .error .bigintToNumber
  | .symbol _ => .error .symbolToNumber

/-- Primitive ToNumeric preserves BigInt and otherwise applies ToNumber. -/
def toNumeric : Primitive → Except CoercionFault Numeric
  | .bigint value => .ok (.bigint value)
  | value => value.toNumber.map .number

/-- Primitive ToString, preserving exact UTF-16 strings and rejecting Symbol. -/
def toString : Primitive → Except CoercionFault JSString
  | .undefined => .ok (JSString.ofLeanString "undefined")
  | .null => .ok (JSString.ofLeanString "null")
  | .boolean false => .ok (JSString.ofLeanString "false")
  | .boolean true => .ok (JSString.ofLeanString "true")
  | .number value => .ok value.format
  | .string value => .ok value
  | .bigint value => .ok (JSString.ofLeanString value.repr)
  | .symbol _ => .error .symbolToString

/-- Primitive ToPropertyKey preserves symbols and stringifies every other primitive. -/
def toPropertyKey : Primitive → Except CoercionFault PropertyKey
  | .symbol id => .ok (.symbol id)
  | value => value.toString.map .string

end Primitive
end TSLean.JS
