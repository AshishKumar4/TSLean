import TSLean.JS.PrimitiveConversion

namespace TSLean.JS

private def primitiveEqual
    (numberEqual : JSNumber → JSNumber → Bool) : Primitive → Primitive → Bool
  | .undefined, .undefined => true
  | .null, .null => true
  | .boolean left, .boolean right => left == right
  | .number left, .number right => numberEqual left right
  | .string left, .string right => JSString.equal left right
  | .bigint left, .bigint right => left == right
  | .symbol left, .symbol right => decide (left = right)
  | .undefined, .null | .undefined, .boolean _ | .undefined, .number _
  | .undefined, .string _ | .undefined, .bigint _ | .undefined, .symbol _
  | .null, .undefined | .null, .boolean _ | .null, .number _
  | .null, .string _ | .null, .bigint _ | .null, .symbol _
  | .boolean _, .undefined | .boolean _, .null | .boolean _, .number _
  | .boolean _, .string _ | .boolean _, .bigint _ | .boolean _, .symbol _
  | .number _, .undefined | .number _, .null | .number _, .boolean _
  | .number _, .string _ | .number _, .bigint _ | .number _, .symbol _
  | .string _, .undefined | .string _, .null | .string _, .boolean _
  | .string _, .number _ | .string _, .bigint _ | .string _, .symbol _
  | .bigint _, .undefined | .bigint _, .null | .bigint _, .boolean _
  | .bigint _, .number _ | .bigint _, .string _ | .bigint _, .symbol _
  | .symbol _, .undefined | .symbol _, .null | .symbol _, .boolean _
  | .symbol _, .number _ | .symbol _, .string _ | .symbol _, .bigint _ => false

private def valueEqual
    (numberEqual : JSNumber → JSNumber → Bool) : Value → Value → Bool
  | .primitive left, .primitive right => primitiveEqual numberEqual left right
  | .object left, .object right => decide (left = right)
  | .primitive _, .object _ => false
  | .object _, .primitive _ => false

/-- ECMAScript strict equality over values. -/
def strictEqual : Value → Value → Bool := valueEqual JSNumber.strictEqual

/-- ECMAScript SameValue over values. -/
def sameValue : Value → Value → Bool := valueEqual JSNumber.sameValue

/-- ECMAScript SameValueZero over values. -/
def sameValueZero : Value → Value → Bool := valueEqual JSNumber.sameValueZero

namespace Primitive

/-- ECMAScript loose equality for the complete primitive-only matrix. -/
def looseEqual : Primitive → Primitive → Bool
  | .undefined, .undefined | .null, .null | .undefined, .null | .null, .undefined => true
  | .boolean left, .boolean right => left == right
  | .number left, .number right => left.strictEqual right
  | .string left, .string right => left.equal right
  | .bigint left, .bigint right => left == right
  | .symbol left, .symbol right => decide (left = right)
  | .boolean value, .number numeric | .number numeric, .boolean value =>
      numeric.strictEqual (if value then JSNumber.one else JSNumber.positiveZero)
  | .boolean value, .string text | .string text, .boolean value =>
      (JSNumber.parse text).strictEqual (if value then JSNumber.one else JSNumber.positiveZero)
  | .boolean value, .bigint integer | .bigint integer, .boolean value =>
      integer = if value then 1 else 0
  | .number numeric, .string text | .string text, .number numeric =>
      numeric.strictEqual (JSNumber.parse text)
  | .bigint integer, .string text | .string text, .bigint integer =>
      text.parseBigInt? == some integer
  | .number numeric, .bigint integer | .bigint integer, .number numeric =>
      numeric.equalsBigInt integer
  | .undefined, .boolean _ | .undefined, .number _ | .undefined, .string _
  | .undefined, .bigint _ | .undefined, .symbol _
  | .null, .boolean _ | .null, .number _ | .null, .string _ | .null, .bigint _
  | .null, .symbol _
  | .boolean _, .undefined | .boolean _, .null | .boolean _, .symbol _
  | .number _, .undefined | .number _, .null | .number _, .symbol _
  | .string _, .undefined | .string _, .null | .string _, .symbol _
  | .bigint _, .undefined | .bigint _, .null | .bigint _, .symbol _
  | .symbol _, .undefined | .symbol _, .null | .symbol _, .boolean _
  | .symbol _, .number _ | .symbol _, .string _ | .symbol _, .bigint _ => false

end Primitive

end TSLean.JS
