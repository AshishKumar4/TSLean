import TSLean.JS.PrimitiveConversion

namespace TSLean.JS

namespace Numeric

/-- Embeds a numeric result as a JavaScript value. -/
def toValue : Numeric → Value
  | .number value => .primitive (.number value)
  | .bigint value => .primitive (.bigint value)

/-- Adds same-domain numeric operands and rejects Number/BigInt mixing. -/
def add : Numeric → Numeric → Except CoercionFault Numeric
  | .number left, .number right => .ok (.number (JSNumber.add left right))
  | .bigint left, .bigint right => .ok (.bigint (left + right))
  | _, _ => .error .mixedNumericTypes

/-- Subtracts same-domain numeric operands and rejects Number/BigInt mixing. -/
def subtract : Numeric → Numeric → Except CoercionFault Numeric
  | .number left, .number right => .ok (.number (JSNumber.subtract left right))
  | .bigint left, .bigint right => .ok (.bigint (left - right))
  | _, _ => .error .mixedNumericTypes

/-- Multiplies same-domain numeric operands and rejects Number/BigInt mixing. -/
def multiply : Numeric → Numeric → Except CoercionFault Numeric
  | .number left, .number right => .ok (.number (JSNumber.multiply left right))
  | .bigint left, .bigint right => .ok (.bigint (left * right))
  | _, _ => .error .mixedNumericTypes

/-- Divides same-domain operands; BigInt division truncates toward zero and rejects zero. -/
def divide : Numeric → Numeric → Except CoercionFault Numeric
  | .number left, .number right => .ok (.number (JSNumber.divide left right))
  | .bigint _, .bigint 0 => .error .bigintDivisionByZero
  | .bigint left, .bigint right => .ok (.bigint (left.tdiv right))
  | _, _ => .error .mixedNumericTypes

/-- Computes same-domain remainder; BigInt remainder uses truncating division and rejects zero. -/
def remainder : Numeric → Numeric → Except CoercionFault Numeric
  | .number left, .number right => .ok (.number (JSNumber.remainder left right))
  | .bigint _, .bigint 0 => .error .bigintDivisionByZero
  | .bigint left, .bigint right => .ok (.bigint (left.tmod right))
  | _, _ => .error .mixedNumericTypes

/-- Exact numeric ordering; `none` represents an unordered NaN comparison. -/
def lessThan? : Numeric → Numeric → Option Bool
  | .number left, .number right =>
      if left.isNaN || right.isNaN then none else some (left.lessThan right)
  | .bigint left, .bigint right => some (left < right)
  | .number left, .bigint right => left.compareBigInt right |>.map (· = .lt)
  | .bigint left, .number right => right.compareBigInt left |>.map (· = .gt)

end Numeric

namespace Primitive

/-- Primitive ToPrimitive is identity because this module deliberately excludes objects. -/
def toPrimitive (value : Primitive) : Primitive := value

private def toNumericPair (left right : Primitive) (leftFirst : Bool) :
    Except CoercionFault (Numeric × Numeric) := do
  if leftFirst then
    let leftNumeric ← left.toNumeric
    let rightNumeric ← right.toNumeric
    return (leftNumeric, rightNumeric)
  else
    let rightNumeric ← right.toNumeric
    let leftNumeric ← left.toNumeric
    return (leftNumeric, rightNumeric)

/-- Primitive addition follows ToPrimitive, string concatenation, then same-domain ToNumeric. -/
def add (left right : Primitive) : Except CoercionFault Value := do
  let left := left.toPrimitive
  let right := right.toPrimitive
  match left, right with
  | .string _, _ | _, .string _ =>
      return .primitive (.string ((← left.toString).append (← right.toString)))
  | _, _ => return (← Numeric.add (← left.toNumeric) (← right.toNumeric)).toValue

/-- Primitive numeric subtraction through ToNumeric. -/
def subtract (left right : Primitive) : Except CoercionFault Value := do
  return (← Numeric.subtract (← left.toNumeric) (← right.toNumeric)).toValue

/-- Primitive numeric multiplication through ToNumeric. -/
def multiply (left right : Primitive) : Except CoercionFault Value := do
  return (← Numeric.multiply (← left.toNumeric) (← right.toNumeric)).toValue

/-- Primitive numeric division through ToNumeric. -/
def divide (left right : Primitive) : Except CoercionFault Value := do
  return (← Numeric.divide (← left.toNumeric) (← right.toNumeric)).toValue

/-- Primitive numeric remainder through ToNumeric. -/
def remainder (left right : Primitive) : Except CoercionFault Value := do
  return (← Numeric.remainder (← left.toNumeric) (← right.toNumeric)).toValue

/--
ECMAScript Abstract Relational Comparison for primitives. `none` is the specification's
undefined result. `leftFirst` preserves the conversion-order interface for future objects.
-/
def abstractRelationalComparison
    (left right : Primitive) (leftFirst : Bool := true) : Except CoercionFault (Option Bool) :=
  let left := left.toPrimitive
  let right := right.toPrimitive
  match left, right with
  | .string left, .string right => .ok (some (left.lessThan right))
  | .string left, .bigint right => .ok (left.parseBigInt?.map (· < right))
  | .bigint left, .string right => .ok (right.parseBigInt?.map (left < ·))
  | left, right => do
      let (leftNumeric, rightNumeric) ← toNumericPair left right leftFirst
      return Numeric.lessThan? leftNumeric rightNumeric

/-- Primitive `<`; unordered comparisons produce false. -/
def lessThan (left right : Primitive) : Except CoercionFault Bool := do
  return (← abstractRelationalComparison left right).getD false

/-- Primitive `>`; unordered comparisons produce false. -/
def greaterThan (left right : Primitive) : Except CoercionFault Bool := do
  return (← abstractRelationalComparison right left false).getD false

/-- Primitive `<=`; unordered comparisons produce false. -/
def lessThanOrEqual (left right : Primitive) : Except CoercionFault Bool := do
  match ← abstractRelationalComparison right left false with
  | none | some true => return false
  | some false => return true

/-- Primitive `>=`; unordered comparisons produce false. -/
def greaterThanOrEqual (left right : Primitive) : Except CoercionFault Bool := do
  match ← abstractRelationalComparison left right with
  | none | some true => return false
  | some false => return true

end Primitive
end TSLean.JS
