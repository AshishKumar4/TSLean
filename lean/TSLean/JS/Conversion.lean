import TSLean.JS.Value

namespace TSLean.JS

/-- The `typeof` results determined entirely by a primitive value. -/
inductive PrimitiveTypeof where
  | undefined
  | object
  | boolean
  | number
  | string
  | bigint
  | symbol

namespace Primitive

/-- ECMAScript ToBoolean for primitives. -/
def toBoolean : Primitive → Bool
  | .undefined | .null => false
  | .boolean value => value
  | .number value => !(value.isZero || value.isNaN)
  | .string value => !value.isEmpty
  | .bigint value => value != 0
  | .symbol _ => true

/--
The primitive-only portion of ECMAScript `typeof`; null has tag `object`.
Heap objects are deliberately outside this API because their result depends on
callability, which belongs to the later heap boundary.
-/
def typeof : Primitive → PrimitiveTypeof
  | .undefined => .undefined
  | .null => .object
  | .boolean _ => .boolean
  | .number _ => .number
  | .string _ => .string
  | .bigint _ => .bigint
  | .symbol _ => .symbol

end Primitive

namespace Value

/-- ECMAScript ToBoolean. Every heap object is truthy. -/
def toBoolean : Value → Bool
  | .primitive value => value.toBoolean
  | .object _ => true

end Value
end TSLean.JS
