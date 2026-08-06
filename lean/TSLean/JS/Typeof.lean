import TSLean.JS.Conversion
import TSLean.JS.Heap

namespace TSLean.JS

/-- Complete ECMAScript `typeof` result tags. -/
inductive TypeofTag where
  | undefined
  | object
  | boolean
  | number
  | string
  | bigint
  | symbol
  | function
  deriving DecidableEq

namespace TypeofTag

/-- Embeds the unchanged primitive-only classification. -/
def ofPrimitive : PrimitiveTypeof → TypeofTag
  | .undefined => .undefined
  | .object => .object
  | .boolean => .boolean
  | .number => .number
  | .string => .string
  | .bigint => .bigint
  | .symbol => .symbol

/-- Exact JavaScript spelling for a `typeof` tag. -/
def text : TypeofTag → String
  | .undefined => "undefined"
  | .object => "object"
  | .boolean => "boolean"
  | .number => "number"
  | .string => "string"
  | .bigint => "bigint"
  | .symbol => "symbol"
  | .function => "function"

end TypeofTag

namespace Value

/-- Full ECMAScript `typeof`; invalid object references are model faults rather than objects. -/
def typeof (heap : Heap) : Value → Except HeapFault TypeofTag
  | .primitive value => .ok (TypeofTag.ofPrimitive value.typeof)
  | .object ref => do
      if ← heap.isCallable ref then pure .function else pure .object

end Value
end TSLean.JS
