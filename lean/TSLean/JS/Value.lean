import TSLean.JS.Id
import TSLean.JS.Number
import TSLean.JS.String

namespace TSLean.JS

/-- The seven ECMAScript primitive value categories. -/
inductive Primitive where
  | undefined
  | null
  | boolean (value : Bool)
  | number (value : JSNumber)
  | string (value : JSString)
  | bigint (value : Int)
  | symbol (id : SymbolId)

/-- An ECMAScript value is either a primitive or an identity-bearing heap reference. -/
inductive Value where
  | primitive (value : Primitive)
  | object (ref : RefId)

end TSLean.JS
