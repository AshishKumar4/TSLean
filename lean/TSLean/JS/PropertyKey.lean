import TSLean.JS.Id
import TSLean.JS.String

namespace TSLean.JS

/-- An ECMAScript property key is a UTF-16 string or a symbol identity. -/
inductive PropertyKey where
  | string (value : JSString)
  | symbol (id : SymbolId)

namespace PropertyKey

/-- Compares property keys by code-unit equality or symbol identity. -/
def equal : PropertyKey → PropertyKey → Bool
  | .string left, .string right => JSString.equal left right
  | .symbol left, .symbol right => decide (left = right)
  | .string _, .symbol _ => false
  | .symbol _, .string _ => false

end PropertyKey
end TSLean.JS
