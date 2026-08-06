import Init.Data.Nat

namespace TSLean.JS

/-- A nominal identity for an ECMAScript object allocated in a heap. -/
structure RefId where
  value : Nat
  deriving DecidableEq

/-- The fixed identities from ECMAScript's well-known symbol registry. -/
inductive WellKnownSymbol where
  | asyncDispose
  | asyncIterator
  | dispose
  | hasInstance
  | isConcatSpreadable
  | iterator
  | match
  | matchAll
  | replace
  | search
  | species
  | split
  | toPrimitive
  | toStringTag
  | unscopables
  deriving DecidableEq

/-- A symbol identity is either language-defined or allocated by the heap. -/
inductive SymbolId where
  | wellKnown (symbol : WellKnownSymbol)
  | allocated (id : Nat)
  deriving DecidableEq

end TSLean.JS
