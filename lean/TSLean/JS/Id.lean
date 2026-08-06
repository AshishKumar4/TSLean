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
  deriving DecidableEq, Hashable

instance : BEq WellKnownSymbol := ⟨fun left right => decide (left = right)⟩

/-- Derived well-known-symbol equality is lawful. -/
instance : LawfulBEq WellKnownSymbol where
  eq_of_beq := by intro left right equal; simpa [BEq.beq] using equal
  rfl := by intro symbol; simp [BEq.beq]

/-- A symbol identity is either language-defined or allocated by the heap. -/
inductive SymbolId where
  | wellKnown (symbol : WellKnownSymbol)
  | allocated (id : Nat)
  deriving DecidableEq, Hashable

instance : BEq SymbolId := ⟨fun left right => decide (left = right)⟩

/-- Symbol hash-table equality is identity equality. -/
instance : LawfulBEq SymbolId where
  eq_of_beq := by intro left right equal; simpa [BEq.beq] using equal
  rfl := by intro symbol; simp [BEq.beq]

end TSLean.JS
