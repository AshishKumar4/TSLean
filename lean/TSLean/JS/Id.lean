import Init.Data.Nat

namespace TSLean.JS

/-- A nominal identity for an ECMAScript object allocated in a heap. -/
structure RefId where
  value : Nat
  deriving DecidableEq, Hashable

instance : BEq RefId := ⟨fun left right => decide (left = right)⟩

/-- Reference hash-table equality is identity equality. -/
instance : LawfulBEq RefId where
  eq_of_beq := by intro left right equal; simpa [BEq.beq] using equal
  rfl := by intro id; simp [BEq.beq]

/-- A stable lexical-environment arena identity. -/
structure EnvId where
  value : Nat
  deriving DecidableEq, Hashable

instance : BEq EnvId := ⟨fun left right => decide (left = right)⟩

/-- Environment hash-table equality is identity equality. -/
instance : LawfulBEq EnvId where
  eq_of_beq := by intro left right equal; simpa [BEq.beq] using equal
  rfl := by intro id; simp [BEq.beq]

/-- A stable lexical-cell arena identity. -/
structure CellId where
  value : Nat
  deriving DecidableEq, Hashable

instance : BEq CellId := ⟨fun left right => decide (left = right)⟩

/-- Cell hash-table equality is identity equality. -/
instance : LawfulBEq CellId where
  eq_of_beq := by intro left right equal; simpa [BEq.beq] using equal
  rfl := by intro id; simp [BEq.beq]

/-- A stable function-table identity reserved for closure records. -/
structure FunctionId where
  value : Nat
  deriving DecidableEq, Hashable

instance : BEq FunctionId := ⟨fun left right => decide (left = right)⟩

/-- Function hash-table equality is identity equality. -/
instance : LawfulBEq FunctionId where
  eq_of_beq := by intro left right equal; simpa [BEq.beq] using equal
  rfl := by intro id; simp [BEq.beq]

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
