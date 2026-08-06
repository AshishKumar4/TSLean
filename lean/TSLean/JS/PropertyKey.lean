import TSLean.JS.Id
import TSLean.JS.String

namespace TSLean.JS

/-- An ECMAScript property key is a UTF-16 string or a symbol identity. -/
inductive PropertyKey where
  | string (value : JSString)
  | symbol (id : SymbolId)
  deriving DecidableEq, Hashable

namespace PropertyKey

/-- The largest integer whose decimal spelling is an ECMAScript array index. -/
def maxArrayIndex : Nat := 4294967294

private def decimalDigit? (unit : UInt16) : Option Nat :=
  let value := unit.toNat
  if 0x30 ≤ value && value ≤ 0x39 then some (value - 0x30) else none

private def parseDecimal (acc : Nat) : List UInt16 → Option Nat
  | [] => some acc
  | unit :: rest => do
      let digit ← decimalDigit? unit
      let next := acc * 10 + digit
      if next ≤ maxArrayIndex then parseDecimal next rest else none

/-- Recognizes canonical ECMAScript array-index strings in `0 .. 2^32 - 2`. -/
def arrayIndex? (value : JSString) : Option Nat :=
  match value.codeUnits with
  | [] => none
  | first :: rest =>
      if first.toNat = 0x30 then
        if rest.isEmpty then some 0 else none
      else do
        let digit ← decimalDigit? first
        if digit = 0 then none else parseDecimal digit rest

/-- Returns the exact ASCII decimal property key for an array index. -/
def arrayIndexString (index : Nat) : JSString :=
  JSString.ofLeanString index.repr

/-- Compares property keys by code-unit equality or symbol identity. -/
def equal : PropertyKey → PropertyKey → Bool
  | .string left, .string right => JSString.equal left right
  | .symbol left, .symbol right => decide (left = right)
  | .string _, .symbol _ => false
  | .symbol _, .string _ => false

/-- Property-key hash-table equality uses UTF-16 equality or symbol identity. -/
instance : BEq PropertyKey := ⟨equal⟩

/-- Property-key equality is lawful. -/
instance : LawfulBEq PropertyKey where
  eq_of_beq := by
    intro left right equal
    cases left <;> cases right
    · rename_i left right
      cases left
      cases right
      simp [BEq.beq, PropertyKey.equal, JSString.equal] at equal
      simp_all
    · simp [BEq.beq, PropertyKey.equal] at equal
    · simp [BEq.beq, PropertyKey.equal] at equal
    · simp [BEq.beq, PropertyKey.equal] at equal
      simp_all
  rfl := by
    intro key
    cases key <;> simp [BEq.beq, PropertyKey.equal, JSString.equal]

end PropertyKey
end TSLean.JS
