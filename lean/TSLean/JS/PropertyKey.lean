import TSLean.JS.Id
import TSLean.JS.String
import Std

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

/-- Returns the exact ASCII decimal property key for an array index. -/
def arrayIndexString (index : Nat) : JSString :=
  JSString.ofLeanString index.repr

private def arrayIndexCandidate? (value : JSString) : Option Nat :=
  match value.codeUnits with
  | [] => none
  | first :: rest =>
      if first.toNat = 0x30 then
        if rest.isEmpty then some 0 else none
      else do
        let digit ← decimalDigit? first
        if digit = 0 then none else parseDecimal digit rest

/-- Recognizes canonical ECMAScript array-index strings in `0 .. 2^32 - 2`. -/
def arrayIndex? (value : JSString) : Option Nat :=
  match arrayIndexCandidate? value with
  | none => none
  | some index => if value = arrayIndexString index then some index else none

private theorem parseDecimal_bound {acc index : Nat} {units : List UInt16}
    (accBound : acc ≤ maxArrayIndex) (parsed : parseDecimal acc units = some index) :
    index ≤ maxArrayIndex := by
  induction units generalizing acc with
  | nil => simp [parseDecimal] at parsed; subst index; omega
  | cons unit rest ih =>
      cases digitEq : decimalDigit? unit with
      | none => simp [parseDecimal, digitEq] at parsed
      | some digit =>
          by_cases nextBound : acc * 10 + digit ≤ maxArrayIndex
          · simp [parseDecimal, digitEq, nextBound] at parsed
            exact ih nextBound parsed
          · simp [parseDecimal, digitEq, nextBound] at parsed

private theorem arrayIndexCandidate?_bound {value : JSString} {index : Nat}
    (parsed : arrayIndexCandidate? value = some index) : index ≤ maxArrayIndex := by
  unfold arrayIndexCandidate? at parsed
  cases unitsEq : value.codeUnits with
  | nil => simp [unitsEq] at parsed
  | cons first rest =>
      by_cases zero : first.toNat = 0x30
      · by_cases empty : rest.isEmpty
        · simp [unitsEq, zero, empty] at parsed
          subst index
          decide
        · simp [unitsEq, zero, empty] at parsed
      · cases digitEq : decimalDigit? first with
        | none => simp [unitsEq, zero, digitEq] at parsed
        | some digit =>
            by_cases digitZero : digit = 0
            · simp [unitsEq, zero, digitEq, digitZero] at parsed
            · simp [unitsEq, zero, digitEq, digitZero] at parsed
              exact parseDecimal_bound (by
                rw [decimalDigit?] at digitEq
                split at digitEq <;> simp_all
                have := first.toNat_lt
                unfold maxArrayIndex
                omega) parsed

/-- Every recognized array index is within the ECMAScript array-index bound. -/
theorem arrayIndex?_bound {value : JSString} {index : Nat}
    (parsed : arrayIndex? value = some index) : index ≤ maxArrayIndex := by
  unfold arrayIndex? at parsed
  cases candidateEq : arrayIndexCandidate? value with
  | none => simp [candidateEq] at parsed
  | some candidate =>
      rw [candidateEq] at parsed
      by_cases canonical : value = arrayIndexString candidate
      · simp [canonical] at parsed
        cases parsed
        exact arrayIndexCandidate?_bound candidateEq
      · simp [canonical] at parsed

/-- Recognition retains the exact original canonical spelling. -/
theorem arrayIndex?_sound {value : JSString} {index : Nat}
    (parsed : arrayIndex? value = some index) : value = arrayIndexString index := by
  unfold arrayIndex? at parsed
  cases candidateEq : arrayIndexCandidate? value with
  | none => simp [candidateEq] at parsed
  | some candidate =>
      rw [candidateEq] at parsed
      by_cases canonical : value = arrayIndexString candidate
      · simp [canonical] at parsed
        cases parsed
        exact canonical
      · simp [canonical] at parsed

/-- Canonical array-index parsing is injective. -/
theorem arrayIndex?_injective {left right : JSString} {index : Nat}
    (leftParsed : arrayIndex? left = some index) (rightParsed : arrayIndex? right = some index) :
    left = right := by
  rw [arrayIndex?_sound leftParsed, arrayIndex?_sound rightParsed]

private theorem lt_ten_cases (value : Nat) (bound : value < 10) :
    value = 0 ∨ value = 1 ∨ value = 2 ∨ value = 3 ∨ value = 4 ∨ value = 5 ∨
      value = 6 ∨ value = 7 ∨ value = 8 ∨ value = 9 := by omega

private theorem decimalDigit?_ofNat (digit : Nat) (bound : digit < 10) :
    decimalDigit? (UInt16.ofNat (48 + digit)) = some digit := by
  rcases lt_ten_cases digit bound with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem encode_digitChar (digit : Nat) (bound : digit < 10) :
    (JSString.ofLeanString (String.singleton (Nat.digitChar digit))).codeUnits =
      [UInt16.ofNat (48 + digit)] := by
  rcases lt_ten_cases digit bound with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem parseDecimal_append_digit (acc value digit : Nat) (units : List UInt16)
    (parsed : parseDecimal acc units = some value) (digitBound : digit < 10)
    (nextBound : value * 10 + digit ≤ maxArrayIndex) :
    parseDecimal acc (units ++ [UInt16.ofNat (48 + digit)]) = some (value * 10 + digit) := by
  induction units generalizing acc with
  | nil =>
      simp only [parseDecimal] at parsed
      cases parsed
      change parseDecimal value [UInt16.ofNat (48 + digit)] = some (value * 10 + digit)
      simp only [parseDecimal]
      rw [decimalDigit?_ofNat digit digitBound]
      simp [nextBound]
  | cons unit rest ih =>
      unfold parseDecimal at parsed ⊢
      cases decoded : decimalDigit? unit with
      | none => simp [decoded] at parsed
      | some headDigit =>
          by_cases prefixBound : acc * 10 + headDigit ≤ maxArrayIndex
          · simp [decoded, prefixBound] at parsed ⊢
            have unitEq : (48 : UInt16) + UInt16.ofNat digit =
                UInt16.ofNat (48 + digit) := (UInt16.ofNat_add 48 digit).symm
            rw [unitEq]
            exact ih (acc * 10 + headDigit) parsed
          · simp [decoded, prefixBound] at parsed

private theorem arrayIndexCandidate?_arrayIndexString {index : Nat}
    (bound : index ≤ maxArrayIndex) :
    arrayIndexCandidate? (arrayIndexString index) = some index := by
  induction index using Nat.strongRecOn with
  | ind index ih =>
      by_cases small : index < 10
      · rcases lt_ten_cases index small with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      · have tenLe : 10 ≤ index := by omega
        let leading := index / 10
        let digit := index % 10
        have leadingLt : leading < index := by omega
        have leadingPositive : 0 < leading := by omega
        have leadingBound : leading ≤ maxArrayIndex := by omega
        have leadingParsed := ih leading leadingLt leadingBound
        have digitBound : digit < 10 := by omega
        have nextBound : leading * 10 + digit ≤ maxArrayIndex := by
          dsimp [leading, digit]
          omega
        have digitCodeUnits := encode_digitChar digit digitBound
        unfold JSString.ofLeanString at digitCodeUnits
        simp only [String.toList_singleton, List.flatMap_cons, List.flatMap_nil,
          List.append_nil] at digitCodeUnits
        have codeUnitsEq : (arrayIndexString index).codeUnits =
            (arrayIndexString leading).codeUnits ++ [UInt16.ofNat (48 + digit)] := by
          unfold arrayIndexString JSString.ofLeanString
          rw [Nat.repr_of_ge tenLe]
          simp only [String.toList_append, List.flatMap_append, String.toList_singleton]
          simpa [leading, digit] using digitCodeUnits
        cases leadingUnits : (arrayIndexString leading).codeUnits with
        | nil => simp [arrayIndexCandidate?, leadingUnits] at leadingParsed
        | cons first rest =>
            unfold arrayIndexCandidate? at leadingParsed ⊢
            rw [leadingUnits] at leadingParsed
            rw [codeUnitsEq, leadingUnits]
            simp only [List.cons_append]
            by_cases leadingZero : first.toNat = 48
            · simp [leadingZero] at leadingParsed
              cases rest <;> simp_all
            · cases firstDigit : decimalDigit? first with
              | none => simp [leadingZero, firstDigit] at leadingParsed
              | some firstValue =>
                  by_cases firstZero : firstValue = 0
                  · simp [leadingZero, firstDigit, firstZero] at leadingParsed
                  · simp [leadingZero, firstDigit, firstZero] at leadingParsed ⊢
                    have result := parseDecimal_append_digit firstValue leading digit rest
                      leadingParsed digitBound nextBound
                    have indexEq : leading * 10 + digit = index := by
                      dsimp [leading, digit]
                      omega
                    simpa [indexEq] using result

/-- Every in-range canonical decimal index spelling is recognized at its original value. -/
theorem arrayIndex?_arrayIndexString {index : Nat} (bound : index ≤ maxArrayIndex) :
    arrayIndex? (arrayIndexString index) = some index := by
  unfold arrayIndex?
  rw [arrayIndexCandidate?_arrayIndexString bound]
  simp

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
