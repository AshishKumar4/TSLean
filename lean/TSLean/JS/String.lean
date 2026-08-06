import Init.Data.String
import Init.Data.UInt
import Init.Data.Bool

namespace TSLean.JS

/-- An ECMAScript string, represented exactly as UTF-16 code units. -/
structure JSString where
  codeUnits : List UInt16
  deriving DecidableEq, Hashable

namespace JSString

private def encodeScalar (c : Char) : List UInt16 :=
  let scalar := c.toNat
  if scalar ≤ 0xffff then
    [UInt16.ofNat scalar]
  else
    let offset := scalar - 0x10000
    [UInt16.ofNat (0xd800 + offset / 0x400),
      UInt16.ofNat (0xdc00 + offset % 0x400)]

/-- Encodes a Lean Unicode scalar string as ECMAScript UTF-16. -/
def ofLeanString (value : String) : JSString :=
  ⟨value.toList.flatMap encodeScalar⟩

private def decodeCodeUnits : List UInt16 → Option (List Char)
  | [] => some []
  | unit :: rest =>
      let first := unit.toNat
      if 0xd800 ≤ first && first ≤ 0xdbff then
        match rest with
        | [] => none
        | secondUnit :: tail =>
            let second := secondUnit.toNat
            if 0xdc00 ≤ second && second ≤ 0xdfff then
              let scalar := 0x10000 + (first - 0xd800) * 0x400 + (second - 0xdc00)
              Option.map (Char.ofNat scalar :: ·) (decodeCodeUnits tail)
            else
              none
      else if 0xdc00 ≤ first && first ≤ 0xdfff then
        none
      else
        Option.map (Char.ofNat first :: ·) (decodeCodeUnits rest)

/-- Decodes valid UTF-16, returning `none` rather than replacing an unpaired surrogate. -/
def toLeanString? (value : JSString) : Option String :=
  Option.map String.ofList (decodeCodeUnits value.codeUnits)

/-- Concatenates UTF-16 code units without decoding them. -/
def append (left right : JSString) : JSString :=
  ⟨left.codeUnits ++ right.codeUnits⟩

/-- Returns the ECMAScript length in UTF-16 code units. -/
def length (value : JSString) : Nat := value.codeUnits.length

/-- Reports whether the string has no UTF-16 code units. -/
def isEmpty (value : JSString) : Bool := value.codeUnits.isEmpty

/-- Compares the exact UTF-16 code-unit sequences. -/
def equal (left right : JSString) : Bool := decide (left.codeUnits = right.codeUnits)

/-- Reports whether a code unit is ECMAScript WhiteSpace or a LineTerminator. -/
def isStrWhiteSpace (unit : UInt16) : Bool :=
  match unit.toNat with
  | 0x0009 | 0x000a | 0x000b | 0x000c | 0x000d | 0x0020 | 0x00a0
  | 0x1680 | 0x2000 | 0x2001 | 0x2002 | 0x2003 | 0x2004 | 0x2005
  | 0x2006 | 0x2007 | 0x2008 | 0x2009 | 0x200a | 0x2028 | 0x2029
  | 0x202f | 0x205f | 0x3000 | 0xfeff => true
  | _ => false

/-- Removes ECMAScript WhiteSpace and LineTerminators from both code-unit ends. -/
def trim (value : JSString) : JSString :=
  let leading := value.codeUnits.dropWhile isStrWhiteSpace
  ⟨(leading.reverse.dropWhile isStrWhiteSpace).reverse⟩

/-- Decodes one ASCII digit for a radix in `2 .. 36`. -/
def asciiDigitValue? (radix : Nat) (unit : UInt16) : Option Nat :=
  if radix < 2 || 36 < radix then
    none
  else
    let code := unit.toNat
    let digit :=
      if 0x30 ≤ code && code ≤ 0x39 then some (code - 0x30)
      else if 0x41 ≤ code && code ≤ 0x5a then some (code - 0x41 + 10)
      else if 0x61 ≤ code && code ≤ 0x7a then some (code - 0x61 + 10)
      else none
    digit.bind fun value => if value < radix then some value else none

/-- Parses a nonempty sequence of ASCII digits in the given radix. -/
def parseUnsignedRadix? (radix : Nat) (units : List UInt16) : Option Nat := do
  if units.isEmpty then none else pure ()
  units.foldlM (fun value unit => do
    let digit ← asciiDigitValue? radix unit
    pure (value * radix + digit)) 0

/-- Parses an optional ASCII sign followed by nonempty digits in the given radix. -/
def parseSignedRadix? (radix : Nat) (units : List UInt16) : Option Int :=
  match units with
  | unit :: rest =>
      if unit.toNat = 0x2b then
        (parseUnsignedRadix? radix rest).map Int.ofNat
      else if unit.toNat = 0x2d then
        (parseUnsignedRadix? radix rest).map fun value => -Int.ofNat value
      else
        (parseUnsignedRadix? radix units).map Int.ofNat
  | [] => none

/-- Parses an optional ASCII sign followed by nonempty decimal digits. -/
def parseSignedDecimal? (units : List UInt16) : Option Int := parseSignedRadix? 10 units

private def prefixedRadix? (units : List UInt16) : Option (Nat × List UInt16) :=
  match units with
  | zero :: marker :: rest =>
      if zero.toNat != 0x30 then none
      else match marker.toNat with
        | 0x58 | 0x78 => some (16, rest)
        | 0x4f | 0x6f => some (8, rest)
        | 0x42 | 0x62 => some (2, rest)
        | _ => none
  | _ => none

/-- Parses signed decimal or unsigned `0x`, `0o`, and `0b` integer syntax. -/
def parseInteger? (units : List UInt16) : Option Int :=
  match prefixedRadix? units with
  | some (radix, digits) => (parseUnsignedRadix? radix digits).map Int.ofNat
  | none => parseSignedDecimal? units

/--
Parses ECMAScript StringToBigInt syntax after code-unit whitespace trimming. Finite
arbitrary-size inputs remain exact and can consume proportional resources; evaluator
fuel or a deployment resource profile will govern that cost without changing results.
-/
def parseBigInt? (value : JSString) : Option Int :=
  let units := value.trim.codeUnits
  if units.isEmpty then some 0 else parseInteger? units

/-- Compares UTF-16 code-unit sequences lexicographically. -/
def lessThan (left right : JSString) : Bool :=
  let rec loop : List UInt16 → List UInt16 → Bool
    | [], _ :: _ => true
    | _, [] => false
    | leftUnit :: leftRest, rightUnit :: rightRest =>
        if leftUnit.toNat < rightUnit.toNat then true
        else if rightUnit.toNat < leftUnit.toNat then false
        else loop leftRest rightRest
  loop left.codeUnits right.codeUnits

/-- Hash-table equality is exact UTF-16 representation equality. -/
instance : BEq JSString := ⟨equal⟩

/-- Exact UTF-16 equality is lawful. -/
instance : LawfulBEq JSString where
  eq_of_beq := by
    intro left right equal
    cases left
    cases right
    simp [BEq.beq, JSString.equal] at equal
    simp_all
  rfl := by intro value; cases value; simp [BEq.beq, JSString.equal]

/-- Exact UTF-16 code-unit equality is symmetric. -/
theorem equal_symm (left right : JSString) : equal left right = equal right left := by
  unfold equal
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact eq_comm

end JSString
end TSLean.JS
