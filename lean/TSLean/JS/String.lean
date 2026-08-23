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
  Option.map String.mk (decodeCodeUnits value.codeUnits)

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

private theorem decodeCodeUnits_encodeScalar (character : Char) (units : List UInt16)
    (decoded : decodeCodeUnits units = some characters) :
    decodeCodeUnits (encodeScalar character ++ units) = some (character :: characters) := by
  have valid : character.toNat.isValidChar := by
    simpa [Char.toNat, UInt32.isValidChar] using character.valid
  by_cases bmp : character.toNat ≤ 0xffff
  · have scalarLt : character.toNat < 0x10000 := by omega
    have notHigh : ¬(0xd800 ≤ character.toNat ∧ character.toNat ≤ 0xdbff) := by
      rcases valid with valid | valid <;> omega
    have notLow : ¬(0xdc00 ≤ character.toNat ∧ character.toNat ≤ 0xdfff) := by
      rcases valid with valid | valid <;> omega
    have scalarToNat : (UInt16.ofNat character.toNat).toNat = character.toNat := by
      simp [UInt16.ofNat, UInt16.toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt scalarLt]
    simp only [encodeScalar, bmp, if_pos, List.singleton_append]
    rw [decodeCodeUnits.eq_def]
    simp [scalarToNat, notHigh, notLow, decoded, Char.ofNat_toNat]
  · have scalarGt : 0xffff < character.toNat := by omega
    have scalarLt : character.toNat < 0x110000 := by
      rcases valid with valid | valid <;> omega
    let offset := character.toNat - 0x10000
    have offsetEq : character.toNat = 0x10000 + offset := by
      simp only [offset]
      omega
    have offsetLt : offset < 0x100000 := by
      simp only [offset]
      omega
    have offsetDivLt : offset / 0x400 < 0x400 := by
      apply Nat.div_lt_iff_lt_mul (by omega : 0 < (0x400 : Nat)) |>.2
      simpa using offsetLt
    have highLt : 0xd800 + offset / 0x400 < 0x10000 := by
      have := offsetDivLt
      omega
    have lowLt : 0xdc00 + offset % 0x400 < 0x10000 := by
      have := Nat.mod_lt offset (by omega : 0 < (0x400 : Nat))
      omega
    have highRange : 0xd800 ≤ 0xd800 + offset / 0x400 ∧
        0xd800 + offset / 0x400 ≤ 0xdbff := by
      have := offsetDivLt
      omega
    have lowRange : 0xdc00 ≤ 0xdc00 + offset % 0x400 ∧
        0xdc00 + offset % 0x400 ≤ 0xdfff := by
      have := Nat.mod_lt offset (by omega : 0 < (0x400 : Nat))
      omega
    have highToNat : (UInt16.ofNat (0xd800 + offset / 0x400)).toNat =
        0xd800 + offset / 0x400 := by
      simp [UInt16.ofNat, UInt16.toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt highLt]
    have lowToNat : (UInt16.ofNat (0xdc00 + offset % 0x400)).toNat =
        0xdc00 + offset % 0x400 := by
      simp [UInt16.ofNat, UInt16.toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt lowLt]
    have recombineSimple :
        0x10000 + offset / 0x400 * 0x400 + offset % 0x400 = character.toNat := by
      omega
    unfold encodeScalar
    rw [if_neg bmp]
    change decodeCodeUnits
      ([UInt16.ofNat (0xd800 + offset / 0x400),
        UInt16.ofNat (0xdc00 + offset % 0x400)] ++ units) =
        some (character :: characters)
    simp only [List.cons_append, List.nil_append]
    rw [decodeCodeUnits.eq_def]
    simp only [highToNat, lowToNat]
    simp [highRange, lowRange, decoded]
    simp only [Nat.add_sub_cancel_left]
    rw [recombineSimple, Char.ofNat_toNat]

private theorem decodeCodeUnits_encodeList (characters : List Char) :
    decodeCodeUnits (characters.flatMap encodeScalar) = some characters := by
  induction characters with
  | nil => rfl
  | cons character rest ih =>
      rw [List.flatMap_cons]
      exact decodeCodeUnits_encodeScalar character _ ih

/-- Encoding a Lean scalar string and decoding its UTF-16 representation returns the input. -/
theorem toLeanString?_ofLeanString (value : String) :
    (ofLeanString value).toLeanString? = some value := by
  simp [ofLeanString, toLeanString?, decodeCodeUnits_encodeList]

/-- UTF-16 encoding of Lean scalar strings is injective. -/
-- Stated as the unfolding of `Function.Injective`, which 4.16 core does not provide. The
-- strict-implicit binders are load-bearing: call sites apply this to the equality alone.
theorem ofLeanString_injective :
    ∀ ⦃left right : String⦄, ofLeanString left = ofLeanString right → left = right := by
  intro left right equal
  have decoded := congrArg toLeanString? equal
  simpa [toLeanString?_ofLeanString] using decoded

/-- UTF-16 encoding commutes with Lean string append. -/
theorem ofLeanString_append (left right : String) :
    ofLeanString (left ++ right) = (ofLeanString left).append (ofLeanString right) := by
  congr
  simp [ofLeanString, append, List.flatMap_append]

private theorem flatMap_encodeScalar_of_bmp (characters : List Char)
    (bmp : ∀ character, character ∈ characters → character.toNat ≤ 0xffff) :
    characters.flatMap encodeScalar = characters.map (UInt16.ofNat ∘ Char.toNat) := by
  induction characters with
  | nil => rfl
  | cons character rest ih =>
      rw [List.flatMap_cons, List.map_cons]
      simp only [encodeScalar, bmp character (List.mem_cons_self character rest), if_pos,
        List.singleton_append, Function.comp_apply]
      congr
      exact ih fun current member => bmp current (List.mem_cons_of_mem character member)

/-- BMP-only encoding emits exactly one code unit for each Lean character. -/
theorem ofLeanString_codeUnits_of_bmp (value : String)
    (bmp : ∀ character, character ∈ value.toList → character.toNat ≤ 0xffff) :
    (ofLeanString value).codeUnits = value.toList.map (UInt16.ofNat ∘ Char.toNat) := by
  exact flatMap_encodeScalar_of_bmp value.toList bmp

private theorem encodeScalar_of_bmpUnit (unit : UInt16)
    (notHigh : ¬(0xd800 ≤ unit.toNat ∧ unit.toNat ≤ 0xdbff))
    (notLow : ¬(0xdc00 ≤ unit.toNat ∧ unit.toNat ≤ 0xdfff)) :
    encodeScalar (Char.ofNat unit.toNat) = [unit] := by
  have scalarLt : unit.toNat < 0x10000 := UInt16.toNat_lt_size unit
  have valid : unit.toNat.isValidChar := by
    simp only [Nat.isValidChar]
    omega
  have charToNat : (Char.ofNat unit.toNat).toNat = unit.toNat := by
    unfold Char.ofNat
    rw [dif_pos valid]
    rfl
  have scalarLe : unit.toNat ≤ 0xffff := by omega
  simp [encodeScalar, charToNat, scalarLe, UInt16.ofNat_toNat]

private theorem encodeScalar_of_surrogates (high low : UInt16)
    (highRange : 0xd800 ≤ high.toNat ∧ high.toNat ≤ 0xdbff)
    (lowRange : 0xdc00 ≤ low.toNat ∧ low.toNat ≤ 0xdfff) :
    encodeScalar (Char.ofNat
      (0x10000 + (high.toNat - 0xd800) * 0x400 + (low.toNat - 0xdc00))) = [high, low] := by
  let scalar := 0x10000 + (high.toNat - 0xd800) * 0x400 + (low.toNat - 0xdc00)
  have scalarRange : 0x10000 ≤ scalar ∧ scalar < 0x110000 := by
    simp only [scalar]
    omega
  have valid : scalar.isValidChar := by
    simp only [Nat.isValidChar]
    omega
  have charToNat : (Char.ofNat scalar).toNat = scalar := by
    unfold Char.ofNat
    rw [dif_pos valid]
    rfl
  have offsetEq : scalar - 0x10000 =
      (high.toNat - 0xd800) * 0x400 + (low.toNat - 0xdc00) := by
    simp only [scalar]
    omega
  have highEq : 0xd800 + (scalar - 0x10000) / 0x400 = high.toNat := by
    rw [offsetEq]
    omega
  have lowEq : 0xdc00 + (scalar - 0x10000) % 0x400 = low.toNat := by
    rw [offsetEq]
    omega
  unfold encodeScalar
  rw [charToNat, if_neg (by omega)]
  change [UInt16.ofNat (0xd800 + (scalar - 0x10000) / 0x400),
    UInt16.ofNat (0xdc00 + (scalar - 0x10000) % 0x400)] = [high, low]
  rw [highEq, lowEq, UInt16.ofNat_toNat, UInt16.ofNat_toNat]

private theorem encodeList_decodeCodeUnits (units : List UInt16) (characters : List Char)
    (decoded : decodeCodeUnits units = some characters) :
    characters.flatMap encodeScalar = units := by
  cases units with
  | nil =>
      simp [decodeCodeUnits.eq_def] at decoded
      subst characters
      rfl
  | cons unit rest =>
      by_cases high : 0xd800 ≤ unit.toNat ∧ unit.toNat ≤ 0xdbff
      · cases rest with
        | nil => simp [decodeCodeUnits.eq_def, high] at decoded
        | cons second tail =>
            by_cases low : 0xdc00 ≤ second.toNat ∧ second.toNat ≤ 0xdfff
            · rw [decodeCodeUnits.eq_def] at decoded
              simp only [high, decide_true, Bool.true_and, if_pos, low] at decoded
              obtain ⟨tailCharacters, tailDecoded, rfl⟩ :=
                Option.map_eq_some'.mp decoded
              rw [List.flatMap_cons, encodeScalar_of_surrogates unit second high low,
                List.cons_append, List.cons_append, List.nil_append]
              congr
              exact encodeList_decodeCodeUnits tail tailCharacters tailDecoded
            · simp [decodeCodeUnits.eq_def, high, low] at decoded
      · by_cases low : 0xdc00 ≤ unit.toNat ∧ unit.toNat ≤ 0xdfff
        · simp [decodeCodeUnits.eq_def, high, low] at decoded
        · rw [decodeCodeUnits.eq_def] at decoded
          simp [high, low] at decoded
          obtain ⟨restCharacters, restDecoded, rfl⟩ := decoded
          rw [List.flatMap_cons, encodeScalar_of_bmpUnit unit high low,
            List.singleton_append]
          congr
          exact encodeList_decodeCodeUnits rest restCharacters restDecoded
termination_by units.length

/-- Decoding valid UTF-16 and re-encoding the result preserves every code unit exactly. -/
theorem ofLeanString_toLeanString? {value : JSString} {native : String}
    (decoded : value.toLeanString? = some native) : ofLeanString native = value := by
  cases value with
  | mk units =>
      simp only [toLeanString?, Option.map_eq_some'] at decoded
      obtain ⟨characters, charactersDecoded, rfl⟩ := decoded
      congr
      simpa [ofLeanString] using encodeList_decodeCodeUnits units characters charactersDecoded

end JSString
end TSLean.JS
