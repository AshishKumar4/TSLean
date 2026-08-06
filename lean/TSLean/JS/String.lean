import Init.Data.String
import Init.Data.UInt

namespace TSLean.JS

/-- An ECMAScript string, represented exactly as UTF-16 code units. -/
structure JSString where
  codeUnits : List UInt16

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

end JSString
end TSLean.JS
