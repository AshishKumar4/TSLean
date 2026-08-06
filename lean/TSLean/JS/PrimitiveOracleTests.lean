import TSLean.JS

namespace TSLean.JS.PrimitiveOracleTests

private def parseNat? (value : String) : Option Nat := value.toNat?

private def parseInt? (value : String) : Option Int :=
  match value.toList with
  | '-' :: rest => (String.ofList rest).toNat?.map fun magnitude => -(Int.ofNat magnitude)
  | '+' :: rest => (String.ofList rest).toNat?.map Int.ofNat
  | _ => value.toNat?.map Int.ofNat

private def decodeString? (encoded : String) : Option JSString := do
  if encoded = "_" then return ⟨[]⟩
  let units ← encoded.splitOn "," |>.mapM fun value => value.toNat?.map UInt16.ofNat
  return ⟨units⟩

private def encodeString (value : JSString) : String :=
  if value.codeUnits.isEmpty then "_"
  else String.intercalate "," (value.codeUnits.map fun unit => unit.toNat.repr)

private def parsePrimitive? (encoded : String) : Option Primitive :=
  match encoded.splitOn ":" with
  | ["u"] => some .undefined
  | ["n"] => some .null
  | ["f"] => some (.boolean false)
  | ["t"] => some (.boolean true)
  | ["d", bits] => bits.toNat?.map fun value => .number ⟨UInt64.ofNat value⟩
  | ["s", units] => (decodeString? units).map .string
  | ["i", value] => (parseInt? value).map .bigint
  | ["y", id] => id.toNat?.map fun value => .symbol (.allocated value)
  | _ => none

private def encodeNumber (value : JSNumber) : String := "number:" ++ value.bits.toNat.repr

private def encodeFault : CoercionFault → String
  | .bigintDivisionByZero => "error:RangeError"
  | .bigintToNumber | .symbolToNumber | .symbolToString | .mixedNumericTypes => "error:TypeError"

private def encodePrimitive : Primitive → String
  | .undefined => "undefined"
  | .null => "null"
  | .boolean value => "boolean:" ++ toString value
  | .number value => encodeNumber value
  | .string value => "string:" ++ encodeString value
  | .bigint value => "bigint:" ++ value.repr
  | .symbol (.allocated id) => "symbol:" ++ id.repr
  | .symbol (.wellKnown _) => "symbol:wellKnown"

private def encodeValue : Value → String
  | .primitive value => encodePrimitive value
  | .object ref => "object:" ++ ref.value.repr

private def encodeExcept (encode : α → String) : Except CoercionFault α → String
  | .ok value => encode value
  | .error fault => encodeFault fault

private def evaluate (query : String) : String :=
  match query.splitOn "/" with
  | ["parse", encoded] =>
      match decodeString? encoded with
      | some value => encodeNumber (JSNumber.parse value)
      | none => "invalid"
  | ["format", bits] =>
      match bits.toNat? with
      | some value => "string:" ++ encodeString (JSNumber.format ⟨UInt64.ofNat value⟩)
      | none => "invalid"
  | ["number", encoded] =>
      match parsePrimitive? encoded with
      | some value => encodeExcept encodeNumber value.toNumber
      | none => "invalid"
  | ["string", encoded] =>
      match parsePrimitive? encoded with
      | some value => encodeExcept (fun text => "string:" ++ encodeString text) value.toString
      | none => "invalid"
  | ["key", encoded] =>
      match parsePrimitive? encoded with
      | some value => encodeExcept (fun
          | .string text => "string:" ++ encodeString text
          | .symbol (.allocated id) => "symbol:" ++ id.repr
          | .symbol (.wellKnown _) => "symbol:wellKnown") value.toPropertyKey
      | none => "invalid"
  | ["loose", left, right] =>
      match parsePrimitive? left, parsePrimitive? right with
      | some left, some right => "boolean:" ++ toString (left.looseEqual right)
      | _, _ => "invalid"
  | [operation, left, right] =>
      match parsePrimitive? left, parsePrimitive? right with
      | some left, some right =>
          match operation with
          | "add" => encodeExcept encodeValue (left.add right)
          | "sub" => encodeExcept encodeValue (left.subtract right)
          | "mul" => encodeExcept encodeValue (left.multiply right)
          | "div" => encodeExcept encodeValue (left.divide right)
          | "rem" => encodeExcept encodeValue (left.remainder right)
          | "lt" => encodeExcept (fun value => "boolean:" ++ toString value) (left.lessThan right)
          | "le" => encodeExcept (fun value => "boolean:" ++ toString value) (left.lessThanOrEqual right)
          | "gt" => encodeExcept (fun value => "boolean:" ++ toString value) (left.greaterThan right)
          | "ge" => encodeExcept (fun value => "boolean:" ++ toString value) (left.greaterThanOrEqual right)
          | _ => "invalid"
      | _, _ => "invalid"
  | _ => "invalid"

def run (arguments : List String) : IO UInt32 := do
  for query in arguments do IO.println (evaluate query)
  return 0

end TSLean.JS.PrimitiveOracleTests

def main (arguments : List String) : IO UInt32 :=
  TSLean.JS.PrimitiveOracleTests.run arguments
