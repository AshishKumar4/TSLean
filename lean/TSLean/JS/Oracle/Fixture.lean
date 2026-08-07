import TSLean.JS.Value
import TSLean.JS.Oracle.Protocol

namespace TSLean.JS.Oracle

structure MaterializedFixtures where
  values : Array Primitive
  symbols : Array String

private def parseDecimalInt? (value : String) : Option Int :=
  match value.toList with
  | '-' :: rest => (String.ofList rest).toNat?.map fun magnitude => -(Int.ofNat magnitude)
  | _ => value.toNat?.map Int.ofNat

private def parseUnits (value : Lean.Json) : Except String JSString := do
  let units ← (← value.getObjVal? "units").getArr?
  if units.size > 65536 then throw "string exceeds UTF-16 limit"
  let parsed ← units.mapM fun unit => do
    let number ← unit.getNat?
    if number < 65536 then return UInt16.ofNat number
    throw "string code unit exceeds UInt16"
  return ⟨parsed.toList⟩

private def symbolIndex (symbols : Array String) (identity : String) : Nat × Array String :=
  match symbols.findIdx? (· = identity) with
  | some index => (index, symbols)
  | none => (symbols.size, symbols.push identity)

private def parseFixture (value : Lean.Json) (symbols : Array String) : Except String (Primitive × Array String) := do
  let kind ← stringField value "kind"
  match kind with
  | "undefined" => exactObject value 1; return (.undefined, symbols)
  | "null" => exactObject value 1; return (.null, symbols)
  | "boolean" =>
      exactObject value 2
      return (.boolean (← (← value.getObjVal? "value").getBool?), symbols)
  | "number" =>
      exactObject value 2
      let bitsText ← stringField value "bits"
      let bits ← match bitsText.toNat? with
        | some bits => pure bits
        | none => throw "invalid binary64 bits"
      if bits.repr != bitsText then throw "binary64 bits must use canonical decimal"
      if bits < 18446744073709551616 then return (.number ⟨UInt64.ofNat bits⟩, symbols)
      throw "binary64 bits exceed UInt64"
  | "string" => exactObject value 2; return (.string (← parseUnits value), symbols)
  | "bigint" =>
      exactObject value 2
      let decimal ← stringField value "decimal"
      let integer ← match parseDecimalInt? decimal with
        | some integer => pure integer
        | none => throw "invalid BigInt decimal"
      if integer.repr != decimal then throw "BigInt must use canonical decimal"
      return (.bigint integer, symbols)
  | "symbol" =>
      exactObject value 2
      let identity ← stringField value "identity"
      if identity.isEmpty then throw "symbol identity must not be empty"
      let (index, symbols) := symbolIndex symbols identity
      return (.symbol (.allocated index), symbols)
  | _ => throw s!"unknown fixture kind: {kind}"

def materializeFixtures (fixtures : Array Lean.Json) : Except String MaterializedFixtures := do
  let (values, symbols) ← fixtures.foldlM (init := (#[], #[])) fun (values, symbols) fixture => do
    let (value, symbols) ← parseFixture fixture symbols
    return (values.push value, symbols)
  return { values, symbols }

end TSLean.JS.Oracle
