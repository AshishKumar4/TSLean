import TSLean.JS.AbstractEquality
import TSLean.JS.PrimitiveOperators
import TSLean.JS.Oracle.Canonical
import TSLean.JS.Oracle.Registry

namespace TSLean.JS.Oracle

private def invalid (request : Request) (code message : String) : Except ProtocolError α :=
  .error { id := some request.id, code, message }

private def unary (request : Request) (values : Array Primitive) : Except ProtocolError Primitive :=
  match values with
  | #[value] => .ok value
  | _ => invalid request "invalid-arity" "operation requires one fixture"

private def binary (request : Request) (values : Array Primitive) : Except ProtocolError (Primitive × Primitive) :=
  match values with
  | #[left, right] => .ok (left, right)
  | _ => invalid request "invalid-arity" "operation requires two fixtures"

def evaluatePrimitive (request : Request) : Except ProtocolError Lean.Json := do
  let arity ← match operationArity? request.operation with
    | some arity => pure arity
    | none => .error {
        id := some request.id, code := "unknown-operation", message := s!"unknown operation: {request.operation}" }
  if request.fixtures.size != arity then
    return ← invalid request "invalid-arity" s!"operation requires {arity} fixture(s)"
  let materialized ← match materializeFixtures request.fixtures with
    | .ok value => .ok value
    | .error message => invalid request "invalid-fixture" message
  let symbols := materialized.symbols
  match request.operation with
  | "parse" =>
      match ← unary request materialized.values with
      | .string value => return normalObservation (primitiveDatum symbols (.number (JSNumber.parse value)))
      | _ => return ← invalid request "invalid-fixture" "parse requires a string fixture"
  | "format" =>
      match ← unary request materialized.values with
      | .number value => return normalObservation (primitiveDatum symbols (.string value.format))
      | _ => return ← invalid request "invalid-fixture" "format requires a number fixture"
  | "number" =>
      return exceptObservation (fun value => primitiveDatum symbols (.number value)) (← unary request materialized.values).toNumber
  | "string" =>
      return exceptObservation (fun value => primitiveDatum symbols (.string value)) (← unary request materialized.values).toString
  | "key" =>
      return exceptObservation (propertyKeyDatum symbols) (← unary request materialized.values).toPropertyKey
  | "loose" =>
      let (left, right) ← binary request materialized.values
      return normalObservation (primitiveDatum symbols (.boolean (left.looseEqual right)))
  | operation =>
      let (left, right) ← binary request materialized.values
      match operation with
      | "add" => return exceptObservation (valueDatum symbols) (left.add right)
      | "sub" => return exceptObservation (valueDatum symbols) (left.subtract right)
      | "mul" => return exceptObservation (valueDatum symbols) (left.multiply right)
      | "div" => return exceptObservation (valueDatum symbols) (left.divide right)
      | "rem" => return exceptObservation (valueDatum symbols) (left.remainder right)
      | "lt" => return exceptObservation (fun value => primitiveDatum symbols (.boolean value)) (left.lessThan right)
      | "le" => return exceptObservation (fun value => primitiveDatum symbols (.boolean value)) (left.lessThanOrEqual right)
      | "gt" => return exceptObservation (fun value => primitiveDatum symbols (.boolean value)) (left.greaterThan right)
      | "ge" => return exceptObservation (fun value => primitiveDatum symbols (.boolean value)) (left.greaterThanOrEqual right)
      | _ => return ← invalid request "unknown-operation" s!"unknown operation: {operation}"

end TSLean.JS.Oracle
