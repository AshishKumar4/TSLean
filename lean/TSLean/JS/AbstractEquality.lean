import TSLean.JS.AbstractOperations
import TSLean.JS.Equality
import TSLean.JS.PrimitiveOperators

namespace TSLean.JS

namespace AbstractEquality

private def coercion (result : Except CoercionFault α) : JSM P α :=
  match result with
  | .ok value => pure value
  | .error fault => JSM.throwJS fault.toThrownValue

private def nullish : Primitive → Bool
  | .undefined | .null => true
  | _ => false

private def primitiveAgainstObject (hook : BodyHook P) (primitive : Primitive)
    (object : RefId) : JSM P Bool :=
  if nullish primitive then pure false
  else do
    let converted ← AbstractOperations.toPrimitive hook (.object object)
    pure (primitive.looseEqual converted)

/-- Full ECMAScript abstract equality with at most one object-to-primitive conversion. -/
def looseEqual (hook : BodyHook P) (left right : Value) : JSM P Bool :=
  match left, right with
  | .primitive left, .primitive right => pure (left.looseEqual right)
  | .object left, .object right => pure (decide (left = right))
  | .primitive primitive, .object object => primitiveAgainstObject hook primitive object
  | .object object, .primitive primitive => primitiveAgainstObject hook primitive object

/-- Value-level addition performs ordered ToPrimitive conversion, then concatenation or ToNumeric. -/
def add (hook : BodyHook P) (left right : Value) : JSM P Value := do
  let leftPrimitive ← AbstractOperations.toPrimitive hook left
  let rightPrimitive ← AbstractOperations.toPrimitive hook right
  match leftPrimitive, rightPrimitive with
  | .string _, _ | _, .string _ =>
      let leftString ← coercion leftPrimitive.toString
      let rightString ← coercion rightPrimitive.toString
      pure (.primitive (.string (leftString.append rightString)))
  | _, _ =>
      let leftNumeric ← coercion leftPrimitive.toNumeric
      let rightNumeric ← coercion rightPrimitive.toNumeric
      pure (← coercion (Numeric.add leftNumeric rightNumeric)).toValue

private def orderedPrimitives (hook : BodyHook P) (left right : Value) (leftFirst : Bool) :
    JSM P (Primitive × Primitive) := do
  if leftFirst then
    let leftPrimitive ← AbstractOperations.toPrimitive hook left .number
    let rightPrimitive ← AbstractOperations.toPrimitive hook right .number
    pure (leftPrimitive, rightPrimitive)
  else
    let rightPrimitive ← AbstractOperations.toPrimitive hook right .number
    let leftPrimitive ← AbstractOperations.toPrimitive hook left .number
    pure (leftPrimitive, rightPrimitive)

/-- ECMAScript Abstract Relational Comparison over values with explicit coercion order. -/
def relationalComparison (hook : BodyHook P) (left right : Value)
    (leftFirst : Bool := true) : JSM P (Option Bool) := do
  let (leftPrimitive, rightPrimitive) ← orderedPrimitives hook left right leftFirst
  coercion (Primitive.abstractRelationalComparison leftPrimitive rightPrimitive leftFirst)

/-- Value-level `<`; unordered comparisons are false. -/
def lessThan (hook : BodyHook P) (left right : Value) : JSM P Bool := do
  let result ← relationalComparison hook left right
  pure (result.getD false)

/-- Value-level `>` with specification-prescribed conversion order. -/
def greaterThan (hook : BodyHook P) (left right : Value) : JSM P Bool := do
  let result ← relationalComparison hook right left false
  pure (result.getD false)

/-- Value-level `<=`; unordered comparisons are false. -/
def lessThanOrEqual (hook : BodyHook P) (left right : Value) : JSM P Bool := do
  match ← relationalComparison hook right left false with
  | none | some true => pure false
  | some false => pure true

/-- Value-level `>=`; unordered comparisons are false. -/
def greaterThanOrEqual (hook : BodyHook P) (left right : Value) : JSM P Bool := do
  match ← relationalComparison hook left right with
  | none | some true => pure false
  | some false => pure true

end AbstractEquality
end TSLean.JS
