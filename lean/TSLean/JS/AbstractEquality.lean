import TSLean.JS.AbstractOperations
import TSLean.JS.Equality
import TSLean.JS.PrimitiveOperators

namespace TSLean.JS

namespace AbstractEquality

/-- Whether a primitive is null or undefined for abstract equality. -/
def nullish : Primitive → Bool
  | .undefined | .null => true
  | _ => false

/-- Compares a primitive with an object after the required object coercion. -/
def primitiveAgainstObjectWith [Monad m] (effects : CoercionEffects m) (primitive : Primitive)
    (object : RefId) : m Bool :=
  if nullish primitive then pure false
  else do
    let converted ← AbstractOperations.toPrimitiveWith effects (.object object)
    pure (primitive.looseEqual converted)

/-- Full ECMAScript abstract equality through generic coercion effects. -/
def looseEqualWith [Monad m] (effects : CoercionEffects m) (left right : Value) : m Bool :=
  match left, right with
  | .primitive left, .primitive right => pure (left.looseEqual right)
  | .object left, .object right => pure (decide (left = right))
  | .primitive primitive, .object object => primitiveAgainstObjectWith effects primitive object
  | .object object, .primitive primitive => primitiveAgainstObjectWith effects primitive object

/-- Applies the concatenation-or-numeric part of addition to already-coerced operands. -/
def addPrimitivesWith [Monad m] (effects : CoercionEffects m)
    (leftPrimitive rightPrimitive : Primitive) : m Value :=
  match leftPrimitive, rightPrimitive with
  | .string _, _ | _, .string _ =>
      do
        let leftString ← CoercionEffects.fromCoercion effects leftPrimitive.toString
        let rightString ← CoercionEffects.fromCoercion effects rightPrimitive.toString
        pure (.primitive (.string (leftString.append rightString)))
  | _, _ =>
      do
        let leftNumeric ← CoercionEffects.fromCoercion effects leftPrimitive.toNumeric
        let rightNumeric ← CoercionEffects.fromCoercion effects rightPrimitive.toNumeric
        pure (← CoercionEffects.fromCoercion effects (Numeric.add leftNumeric rightNumeric)).toValue

/-- Value-level addition through generic coercion effects. -/
def addWith [Monad m] (effects : CoercionEffects m) (left right : Value) : m Value := do
  let leftPrimitive ← AbstractOperations.toPrimitiveWith effects left
  let rightPrimitive ← AbstractOperations.toPrimitiveWith effects right
  addPrimitivesWith effects leftPrimitive rightPrimitive

/-- Coerces relational operands in the order required by `leftFirst`. -/
def orderedPrimitivesWith [Monad m] (effects : CoercionEffects m) (left right : Value)
    (leftFirst : Bool) : m (Primitive × Primitive) := do
  if leftFirst then
    let leftPrimitive ← AbstractOperations.toPrimitiveWith effects left .number
    let rightPrimitive ← AbstractOperations.toPrimitiveWith effects right .number
    pure (leftPrimitive, rightPrimitive)
  else
    let rightPrimitive ← AbstractOperations.toPrimitiveWith effects right .number
    let leftPrimitive ← AbstractOperations.toPrimitiveWith effects left .number
    pure (leftPrimitive, rightPrimitive)

/-- ECMAScript Abstract Relational Comparison through generic coercion effects. -/
def relationalComparisonWith [Monad m] (effects : CoercionEffects m) (left right : Value)
    (leftFirst : Bool := true) : m (Option Bool) := do
  let (leftPrimitive, rightPrimitive) ← orderedPrimitivesWith effects left right leftFirst
  CoercionEffects.fromCoercion effects
    (Primitive.abstractRelationalComparison leftPrimitive rightPrimitive leftFirst)

/-- Full ECMAScript abstract equality with at most one object-to-primitive conversion. -/
@[inline]
def looseEqual (hook : BodyHook P) (left right : Value) : JSM P Bool :=
  looseEqualWith (CoercionEffects.forJSM hook) left right

/-- Value-level addition performs ordered ToPrimitive conversion, then concatenation or ToNumeric. -/
@[inline]
def add (hook : BodyHook P) (left right : Value) : JSM P Value :=
  addWith (CoercionEffects.forJSM hook) left right

/-- ECMAScript Abstract Relational Comparison over values with explicit coercion order. -/
@[inline]
def relationalComparison (hook : BodyHook P) (left right : Value)
    (leftFirst : Bool := true) : JSM P (Option Bool) :=
  relationalComparisonWith (CoercionEffects.forJSM hook) left right leftFirst

/-- Value-level `<` through generic coercion effects. -/
def lessThanWith [Monad m] (effects : CoercionEffects m) (left right : Value) : m Bool := do
  let result ← relationalComparisonWith effects left right
  pure (result.getD false)

/-- Value-level `<`; unordered comparisons are false. -/
def lessThan (hook : BodyHook P) (left right : Value) : JSM P Bool :=
  lessThanWith (CoercionEffects.forJSM hook) left right

/-- Value-level `>` through generic coercion effects. -/
def greaterThanWith [Monad m] (effects : CoercionEffects m) (left right : Value) : m Bool := do
  let result ← relationalComparisonWith effects right left false
  pure (result.getD false)

/-- Value-level `>` with specification-prescribed conversion order. -/
def greaterThan (hook : BodyHook P) (left right : Value) : JSM P Bool :=
  greaterThanWith (CoercionEffects.forJSM hook) left right

/-- Value-level `<=` through generic coercion effects. -/
def lessThanOrEqualWith [Monad m] (effects : CoercionEffects m) (left right : Value) : m Bool := do
  match ← relationalComparisonWith effects right left false with
  | none | some true => pure false
  | some false => pure true

/-- Value-level `<=`; unordered comparisons are false. -/
def lessThanOrEqual (hook : BodyHook P) (left right : Value) : JSM P Bool :=
  lessThanOrEqualWith (CoercionEffects.forJSM hook) left right

/-- Value-level `>=` through generic coercion effects. -/
def greaterThanOrEqualWith [Monad m] (effects : CoercionEffects m)
    (left right : Value) : m Bool := do
  match ← relationalComparisonWith effects left right with
  | none | some true => pure false
  | some false => pure true

/-- Value-level `>=`; unordered comparisons are false. -/
def greaterThanOrEqual (hook : BodyHook P) (left right : Value) : JSM P Bool :=
  greaterThanOrEqualWith (CoercionEffects.forJSM hook) left right

end AbstractEquality
end TSLean.JS
