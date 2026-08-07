import TSLean.JS.ObjectAccess
import TSLean.JS.PrimitiveConversion

namespace TSLean.JS

/-- The preferred primitive result requested by `ToPrimitive`. -/
inductive PreferredType where
  | default
  | string
  | number
  deriving DecidableEq

namespace AbstractOperations

private def heapFault (fault : HeapFault) : ModelFault := .runtime (.heap fault)

private def property (name : String) : PropertyKey :=
  .string (JSString.ofLeanString name)

private def coercion (result : Except CoercionFault α) : JSM P α :=
  match result with
  | .ok value => pure value
  | .error fault => JSM.throwJS fault.toThrownValue

/-- Gets a method property. Nullish properties are absent; all other non-callable values throw. -/
def getMethod (hook : BodyHook P) (ref : RefId) (key : PropertyKey) : JSM P (Option RefId) := do
  let value ← ObjectAccess.get hook ref key (.object ref)
  match value with
  | .primitive .undefined | .primitive .null => pure none
  | .primitive _ => ObjectAccess.throwTypeError "property is not callable"
  | .object method =>
      let heap ← JSM.readHeap
      match heap.isCallable method with
      | .error fault => JSM.fail (heapFault fault)
      | .ok true => pure (some method)
      | .ok false => ObjectAccess.throwTypeError "property is not callable"

private def tryOrdinaryMethod (hook : BodyHook P) (receiver : RefId)
    (name : String) : JSM P (Option Primitive) := do
  let methodValue ← ObjectAccess.get hook receiver (property name) (.object receiver)
  match methodValue with
  | .primitive _ => pure none
  | .object method =>
      let heap ← JSM.readHeap
      match heap.isCallable method with
      | .error fault => JSM.fail (heapFault fault)
      | .ok false => pure none
      | .ok true =>
          match ← Call.call hook method (.object receiver) #[] with
          | .primitive primitive => pure (some primitive)
          | .object _ => pure none

private def tryOrdinaryMethods (hook : BodyHook P) (receiver : RefId) : List String → JSM P Primitive
  | [] => ObjectAccess.throwTypeError "cannot convert object to primitive value"
  | name :: rest => do
      match ← tryOrdinaryMethod hook receiver name with
      | some primitive => pure primitive
      | none => tryOrdinaryMethods hook receiver rest

/-- OrdinaryToPrimitive performs at most two ordered property reads and calls. -/
def ordinaryToPrimitive (hook : BodyHook P) (receiver : RefId)
    (hint : PreferredType) : JSM P Primitive :=
  match hint with
  | .string => tryOrdinaryMethods hook receiver ["toString", "valueOf"]
  | .number | .default => tryOrdinaryMethods hook receiver ["valueOf", "toString"]

private def hintString : PreferredType → JSString
  | .default => JSString.ofLeanString "default"
  | .string => JSString.ofLeanString "string"
  | .number => JSString.ofLeanString "number"

/-- ECMAScript ToPrimitive, including `Symbol.toPrimitive` dispatch and ordinary fallback. -/
def toPrimitive (hook : BodyHook P) (value : Value)
    (hint : PreferredType := .default) : JSM P Primitive :=
  match value with
  | .primitive primitive => pure primitive
  | .object receiver => do
      match ← getMethod hook receiver (.symbol (.wellKnown .toPrimitive)) with
      | some method =>
          match ← Call.call hook method value #[.primitive (.string (hintString hint))] with
          | .primitive primitive => pure primitive
          | .object _ => ObjectAccess.throwTypeError "Symbol.toPrimitive returned an object"
      | none => ordinaryToPrimitive hook receiver hint

/-- Value-level ToNumber first performs object coercion, then the committed primitive conversion. -/
def toNumber (hook : BodyHook P) (value : Value) : JSM P JSNumber := do
  coercion (← toPrimitive hook value .number).toNumber

/-- Value-level ToString first performs object coercion, then the committed primitive conversion. -/
def toString (hook : BodyHook P) (value : Value) : JSM P JSString := do
  coercion (← toPrimitive hook value .string).toString

/-- Value-level ToNumeric preserves BigInt after object coercion. -/
def toNumeric (hook : BodyHook P) (value : Value) : JSM P Numeric := do
  coercion (← toPrimitive hook value .number).toNumeric

/-- Value-level ToPropertyKey requests a string-preferred primitive and preserves symbols. -/
def toPropertyKey (hook : BodyHook P) (value : Value) : JSM P PropertyKey := do
  coercion (← toPrimitive hook value .string).toPropertyKey

/-- ECMAScript ToObject. Existing object identity is retained and non-nullish primitives are boxed. -/
def toObject (value : Value) : JSM P RefId := fun machine =>
  match value with
  | .object ref =>
      match machine.heap.get? ref with
      | .ok _ => .done (.normal ref) machine
      | .error fault => .fault (heapFault fault) machine
  | .primitive .undefined | .primitive .null =>
      ObjectAccess.throwTypeError "cannot convert nullish value to object" machine
  | .primitive primitive =>
      match machine.intrinsics with
      | none => .fault (.runtime .realmNotInitialized) machine
      | some intrinsics =>
          if !intrinsics.intrinsicsRefsValid machine.heap then
            .fault (.runtime .invalidRealmIntrinsics) machine
          else
            match intrinsics.prototypeFor? primitive with
            | none => .fault (.runtime .invalidRealmIntrinsics) machine
            | some prototype =>
                match machine.heap.allocatePrimitiveWrapper primitive (some prototype) with
                | .ok (ref, heap) => .done (.normal ref) (machine.setHeap heap)
                | .error fault => .fault (heapFault fault) machine

end AbstractOperations
end TSLean.JS
