import TSLean.JS.ObjectAccess
import TSLean.JS.PrimitiveConversion

namespace TSLean.JS

/-- The preferred primitive result requested by `ToPrimitive`. -/
inductive PreferredType where
  | default
  | string
  | number
  deriving DecidableEq

/-- Observable operations required by the effectful coercion algorithms. -/
structure CoercionEffects (m : Type → Type) [Monad m] where
  get : RefId → PropertyKey → Value → m Value
  call : RefId → Value → Array Value → m Value
  isCallable : RefId → m Bool
  typeError : String → m Empty
  throw : Value → m Empty

namespace CoercionEffects

/-- Eliminates a terminal coercion operation at the result type expected by its caller. -/
@[inline]
def terminal [Monad m] (operation : m Empty) : m α := operation >>= Empty.elim

/-- Raises a configured type error at any result type. -/
@[inline]
def raiseTypeError [Monad m] (effects : CoercionEffects m) (message : String) : m α :=
  terminal (effects.typeError message)

/-- Supplies coercion effects from the production JavaScript machine and evaluator hook.
Public specialization requires extensional equality of `JSM` results for every input machine;
compiled C byte identity is not part of the contract. -/
@[inline]
def forJSM (hook : BodyHook P) : CoercionEffects (JSM P) where
  get := ObjectAccess.get hook
  call := Call.call hook
  isCallable ref := do
    let heap ← JSM.readHeap
    match heap.isCallable ref with
    | .error fault => JSM.fail (.runtime (.heap fault))
    | .ok callable => pure callable
  typeError := ObjectAccess.throwTypeError
  throw := JSM.throwJS

/-- Lifts a pure primitive-coercion result into the configured JavaScript throw boundary. -/
@[inline]
def fromCoercion [Monad m] (effects : CoercionEffects m)
    (result : Except CoercionFault α) : m α :=
  match result with
  | .ok value => pure value
  | .error fault => terminal (effects.throw fault.toThrownValue)

end CoercionEffects

namespace AbstractOperations

private def heapFault (fault : HeapFault) : ModelFault := .runtime (.heap fault)

private def property (name : String) : PropertyKey :=
  .string (JSString.ofLeanString name)

/-- Gets a method through generic coercion effects. -/
def getMethodWith [Monad m] (effects : CoercionEffects m) (ref : RefId)
    (key : PropertyKey) : m (Option RefId) := do
  let value ← effects.get ref key (.object ref)
  match value with
  | .primitive .undefined | .primitive .null => pure none
  | .primitive _ => CoercionEffects.raiseTypeError effects "property is not callable"
  | .object method =>
      if ← effects.isCallable method then pure (some method)
       else CoercionEffects.raiseTypeError effects "property is not callable"

/-- Gets a method property. Nullish properties are absent; all other non-callable values throw. -/
@[inline]
def getMethod (hook : BodyHook P) (ref : RefId) (key : PropertyKey) : JSM P (Option RefId) :=
  getMethodWith (CoercionEffects.forJSM hook) ref key

/-- Tries one ordinary primitive-conversion method through generic coercion effects. -/
def tryOrdinaryMethodWith [Monad m] (effects : CoercionEffects m) (receiver : RefId)
    (name : String) : m (Option Primitive) := do
  let methodValue ← effects.get receiver (property name) (.object receiver)
  match methodValue with
  | .primitive _ => pure none
  | .object method =>
      if !(← effects.isCallable method) then pure none
      else
        match ← effects.call method (.object receiver) #[] with
        | .primitive primitive => pure (some primitive)
        | .object _ => pure none

/-- Tries ordinary primitive-conversion methods in order through generic coercion effects. -/
def tryOrdinaryMethodsWith [Monad m] (effects : CoercionEffects m)
    (receiver : RefId) : List String → m Primitive
  | [] => CoercionEffects.raiseTypeError effects "cannot convert object to primitive value"
  | name :: rest => do
      match ← tryOrdinaryMethodWith effects receiver name with
      | some primitive => pure primitive
      | none => tryOrdinaryMethodsWith effects receiver rest

/-- OrdinaryToPrimitive through generic coercion effects. -/
def ordinaryToPrimitiveWith [Monad m] (effects : CoercionEffects m) (receiver : RefId)
    (hint : PreferredType) : m Primitive :=
  match hint with
  | .string => tryOrdinaryMethodsWith effects receiver ["toString", "valueOf"]
  | .number | .default => tryOrdinaryMethodsWith effects receiver ["valueOf", "toString"]

/-- OrdinaryToPrimitive performs at most two ordered property reads and calls. -/
@[inline]
def ordinaryToPrimitive (hook : BodyHook P) (receiver : RefId)
    (hint : PreferredType) : JSM P Primitive :=
  ordinaryToPrimitiveWith (CoercionEffects.forJSM hook) receiver hint

/-- The exact string argument passed to an exotic `@@toPrimitive` method. -/
def hintString : PreferredType → JSString
  | .default => JSString.ofLeanString "default"
  | .string => JSString.ofLeanString "string"
  | .number => JSString.ofLeanString "number"

/-- ECMAScript ToPrimitive through generic coercion effects. -/
def toPrimitiveWith [Monad m] (effects : CoercionEffects m) (value : Value)
    (hint : PreferredType := .default) : m Primitive :=
  match value with
  | .primitive primitive => pure primitive
  | .object receiver => do
      match ← getMethodWith effects receiver (.symbol (.wellKnown .toPrimitive)) with
      | some method =>
          match ← effects.call method value #[.primitive (.string (hintString hint))] with
          | .primitive primitive => pure primitive
          | .object _ => CoercionEffects.raiseTypeError effects "Symbol.toPrimitive returned an object"
      | none => ordinaryToPrimitiveWith effects receiver hint

/-- ECMAScript ToPrimitive, including `Symbol.toPrimitive` dispatch and ordinary fallback. -/
@[inline]
def toPrimitive (hook : BodyHook P) (value : Value)
    (hint : PreferredType := .default) : JSM P Primitive :=
  toPrimitiveWith (CoercionEffects.forJSM hook) value hint

/-- Value-level ToNumber through generic coercion effects. -/
@[inline]
def toNumberWith [Monad m] (effects : CoercionEffects m) (value : Value) : m JSNumber := do
  CoercionEffects.fromCoercion effects (← toPrimitiveWith effects value .number).toNumber

/-- Value-level ToNumber first performs object coercion, then the committed primitive conversion. -/
@[inline]
def toNumber (hook : BodyHook P) (value : Value) : JSM P JSNumber :=
  toNumberWith (CoercionEffects.forJSM hook) value

/-- Value-level ToString through generic coercion effects. -/
@[inline]
def toStringWith [Monad m] (effects : CoercionEffects m) (value : Value) : m JSString := do
  CoercionEffects.fromCoercion effects (← toPrimitiveWith effects value .string).toString

/-- Value-level ToString first performs object coercion, then the committed primitive conversion. -/
@[inline]
def toString (hook : BodyHook P) (value : Value) : JSM P JSString :=
  toStringWith (CoercionEffects.forJSM hook) value

/-- Value-level ToNumeric through generic coercion effects. -/
@[inline]
def toNumericWith [Monad m] (effects : CoercionEffects m) (value : Value) : m Numeric := do
  CoercionEffects.fromCoercion effects (← toPrimitiveWith effects value .number).toNumeric

/-- Value-level ToNumeric preserves BigInt after object coercion. -/
@[inline]
def toNumeric (hook : BodyHook P) (value : Value) : JSM P Numeric :=
  toNumericWith (CoercionEffects.forJSM hook) value

/-- Value-level ToPropertyKey through generic coercion effects. -/
@[inline]
def toPropertyKeyWith [Monad m] (effects : CoercionEffects m) (value : Value) : m PropertyKey := do
  CoercionEffects.fromCoercion effects (← toPrimitiveWith effects value .string).toPropertyKey

/-- Value-level ToPropertyKey requests a string-preferred primitive and preserves symbols. -/
@[inline]
def toPropertyKey (hook : BodyHook P) (value : Value) : JSM P PropertyKey :=
  toPropertyKeyWith (CoercionEffects.forJSM hook) value

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

/-- `ToObject` preserves machine continuity and returns an allocated object identity. -/
theorem toObject_preservesResults (value : Value) :
    JSM.PreservesResults (fun ref machine =>
      machine.heap.valueValid (.object ref) = true ∧
        ∀ original, value = .object original → ref = original)
      (toObject (P := P) value) := by
  constructor
  · intro machine valid
    unfold toObject
    cases value with
    | object ref =>
        cases found : machine.heap.get? ref <;>
          simp [found] <;> exact ⟨valid, machine.continuesFrom_refl⟩
    | primitive primitive =>
        cases primitive with
        | undefined | null => exact ⟨valid, machine.continuesFrom_refl⟩
        | boolean value | number value | string value | bigint value | symbol value =>
            cases configured : machine.intrinsics with
            | none => exact ⟨valid, machine.continuesFrom_refl⟩
            | some intrinsics =>
                simp only
                split
                · exact ⟨valid, machine.continuesFrom_refl⟩
                · simp only [RealmIntrinsics.prototypeFor?]
                  cases allocated : machine.heap.allocatePrimitiveWrapper _ _ with
                  | error fault => exact ⟨valid, machine.continuesFrom_refl⟩
                  | ok result =>
                      rcases result with ⟨ref, heap⟩
                      have preserved := Heap.allocatePrimitiveWrapper_preserves_machineReferences
                        machine.heap heap _ _ ref allocated
                      have heapValid := Heap.allocatePrimitiveWrapper_preserves_wellFormed
                        machine.heap heap _ _ ref (Machine.wellFormed_heap machine valid) allocated
                      exact ⟨Machine.setHeap_preserves_wellFormed machine heap valid heapValid
                          preserved.1,
                        Machine.setHeap_continuesFrom_machineReferences machine heap valid heapValid
                          preserved.1⟩
  · intro machine valid
    cases value with
    | object ref =>
        cases found : machine.heap.get? ref with
        | error fault => simp [toObject, found, RunResult.CompletionValuesValid]
        | ok object =>
            have validRef : machine.heap.valueValid (.object ref) = true := by
              unfold Heap.get? at found
              cases lookup : machine.heap.objects[ref.value]? with
              | none => simp [lookup] at found
              | some current =>
                  exact decide_eq_true (by
                    simpa [Heap.size] using (Array.getElem?_eq_some_iff.mp lookup).choose)
            have resultValid : machine.heap.valueValid (.object ref) = true ∧
                ∀ original, (.object ref : Value) = .object original → ref = original :=
              ⟨validRef, by
                intro original equal
                cases equal
                rfl⟩
            simpa only [toObject, found, RunResult.CompletionValuesValid] using resultValid
    | primitive primitive =>
        unfold toObject
        cases primitive with
        | undefined | null => rfl
        | boolean value | number value | string value | bigint value | symbol value =>
            cases configured : machine.intrinsics with
            | none => trivial
            | some intrinsics =>
                simp only
                split
                · trivial
                · simp only [RealmIntrinsics.prototypeFor?]
                  cases allocated : machine.heap.allocatePrimitiveWrapper _ _ with
                  | error fault => trivial
                  | ok result =>
                      rcases result with ⟨ref, heap⟩
                      exact ⟨(Heap.allocatePrimitiveWrapper_preserves_machineReferences
                        machine.heap heap _ _ ref allocated).2, by intros original impossible; contradiction⟩

end AbstractOperations
end TSLean.JS
