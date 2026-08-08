import TSLean.JS.AbstractEquality
import TSLean.JS.HasInstance

namespace TSLean.JS

namespace AbstractOperations

/-- Boolean wrappers select the configured Boolean prototype. -/
theorem boolean_wrapper_prototype (intrinsics : RealmIntrinsics) (value : Bool) :
    intrinsics.prototypeFor? (.boolean value) = some intrinsics.booleanPrototype := rfl

/-- Number wrappers select the configured Number prototype. -/
theorem number_wrapper_prototype (intrinsics : RealmIntrinsics) (value : JSNumber) :
    intrinsics.prototypeFor? (.number value) = some intrinsics.numberPrototype := rfl

/-- String wrappers select the configured String prototype. -/
theorem string_wrapper_prototype (intrinsics : RealmIntrinsics) (value : JSString) :
    intrinsics.prototypeFor? (.string value) = some intrinsics.stringPrototype := rfl

/-- BigInt wrappers select the configured BigInt prototype. -/
theorem bigint_wrapper_prototype (intrinsics : RealmIntrinsics) (value : Int) :
    intrinsics.prototypeFor? (.bigint value) = some intrinsics.bigintPrototype := rfl

/-- Symbol wrappers select the configured Symbol prototype. -/
theorem symbol_wrapper_prototype (intrinsics : RealmIntrinsics) (id : SymbolId) :
    intrinsics.prototypeFor? (.symbol id) = some intrinsics.symbolPrototype := rfl

/-- Primitive ToPrimitive is an effect-free passthrough for every hint. -/
theorem toPrimitive_primitive (hook : BodyHook P) (primitive : Primitive) (hint : PreferredType) :
    toPrimitive hook (.primitive primitive) hint = pure primitive := rfl

/-- Primitive symbol keys retain symbol identity without string coercion. -/
theorem toPropertyKey_symbol (hook : BodyHook P) (id : SymbolId) :
    toPropertyKey hook (.primitive (.symbol id)) = pure (.symbol id) := rfl

/-- ToObject preserves the identity and machine state of a valid object. -/
theorem toObject_object (machine : Machine P) (ref : RefId) (object : ObjectRecord)
    (valid : machine.heap.get? ref = .ok object) :
    toObject (.object ref) machine = .done (.normal ref) machine := by
  simp [toObject, valid]

/-- ToObject produces a catchable TypeError for undefined. -/
theorem toObject_undefined (machine : Machine P) :
    toObject (.primitive .undefined) machine =
      .done (.thrown (.primitive (.string
        (JSString.ofLeanString "TypeError: cannot convert nullish value to object")))) machine := rfl

/-- ToObject produces a catchable TypeError for null. -/
theorem toObject_null (machine : Machine P) :
    toObject (.primitive .null) machine =
      .done (.thrown (.primitive (.string
        (JSString.ofLeanString "TypeError: cannot convert nullish value to object")))) machine := rfl

/-- Configured ToObject passes the selected intrinsic prototype to wrapper allocation exactly. -/
theorem toObject_primitive_wrapper (machine : Machine P) (intrinsics : RealmIntrinsics)
    (primitive : Primitive) (prototype ref : RefId) (heap : Heap)
    (configured : machine.intrinsics = some intrinsics)
    (valid : intrinsics.intrinsicsRefsValid machine.heap = true)
    (selected : intrinsics.prototypeFor? primitive = some prototype)
    (allocated : machine.heap.allocatePrimitiveWrapper primitive (some prototype) = .ok (ref, heap)) :
    toObject (.primitive primitive) machine = .done (.normal ref) (machine.setHeap heap) := by
  cases primitive <;> simp_all [RealmIntrinsics.prototypeFor?, toObject]

/-- GetMethod maps an observed undefined property result to absence without further effects. -/
theorem getMethod_undefined (hook : BodyHook P) (machine next : Machine P)
    (ref : RefId) (key : PropertyKey)
    (got : ObjectAccess.get hook ref key (.object ref) machine =
      .done (.normal (.primitive .undefined)) next) :
    getMethod hook ref key machine = .done (.normal none) next := by
  unfold getMethod
  unfold getMethodWith CoercionEffects.forJSM
  change JSM.bind (ObjectAccess.get hook ref key (.object ref)) _ machine = _
  unfold JSM.bind
  rw [got]
  rfl

/-- GetMethod maps an observed null property result to absence without further effects. -/
theorem getMethod_null (hook : BodyHook P) (machine next : Machine P)
    (ref : RefId) (key : PropertyKey)
    (got : ObjectAccess.get hook ref key (.object ref) machine =
      .done (.normal (.primitive .null)) next) :
    getMethod hook ref key machine = .done (.normal none) next := by
  unfold getMethod
  unfold getMethodWith CoercionEffects.forJSM
  change JSM.bind (ObjectAccess.get hook ref key (.object ref)) _ machine = _
  unfold JSM.bind
  rw [got]
  rfl

end AbstractOperations

namespace Instanceof

/-- OrdinaryHasInstance returns false for primitive candidates after a successful callable check. -/
theorem ordinaryHasInstance_primitive (hook : BodyHook P) (machine : Machine P)
    (constructor : RefId) (primitive : Primitive)
    (callable : machine.heap.isCallable constructor = .ok true) :
    ordinaryHasInstance hook constructor (.primitive primitive) machine =
      .done (.normal false) machine := by
  simp [ordinaryHasInstance, callable]

end Instanceof

end TSLean.JS
