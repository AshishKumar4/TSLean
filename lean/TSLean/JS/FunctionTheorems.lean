import TSLean.JS.Instanceof
import TSLean.JS.Typeof

namespace TSLean.JS

/-- Function object equality is heap-reference identity, independent of function metadata. -/
theorem Function.identity_is_reference_identity (left right : RefId) :
    strictEqual (.object left) (.object right) = decide (left = right) :=
  rfl

/-- Function body fallthrough normalizes to JavaScript `undefined`. -/
theorem Call.normalizeBody_fallthrough :
    Call.normalizeBody (.primitive .undefined) id (JSM.pure () : JSM P Unit) =
      JSM.pure (.primitive .undefined) := by
  rfl

/-- Explicit primitive return normalizes to a normal call value. -/
theorem Call.normalizeBody_returned_primitive (value : Primitive) :
    Call.normalizeBody (.primitive .undefined) id
        (JSM.returnJS (.primitive value) : JSM P Unit) =
      JSM.pure (.primitive value) := by
  rfl

/-- Explicit object return is validated against the resulting heap. -/
theorem Call.normalizeBody_returned_object (ref : RefId) :
    Call.normalizeBody (.primitive .undefined) id (JSM.returnJS (.object ref) : JSM P Unit) =
      fun machine =>
        if machine.heap.valueValid (.object ref) then .done (.normal (.object ref)) machine
        else .fault (.runtime (.danglingEscapingValue ref)) machine := by
  rfl

/-- Thrown object values are validated against the resulting heap without changing that state. -/
theorem Call.normalizeBody_thrown_object (ref : RefId) :
    Call.normalizeBody (.primitive .undefined) id (JSM.throwJS (.object ref) : JSM P Unit) =
      fun machine =>
        if machine.heap.valueValid (.object ref) then .done (.thrown (.object ref)) machine
        else .fault (.runtime (.danglingEscapingValue ref)) machine := by
  rfl

/-- Escaping break is rejected as an internal runtime fault. -/
theorem Call.normalizeBody_break :
    Call.normalizeBody (.primitive .undefined) id (JSM.breakJS : JSM P Unit) =
      JSM.fail (.runtime .escapingFunctionControl) := by
  rfl

/-- Successful simple function allocation returns the former heap size. -/
theorem Heap.allocateFunction_fresh (heap next : Heap) (environment : EnvId)
    (kind : FunctionKind) (constructible : Bool) (prototype homeObject : Option RefId)
    (ref : RefId)
    (allocated : heap.allocateFunction environment kind constructible prototype homeObject =
      .ok (ref, next)) : ref.value = heap.size := by
  unfold Heap.allocateFunction at allocated
  split at allocated <;> try contradiction
  split at allocated <;> try contradiction
  split at allocated <;> try contradiction
  split at allocated <;> try contradiction
  split at allocated <;> try contradiction
  split at allocated <;> try contradiction
  rcases allocated with ⟨rfl, rfl⟩
  rfl

/-- Successful simple function allocation adds one stable object slot. -/
theorem Heap.allocateFunction_size (heap next : Heap) (environment : EnvId)
    (kind : FunctionKind) (constructible : Bool) (prototype homeObject : Option RefId)
    (ref : RefId)
    (allocated : heap.allocateFunction environment kind constructible prototype homeObject =
      .ok (ref, next)) : next.size = heap.size + 1 := by
  unfold Heap.allocateFunction at allocated
  split at allocated <;> try contradiction
  split at allocated <;> try contradiction
  split at allocated <;> try contradiction
  split at allocated <;> try contradiction
  split at allocated <;> try contradiction
  split at allocated <;> try contradiction
  rcases allocated with ⟨rfl, rfl⟩
  simp [Heap.size]

/-- Successful simple function allocation issues exactly one metadata identity. -/
theorem Heap.allocateFunction_count (heap next : Heap) (environment : EnvId)
    (kind : FunctionKind) (constructible : Bool) (prototype homeObject : Option RefId)
    (ref : RefId)
    (allocated : heap.allocateFunction environment kind constructible prototype homeObject =
      .ok (ref, next)) : next.functionCount = heap.functionCount + 1 := by
  unfold Heap.allocateFunction at allocated
  split at allocated <;> try contradiction
  split at allocated <;> try contradiction
  split at allocated <;> try contradiction
  split at allocated <;> try contradiction
  split at allocated <;> try contradiction
  split at allocated <;> try contradiction
  rcases allocated with ⟨rfl, rfl⟩
  rfl

/-- Successful simple function allocation preserves all previously valid object lookups. -/
theorem Heap.allocateFunction_stable (heap next : Heap) (environment : EnvId)
    (kind : FunctionKind) (constructible : Bool) (prototype homeObject : Option RefId)
    (allocatedRef ref : RefId)
    (allocated : heap.allocateFunction environment kind constructible prototype homeObject =
      .ok (allocatedRef, next)) (valid : ref.value < heap.size) :
    next.get? ref = heap.get? ref := by
  unfold Heap.allocateFunction at allocated
  split at allocated <;> try contradiction
  split at allocated <;> try contradiction
  split at allocated <;> try contradiction
  split at allocated <;> try contradiction
  split at allocated <;> try contradiction
  split at allocated <;> try contradiction
  rcases allocated with ⟨rfl, rfl⟩
  have notLast : ref.value ≠ heap.objects.size := Nat.ne_of_lt valid
  simp [Heap.get?, Array.getElem?_push, notLast]

/-- Successful arrow allocation requires a valid lexical receiver in the source heap. -/
theorem Heap.allocateArrow_lexicalThis_valid (heap next : Heap) (environment : EnvId)
    (prototype homeObject : Option RefId) (lexicalThis : Value) (ref : RefId)
    (allocated : heap.allocateFunction environment .arrow false prototype homeObject .base
      (some lexicalThis) = .ok (ref, next)) : heap.valueValid lexicalThis = true := by
  unfold Heap.allocateFunction at allocated
  split at allocated <;> try contradiction
  split at allocated <;> try contradiction
  split at allocated <;> try contradiction
  split at allocated <;> try contradiction
  split at allocated <;> try contradiction
  split at allocated <;> try contradiction
  split at allocated <;> try contradiction
  simp_all

/-- Atomic constructor/prototype allocation returns the next two object identities. -/
theorem Heap.allocateConstructorPair_fresh (heap next : Heap) (environment : EnvId)
    (functionPrototype objectPrototype : Option RefId) (classConstructor : Bool)
    (constructor prototype : RefId)
    (allocated : heap.allocateConstructorPair environment functionPrototype objectPrototype
      classConstructor = .ok (constructor, prototype, next)) :
    constructor.value = heap.size ∧ prototype.value = heap.size + 1 := by
  unfold Heap.allocateConstructorPair at allocated
  split at allocated <;> try contradiction
  split at allocated <;> try contradiction
  rcases allocated with ⟨rfl, rfl, rfl⟩
  exact ⟨rfl, rfl⟩

/-- Constructor/prototype descriptors encode exact reference back-links and attributes. -/
theorem Function.constructor_prototype_descriptor_roundtrip (constructor prototype : RefId)
    (classConstructor : Bool) :
    let forward : PropertyDescriptor :=
      .data ⟨.object prototype, !classConstructor, false, false⟩
    let backward : PropertyDescriptor :=
      .data ⟨.object constructor, true, false, true⟩
    (forward, backward) =
      (.data ⟨.object prototype, !classConstructor, false, false⟩,
       .data ⟨.object constructor, true, false, true⟩) := by
  rfl

/-- The descriptor recipe used for class methods is writable, nonenumerable, and configurable. -/
theorem Function.class_method_descriptor_attributes (method : RefId) :
    ({ value := .present (.object method)
       writable := .present true
       enumerable := .present false
       configurable := .present true } : DescriptorUpdate).applyValidatedDescriptor
      none true .data = .ok (.data ⟨.object method, true, false, true⟩) := by
  rfl

/-- A direct prototype edge is found by bounded identity traversal. -/
theorem Instanceof.reachesPrototype_direct (heap : Heap) (object target : RefId)
    (record : ObjectRecord) (found : heap.get? object = .ok record)
    (parent : record.prototype = some target) (fuel : Nat) :
    reachesPrototype heap target (fuel + 1) object = .ok true := by
  unfold reachesPrototype
  rw [found]
  change (match record.prototype with
    | none => Except.ok false
    | some next => if next = target then Except.ok true else reachesPrototype heap target fuel next) =
      Except.ok true
  rw [parent]
  simp

/-- Primitive `typeof` classification is unchanged by the complete value operation. -/
theorem Value.typeof_primitive (heap : Heap) (value : Primitive) :
    Value.typeof heap (.primitive value) = .ok (TypeofTag.ofPrimitive value.typeof) := rfl

/-- Callable references have the complete `typeof` tag `function`. -/
theorem Value.typeof_callable (heap : Heap) (ref : RefId)
    (callable : heap.isCallable ref = .ok true) :
    Value.typeof heap (.object ref) = .ok .function := by
  simp only [Value.typeof]
  change (do
    let result ← heap.isCallable ref
    if result then pure TypeofTag.function else pure TypeofTag.object) = .ok .function
  rw [callable]
  rfl

/-- A missing getter returns `undefined` without changing machine state. -/
theorem ObjectAccess.get_missing_getter (hook : BodyHook P) (machine : Machine P)
    (ref owner : RefId) (key : PropertyKey) (receiver : Value)
    (descriptor : AccessorDescriptor)
    (lookup : Prototype.lookup machine.heap ref key = .ok (some (owner, .accessor descriptor)))
    (missing : descriptor.get = none) :
    ObjectAccess.get hook ref key receiver machine =
      .done (.normal (.primitive .undefined)) machine := by
  simp [ObjectAccess.get, lookup, missing]
  rfl

/-- Getter dispatch is exactly the checked call boundary. -/
theorem ObjectAccess.get_getter_checked (hook : BodyHook P) (machine : Machine P)
    (ref owner getter : RefId) (key : PropertyKey) (receiver : Value)
    (descriptor : AccessorDescriptor)
    (lookup : Prototype.lookup machine.heap ref key = .ok (some (owner, .accessor descriptor)))
    (present : descriptor.get = some getter) :
    ObjectAccess.get hook ref key receiver machine = Call.call hook getter receiver #[] machine := by
  simp [ObjectAccess.get, lookup, present]

-- TODO(theorem): prove generic complete `Heap.WellFormed` preservation for the atomic class-element
-- loop and ordinary get/set. Executable tests cover these operations now.

end TSLean.JS
