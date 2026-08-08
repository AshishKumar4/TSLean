import TSLean.JS.Heap

namespace TSLean.Refinement

open TSLean.JS

namespace Heap

/-- A well-formed heap extension that leaves every previously allocated object record unchanged. -/
structure ExactExtension (old next : JS.Heap) : Prop where
  oldWellFormed : old.WellFormed
  nextWellFormed : next.WellFormed
  size_le : old.size ≤ next.size
  get_eq : ∀ ref object, old.get? ref = .ok object → next.get? ref = .ok object

/-- Exact heap extension is reflexive on well-formed heaps. -/
theorem ExactExtension.refl (heap : JS.Heap) (valid : heap.WellFormed) :
    ExactExtension heap heap :=
  ⟨valid, valid, Nat.le_refl _, fun _ _ found => found⟩

/-- Exact heap extensions compose. -/
theorem ExactExtension.trans {first second third : JS.Heap}
    (left : ExactExtension first second) (right : ExactExtension second third) :
    ExactExtension first third :=
  ⟨left.oldWellFormed, right.nextWellFormed, Nat.le_trans left.size_le right.size_le,
    fun ref object found => right.get_eq ref object (left.get_eq ref object found)⟩

/-- Exact extension implies the identity continuity guaranteed by the JS heap. -/
theorem ExactExtension.continuesFrom {old next : JS.Heap} (extension : ExactExtension old next) :
    old.ContinuesFrom next := by
  refine ⟨extension.size_le, ?_⟩
  intro ref kind found
  unfold JS.Heap.objectKind? at found ⊢
  cases oldFound : old.get? ref with
  | error fault => simp [oldFound] at found
  | ok object =>
      have nextFound := extension.get_eq ref object oldFound
      simp [oldFound] at found
      subst kind
      exact ⟨object.kind, by simp [nextFound], ObjectKind.continuesFrom_refl object.kind⟩

/-- Exact extension preserves every value valid in the old heap. -/
theorem ExactExtension.preserves_valueValid {old next : JS.Heap}
    (extension : ExactExtension old next) (value : Value)
    (valid : old.valueValid value = true) : next.valueValid value = true :=
  extension.continuesFrom.preserves_valueValid value valid

/-- Any observation computed solely from an old object record is framed by exact extension. -/
theorem ExactExtension.frame {old next : JS.Heap} (extension : ExactExtension old next)
    (ref : RefId) (object : ObjectRecord) (found : old.get? ref = .ok object)
    {β : Sort _} (observe : ObjectRecord → β) :
    (old.get? ref).map observe = (next.get? ref).map observe := by
  rw [found, extension.get_eq ref object found]

/-- Own-property reads of existing objects are unchanged by exact extension. -/
theorem ExactExtension.preserves_getOwnProperty {old next : JS.Heap}
    (extension : ExactExtension old next) (ref : RefId) (object : ObjectRecord)
    (found : old.get? ref = .ok object) (key : PropertyKey) :
    next.getOwnProperty ref key = old.getOwnProperty ref key := by
  unfold JS.Heap.getOwnProperty
  rw [found, extension.get_eq ref object found]

/-- Own-key enumeration of existing objects is unchanged by exact extension. -/
theorem ExactExtension.preserves_ownPropertyKeys {old next : JS.Heap}
    (extension : ExactExtension old next) (ref : RefId) (object : ObjectRecord)
    (found : old.get? ref = .ok object) :
    next.ownPropertyKeys ref = old.ownPropertyKeys ref := by
  unfold JS.Heap.ownPropertyKeys
  rw [found, extension.get_eq ref object found]

/-- Existing object kinds are exactly preserved. -/
theorem ExactExtension.preserves_objectKind {old next : JS.Heap}
    (extension : ExactExtension old next) (ref : RefId) (object : ObjectRecord)
    (found : old.get? ref = .ok object) :
    next.objectKind? ref = old.objectKind? ref := by
  unfold JS.Heap.objectKind?
  rw [found, extension.get_eq ref object found]

/-- Existing object prototypes are exactly preserved. -/
theorem ExactExtension.preserves_prototype {old next : JS.Heap}
    (extension : ExactExtension old next) (ref : RefId) (object : ObjectRecord)
    (found : old.get? ref = .ok object) :
    (next.get? ref).map (·.prototype) = (old.get? ref).map (·.prototype) := by
  rw [found, extension.get_eq ref object found]

private theorem get_append_eq (heap next : JS.Heap) (object : ObjectRecord)
    (objectsEq : next.objects = heap.objects.push object)
    (ref : RefId) (oldObject : ObjectRecord) (found : heap.get? ref = .ok oldObject) :
    next.get? ref = .ok oldObject := by
  unfold JS.Heap.get? at found ⊢
  rw [objectsEq]
  cases lookup : heap.objects[ref.value]? with
  | none => simp [lookup] at found
  | some current =>
      simp [lookup] at found
      subst current
      have different : ref.value ≠ heap.objects.size :=
        Nat.ne_of_lt (Array.getElem?_eq_some_iff.mp lookup).choose
      simp [Array.getElem?_push, different, lookup]

/-- Successful ordinary allocation is an exact extension. -/
theorem allocate_exactExtension (heap next : JS.Heap) (prototype : Option RefId)
    (extensible : Bool) (ref : RefId) (valid : heap.WellFormed)
    (allocated : heap.allocate prototype extensible = .ok (ref, next)) :
    ExactExtension heap next := by
  refine ⟨valid, JS.Heap.allocate_preserves_wellFormed heap next prototype extensible ref valid allocated,
    ?_, ?_⟩
  · exact (JS.Heap.allocate_continuesFrom heap next prototype extensible ref allocated).1
  · intro oldRef object found
    unfold JS.Heap.allocate at allocated
    split at allocated
    · rcases allocated with ⟨rfl, rfl⟩
      exact get_append_eq heap _ _ rfl oldRef object found
    · cases prototype <;> simp_all

/-- Successful primitive-wrapper allocation is an exact extension. -/
theorem allocatePrimitiveWrapper_exactExtension (heap next : JS.Heap) (value : Primitive)
    (prototype : Option RefId) (ref : RefId) (valid : heap.WellFormed)
    (allocated : heap.allocatePrimitiveWrapper value prototype = .ok (ref, next)) :
    ExactExtension heap next := by
  refine ⟨valid,
    JS.Heap.allocatePrimitiveWrapper_preserves_wellFormed heap next value prototype ref valid allocated,
    (JS.Heap.allocatePrimitiveWrapper_continuesFrom heap next value prototype ref allocated).1, ?_⟩
  intro oldRef object found
  unfold JS.Heap.allocatePrimitiveWrapper at allocated
  split at allocated <;> try contradiction
  split at allocated
  · rcases allocated with ⟨rfl, rfl⟩
    exact get_append_eq heap _ _ rfl oldRef object found
  · cases prototype <;> simp_all

/-- Successful list-input array allocation is an exact extension. -/
theorem allocateArray_exactExtension (heap next : JS.Heap) (elements : List (Option Value))
    (prototype : Option RefId) (ref : RefId) (valid : heap.WellFormed)
    (allocated : heap.allocateArray elements prototype = .ok (ref, next)) :
    ExactExtension heap next := by
  refine ⟨valid, JS.Heap.allocateArray_preserves_wellFormed heap next elements prototype ref valid allocated,
    (JS.Heap.allocateArray_continuesFrom heap next elements prototype ref allocated).1, ?_⟩
  intro oldRef object found
  unfold JS.Heap.allocateArray JS.Heap.allocateArrayFromArray at allocated
  split at allocated <;> try contradiction
  cases prototype with
  | none =>
      simp only at allocated
      rw [← Array.foldl_toList] at allocated
      simp only at allocated
      split at allocated <;> try contradiction
      rcases allocated with ⟨rfl, rfl⟩
      exact get_append_eq heap _ _ rfl oldRef object found
  | some prototype =>
      simp only at allocated
      cases prototypeFound : heap.get? prototype with
      | error fault => simp [prototypeFound] at allocated
      | ok prototypeObject =>
          rw [prototypeFound, ← Array.foldl_toList] at allocated
          simp only at allocated
          split at allocated <;> try contradiction
          rcases allocated with ⟨rfl, rfl⟩
          exact get_append_eq heap _ _ rfl oldRef object found

/-- Successful array-input allocation is an exact extension. -/
theorem allocateArrayFromArray_exactExtension (heap next : JS.Heap)
    (elements : Array (Option Value)) (prototype : Option RefId) (ref : RefId)
    (valid : heap.WellFormed)
    (allocated : heap.allocateArrayFromArray elements prototype = .ok (ref, next)) :
    ExactExtension heap next := by
  apply allocateArray_exactExtension heap next elements.toList prototype ref valid
  simpa [JS.Heap.allocateArray] using allocated

/-- Successful function allocation is an exact extension. -/
theorem allocateFunction_exactExtension (heap next : JS.Heap) (environment : EnvId)
    (kind : FunctionKind) (constructible : Bool) (prototype homeObject : Option RefId)
    (constructorMode : ConstructorMode) (lexicalThis : Option Value) (ref : RefId)
    (valid : heap.WellFormed)
    (allocated : heap.allocateFunction environment kind constructible prototype homeObject
      constructorMode lexicalThis = .ok (ref, next)) : ExactExtension heap next := by
  refine ⟨valid, JS.Heap.allocateFunction_preserves_wellFormed heap next environment kind constructible
    prototype homeObject constructorMode lexicalThis ref valid allocated,
    (JS.Heap.allocateFunction_continuesFrom heap next environment kind constructible prototype
      homeObject constructorMode lexicalThis ref allocated).1, ?_⟩
  intro oldRef object found
  unfold JS.Heap.allocateFunction at allocated
  all_goals (split at allocated <;> try simp_all)
  all_goals (split at allocated <;> try simp_all)
  all_goals (split at allocated <;> try simp_all)
  cases lexicalThis with
  | some lexicalValue =>
      all_goals (split at allocated <;> try simp_all)
      all_goals (split at allocated <;> try simp_all)
      all_goals (split at allocated <;> try simp_all)
      split at allocated <;> try contradiction
      rcases allocated with ⟨rfl, rfl⟩
      exact get_append_eq heap _ _ rfl oldRef object found
  | none =>
      all_goals (split at allocated <;> try simp_all)
      all_goals (split at allocated <;> try simp_all)
      split at allocated <;> try contradiction
      rcases allocated with ⟨rfl, rfl⟩
      exact get_append_eq heap _ _ rfl oldRef object found

/-- Successful constructor/prototype pair allocation is exact despite fresh cross-references. -/
theorem allocateConstructorPair_exactExtension (heap next : JS.Heap) (environment : EnvId)
    (functionPrototype objectPrototype : Option RefId) (classConstructor : Bool)
    (constructorMode : ConstructorMode) (constructor prototype : RefId)
    (valid : heap.WellFormed)
    (allocated : heap.allocateConstructorPair environment functionPrototype objectPrototype
      classConstructor constructorMode = .ok (constructor, prototype, next)) :
    ExactExtension heap next := by
  refine ⟨valid, JS.Heap.allocateConstructorPair_preserves_wellFormed heap next environment
    functionPrototype objectPrototype classConstructor constructorMode constructor prototype valid allocated,
    (JS.Heap.allocateConstructorPair_continuesFrom heap next environment functionPrototype
      objectPrototype classConstructor constructorMode constructor prototype allocated).1, ?_⟩
  intro oldRef object found
  unfold JS.Heap.allocateConstructorPair at allocated
  split at allocated <;> try contradiction
  split at allocated <;> try contradiction
  split at allocated <;> try contradiction
  rcases allocated with ⟨rfl, rfl, rfl⟩
  unfold JS.Heap.get? at found ⊢
  cases lookup : heap.objects[oldRef.value]? with
  | none => simp [lookup] at found
  | some current =>
      simp [lookup] at found
      subst current
      have firstDifferent : oldRef.value ≠ heap.objects.size :=
        Nat.ne_of_lt (Array.getElem?_eq_some_iff.mp lookup).choose
      have secondDifferent : oldRef.value ≠ heap.objects.size + 1 := by
        have less := (Array.getElem?_eq_some_iff.mp lookup).choose
        omega
      simp [Array.getElem?_push, firstDifferent, secondDifferent, lookup]

/-- Successful array-iterator allocation is an exact extension. -/
theorem allocateArrayIterator_exactExtension (heap next : JS.Heap) (target : RefId)
    (prototype : Option RefId) (ref : RefId) (valid : heap.WellFormed)
    (allocated : heap.allocateArrayIterator target prototype = .ok (ref, next)) :
    ExactExtension heap next := by
  refine ⟨valid, JS.Heap.allocateArrayIterator_preserves_wellFormed heap next target prototype ref
    valid allocated, (JS.Heap.allocateArrayIterator_continuesFrom heap next target prototype ref allocated).1,
    ?_⟩
  intro oldRef object found
  unfold JS.Heap.allocateArrayIterator at allocated
  simp only [Bind.bind, Except.bind] at allocated
  cases targetFound : heap.get? target with
  | error fault => simp [targetFound] at allocated
  | ok targetObject =>
      cases targetKind : targetObject.kind <;> simp [targetFound, targetKind] at allocated
      rename_i slots
      cases prototype with
      | none =>
          simp at allocated
          rcases allocated with ⟨rfl, rfl⟩
          exact get_append_eq heap _ _ rfl oldRef object found
      | some prototype =>
          cases prototypeFound : heap.get? prototype with
          | error fault =>
              simp [prototypeFound, Pure.pure, Except.pure] at allocated
          | ok prototypeObject =>
              simp [prototypeFound] at allocated
              rcases allocated with ⟨rfl, rfl⟩
              exact get_append_eq heap _ _ rfl oldRef object found

end Heap

end TSLean.Refinement
