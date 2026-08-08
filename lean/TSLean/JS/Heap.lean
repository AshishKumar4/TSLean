import TSLean.JS.OrderedProps

namespace TSLean.JS

/-- ECMAScript function invocation categories. -/
inductive FunctionKind where
  | ordinary
  | arrow
  | classConstructor
  deriving DecidableEq

/-- Constructor receiver initialization mode. Derived bodies require `super()` semantics. -/
inductive ConstructorMode where
  | base
  | derived
  deriving DecidableEq

/-- Data-only function metadata. Source evaluation remains outside the heap. -/
structure FunctionSlots where
  functionId : FunctionId
  environment : EnvId
  kind : FunctionKind
  constructible : Bool
  constructorMode : ConstructorMode
  homeObject : Option RefId
  lexicalThis : Option Value
  deriving DecidableEq

/-- Array exotic state. Element descriptors remain in the ordinary property store; holes are
absence from that store. -/
structure ArraySlots where
  length : Nat
  lengthWritable : Bool
  deriving DecidableEq

/-- Array iterator state owned by the heap. -/
structure ArrayIteratorSlots where
  target : RefId
  nextIndex : Nat
  done : Bool
  deriving DecidableEq

/-- Primitive value retained by an ECMAScript wrapper object. Null and undefined are never boxed. -/
structure PrimitiveWrapperSlots where
  value : Primitive
  deriving DecidableEq

/-- Object categories represented by the heap. -/
inductive ObjectKind where
  | ordinary
  | function (slots : FunctionSlots)
  | array (slots : ArraySlots)
  | arrayIterator (slots : ArrayIteratorSlots)
  | primitiveWrapper (slots : PrimitiveWrapperSlots)
  deriving DecidableEq

/-- Stable object-kind labels used by typed wrong-kind faults. -/
inductive ObjectKindTag where
  | ordinary
  | function
  | array
  | arrayIterator
  | primitiveWrapper
  deriving DecidableEq

namespace ObjectKind

/-- Returns the stable label for an object's internal-method category. -/
def tag : ObjectKind → ObjectKindTag
  | .ordinary => .ordinary
  | .function _ => .function
  | .array _ => .array
  | .arrayIterator _ => .arrayIterator
  | .primitiveWrapper _ => .primitiveWrapper

end ObjectKind

/-- Read-only heap payload for an ECMAScript object. -/
structure ObjectRecord where
  private mk ::
  properties : OrderedProps
  prototype : Option RefId
  extensible : Bool
  kind : ObjectKind

/-- A stable append-only table whose constructor is unavailable outside this module. -/
structure Heap where
  private mk ::
  objects : Array ObjectRecord
  nextFunctionId : Nat

/-- Heap validation and access failures. -/
inductive HeapFault where
  | invalidRef (ref : RefId)
  | invalidPrototype (ref : RefId)
  | wrongObjectKind (ref : RefId) (expected actual : ObjectKindTag)
  | cannotBoxPrimitive (value : Primitive)
  | cycleOrFuelExhausted
  | invalidFunctionMetadata
  deriving DecidableEq

/-- Abrupt/model errors from property definition, distinct from invariant rejection. -/
inductive DefinePropertyFault where
  | heap (fault : HeapFault)
  | syntax (fault : DescriptorSyntaxFault)
  | invalidValueRef (ref : RefId)
  | invalidAccessor (ref : RefId)
  | nonCallableAccessor (ref : RefId)
  | invalidArrayLength (value : JSNumber)
  | invalidArrayLengthValue (value : Value)
  | arrayTooLong (length : Nat)
  deriving DecidableEq

namespace Heap

/-- The empty valid heap. -/
def empty : Heap := .mk #[] 0

/-- Number of stable allocated references. -/
def size (heap : Heap) : Nat := heap.objects.size

/-- Number of function metadata identities issued by this heap. -/
def functionCount (heap : Heap) : Nat := heap.nextFunctionId

/-- Reads an object or returns a typed invalid-reference fault. -/
def get? (heap : Heap) (ref : RefId) : Except HeapFault ObjectRecord :=
  match heap.objects[ref.value]? with
  | some object => .ok object
  | none => .error (.invalidRef ref)

/-- Reads an object's internal-method kind without exposing its record constructor. -/
def objectKind? (heap : Heap) (ref : RefId) : Option ObjectKind :=
  match heap.get? ref with
  | .ok object => some object.kind
  | .error _ => none

private def validPrototype (heap : Heap) : Option RefId → Bool
  | none => true
  | some ref => ref.value < heap.size

/-- Allocates an ordinary object after validating its prototype reference. -/
def allocate (heap : Heap) (prototype : Option RefId := none) (extensible : Bool := true) :
    Except HeapFault (RefId × Heap) :=
  if validPrototype heap prototype then
    let ref := ⟨heap.objects.size⟩
    .ok (ref, .mk (heap.objects.push (.mk OrderedProps.empty prototype extensible .ordinary))
      heap.nextFunctionId)
  else
    match prototype with
    | some ref => .error (.invalidPrototype ref)
    | none => .error .cycleOrFuelExhausted

private def primitiveBoxable : Primitive → Bool
  | .null | .undefined => false
  | _ => true

/-- Allocates an honest ECMAScript primitive wrapper. String indexed properties and `length` are
synthetic; all other primitive wrappers begin without own properties. -/
def allocatePrimitiveWrapper (heap : Heap) (value : Primitive)
    (prototype : Option RefId := none) : Except HeapFault (RefId × Heap) :=
  if !primitiveBoxable value then
    .error (.cannotBoxPrimitive value)
  else if validPrototype heap prototype then
    let ref := ⟨heap.objects.size⟩
    .ok (ref, .mk (heap.objects.push (.mk OrderedProps.empty prototype true
      (.primitiveWrapper ⟨value⟩))) heap.nextFunctionId)
  else
    match prototype with
    | some ref => .error (.invalidPrototype ref)
    | none => .error .cycleOrFuelExhausted

/-- The largest valid ECMAScript array length. -/
def maxArrayLength : Nat := 4294967295

/-- The canonical property key for an array's synthetic `length` property. -/
def lengthPropertyKey : PropertyKey := .string (JSString.ofLeanString "length")

private def floorLog2Aux : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n => if n < 2 then 0 else floorLog2Aux fuel (n / 2) + 1

private def floorLog2 (n : Nat) : Nat := floorLog2Aux 64 n

private def replace (heap : Heap) (ref : RefId) (object : ObjectRecord) : Except HeapFault Heap :=
  if inBounds : ref.value < heap.objects.size then
    .ok (.mk (heap.objects.set ref.value object inBounds) heap.nextFunctionId)
  else .error (.invalidRef ref)

/-- Replacing an existing object does not change the stable reference arena size. -/
theorem replace_size (heap next : Heap) (ref : RefId) (object : ObjectRecord)
    (replaced : heap.replace ref object = .ok next) : next.size = heap.size := by
  unfold replace at replaced
  split at replaced
  · cases replaced
    simp [size]
  · contradiction

/-- Replacing an existing object does not issue a function identity. -/
theorem replace_functionCount (heap next : Heap) (ref : RefId) (object : ObjectRecord)
    (replaced : heap.replace ref object = .ok next) :
    next.functionCount = heap.functionCount := by
  unfold replace at replaced
  split at replaced
  · cases replaced
    rfl
  · contradiction

/-- Reading the replaced reference returns exactly the replacement object. -/
theorem get?_replace_same (heap next : Heap) (ref : RefId) (object : ObjectRecord)
    (replaced : heap.replace ref object = .ok next) : next.get? ref = .ok object := by
  unfold replace at replaced
  split at replaced
  · cases replaced
    simp [get?]
  · contradiction

/-- Replacing one object leaves every other reference lookup unchanged. -/
theorem get?_replace_ne (heap next : Heap) (target ref : RefId) (object : ObjectRecord)
    (different : ref ≠ target) (replaced : heap.replace target object = .ok next) :
    next.get? ref = heap.get? ref := by
  unfold replace at replaced
  split at replaced
  · cases replaced
    have differentIndex : ref.value ≠ target.value := by
      intro equal
      apply different
      cases ref
      cases target
      simp_all
    simp [get?, Ne.symm differentIndex]
  · contradiction

private theorem replace_preserves_objectKind (heap next : Heap) (target ref : RefId)
    (current replacement : ObjectRecord) (found : heap.get? target = .ok current)
    (sameKind : replacement.kind = current.kind)
    (replaced : heap.replace target replacement = .ok next) :
    next.objectKind? ref = heap.objectKind? ref := by
  unfold replace at replaced
  split at replaced
  · cases replaced
    unfold objectKind? get?
    by_cases sameRef : ref = target
    · subst ref
      cases lookup : heap.objects[target.value]? with
      | none => simp [get?, lookup] at found
      | some object =>
          have objectEq : object = current := by simpa [get?, lookup] using found
          subst object
          simp [sameKind]
    · have differentIndex : ref.value ≠ target.value := by
        intro equal
        apply sameRef
        cases ref
        cases target
        simp_all
      have reverseIndex : target.value ≠ ref.value := Ne.symm differentIndex
      simp [reverseIndex]
  · contradiction

/-- Exact binary64 encoding of a valid array length. This uses integer bit construction rather than
an unproved bridge through Lean `Float`. -/
def arrayLengthNumber (length : Nat) : JSNumber :=
  if length = 0 then .positiveZero
  else
    let exponent := floorLog2 length
    let leading := 1 <<< exponent
    let fraction := (length - leading) <<< (52 - exponent)
    ⟨UInt64.ofNat (((exponent + 1023) <<< 52) + fraction)⟩

/-- Decodes exactly those binary64 values that are integral valid array lengths. Both signed zeros
decode to zero; NaN, infinities, fractions, negatives, and `2^32` or larger are rejected. -/
def validArrayLength? (number : JSNumber) : Option Nat :=
  let bits := number.bits.toNat
  let magnitude := bits % (1 <<< 63)
  if magnitude = 0 then some 0
  else if number.sign || number.isNaN || number.isInfinite then none
  else
    let encodedExponent := (bits / (1 <<< 52)) % 2048
    if encodedExponent < 1023 then none
    else
      let exponent := encodedExponent - 1023
      if 32 ≤ exponent then none
      else
        let significand := (1 <<< 52) + bits % (1 <<< 52)
        let divisor := 1 <<< (52 - exponent)
        if significand % divisor != 0 then none
        else
          let length := significand / divisor
          if length ≤ maxArrayLength then some length else none

private def appendArray (heap : Heap) (prototype : Option RefId)
    (elements : Array (Option Value)) : RefId × Heap :=
  let properties := elements.foldl (fun state element =>
    let index := state.1
    let properties := match element with
      | none => state.2
      | some value => state.2.insert (.string (PropertyKey.arrayIndexString index))
          (.data ⟨value, true, true, true⟩)
    (index + 1, properties)) (0, OrderedProps.empty) |>.2
  let ref := ⟨heap.objects.size⟩
  (ref, .mk (heap.objects.push (.mk properties prototype true
    (.array ⟨elements.size, true⟩))) heap.nextFunctionId)

/-- Allocates an array from an indexed collection, validating the prototype and every present object
reference before issuing its stable identity. -/
def allocateArrayFromArray (heap : Heap) (elements : Array (Option Value))
    (prototype : Option RefId := none) : Except DefinePropertyFault (RefId × Heap) :=
  if elements.size > maxArrayLength then .error (.arrayTooLong elements.size)
  else
    match prototype with
    | some ref =>
        match heap.get? ref with
        | .error _ => .error (.heap (.invalidPrototype ref))
        | .ok _ =>
            let invalid := elements.foldl (fun found element =>
              match found, element with
              | some ref, _ => some ref
              | none, some (.object ref) => if ref.value < heap.size then none else some ref
              | none, _ => none) none
            match invalid with
            | some invalidRef => .error (.invalidValueRef invalidRef)
            | none => .ok (appendArray heap prototype elements)
    | none =>
        let invalid := elements.foldl (fun found element =>
          match found, element with
          | some ref, _ => some ref
          | none, some (.object ref) => if ref.value < heap.size then none else some ref
          | none, _ => none) none
        match invalid with
        | some invalidRef => .error (.invalidValueRef invalidRef)
        | none => .ok (appendArray heap prototype elements)

/-- List-input array allocation. Holes are represented by `none`, never by `undefined`. -/
def allocateArray (heap : Heap) (elements : List (Option Value))
    (prototype : Option RefId := none) : Except DefinePropertyFault (RefId × Heap) :=
  heap.allocateArrayFromArray elements.toArray prototype

/-- Reads the exact current length of a valid array object. -/
def arrayLength (heap : Heap) (ref : RefId) : Except HeapFault Nat := do
  let object ← heap.get? ref
  match object.kind with
  | .array slots => pure slots.length
  | actual => throw (.wrongObjectKind ref .array actual.tag)

/-- Allocates a distinct iterator object for an existing array target. -/
def allocateArrayIterator (heap : Heap) (target : RefId)
    (prototype : Option RefId := none) : Except HeapFault (RefId × Heap) := do
  let targetObject ← heap.get? target
  match targetObject.kind with
  | .array _ => pure ()
  | actual => throw (.wrongObjectKind target .array actual.tag)
  match prototype with
  | some ref =>
      match heap.get? ref with
      | .ok _ => pure ()
      | .error _ => throw (.invalidPrototype ref)
  | none => pure ()
  let ref := ⟨heap.objects.size⟩
  pure (ref, .mk (heap.objects.push (.mk OrderedProps.empty prototype true
    (.arrayIterator ⟨target, 0, false⟩))) heap.nextFunctionId)

/-- Advances iterator state against the target's current length. A completed iterator remains done
even if the target later grows. -/
def advanceArrayIterator (heap : Heap) (iterator : RefId) :
    Except HeapFault (Option (RefId × Nat) × Heap) := do
  let object ← heap.get? iterator
  match object.kind with
  | .arrayIterator slots =>
      if slots.done then pure (none, heap)
      else
        let length ← heap.arrayLength slots.target
        if slots.nextIndex < length then
          let nextSlots := { slots with nextIndex := slots.nextIndex + 1 }
          let next ← heap.replace iterator { object with kind := .arrayIterator nextSlots }
          pure (some (slots.target, slots.nextIndex), next)
        else
          let nextSlots := { slots with done := true }
          let next ← heap.replace iterator { object with kind := .arrayIterator nextSlots }
          pure (none, next)
  | actual => throw (.wrongObjectKind iterator .arrayIterator actual.tag)

private def validateValue (heap : Heap) : Value → Except DefinePropertyFault Unit
  | .object ref =>
      match heap.get? ref with
      | .ok _ => .ok ()
      | .error _ => .error (.invalidValueRef ref)
  | .primitive _ => .ok ()

private def validateAccessor (heap : Heap) : Option RefId → Except DefinePropertyFault Unit
  | none => .ok ()
  | some ref =>
      match heap.get? ref with
      | .error _ => .error (.invalidAccessor ref)
      | .ok object =>
          match object.kind with
          | .function _ => .ok ()
          | .ordinary | .array _ | .arrayIterator _ | .primitiveWrapper _ =>
              .error (.nonCallableAccessor ref)

/-- Returns function metadata only for a valid function object. -/
def functionSlots? (heap : Heap) (ref : RefId) : Except HeapFault (Option FunctionSlots) := do
  let object ← heap.get? ref
  match object.kind with
  | .ordinary | .array _ | .arrayIterator _ | .primitiveWrapper _ => pure none
  | .function slots => pure (some slots)

/-- Reports whether a valid reference has the ECMAScript `[[Call]]` internal method. -/
def isCallable (heap : Heap) (ref : RefId) : Except HeapFault Bool := do
  let slots ← heap.functionSlots? ref
  pure slots.isSome

/-- Reports whether a valid reference has a construct operation. -/
def isConstructor (heap : Heap) (ref : RefId) : Except HeapFault Bool := do
  let slots ← heap.functionSlots? ref
  pure (slots.any (·.constructible))

private def validateRef (heap : Heap) (ref : RefId) : Except HeapFault Unit :=
  match heap.get? ref with
  | .ok _ => .ok ()
  | .error fault => .error fault

private def validateOptionalRef (heap : Heap) : Option RefId → Except HeapFault Unit
  | none => .ok ()
  | some ref => validateRef heap ref

/-- Reports whether a value contains no dangling heap reference. -/
def valueValid (heap : Heap) : Value → Bool
  | .object ref => ref.value < heap.size
  | .primitive _ => true

/-- Replacing one object preserves validity of every reference. -/
theorem valueValid_replace (heap next : Heap) (target : RefId) (object : ObjectRecord)
    (replaced : heap.replace target object = .ok next) (value : Value) :
    next.valueValid value = heap.valueValid value := by
  cases value with
  | primitive value => rfl
  | object ref => simp [valueValid, replace_size heap next target object replaced]

private def appendFunction (heap : Heap) (environment : EnvId) (kind : FunctionKind)
    (constructible : Bool) (prototype homeObject : Option RefId)
    (constructorMode : ConstructorMode := .base)
    (lexicalThis : Option Value := none)
    (properties : OrderedProps := OrderedProps.empty) : RefId × Heap :=
  let ref := ⟨heap.objects.size⟩
  let slots : FunctionSlots :=
    ⟨⟨heap.nextFunctionId⟩, environment, kind, constructible, constructorMode, homeObject, lexicalThis⟩
  (ref, .mk (heap.objects.push (.mk properties prototype true (.function slots)))
    (heap.nextFunctionId + 1))

/-- Allocates one validated function object. Environment validity is checked by the machine layer. -/
def allocateFunction (heap : Heap) (environment : EnvId) (kind : FunctionKind)
    (constructible : Bool) (prototype : Option RefId) (homeObject : Option RefId := none)
    (constructorMode : ConstructorMode := .base) (lexicalThis : Option Value := none) :
    Except HeapFault (RefId × Heap) :=
  match validateOptionalRef heap prototype with
  | .error fault => .error fault
  | .ok () =>
      match validateOptionalRef heap homeObject with
      | .error fault => .error fault
      | .ok () =>
          if constructorMode = .derived && (kind != .classConstructor || !constructible) then
            .error .invalidFunctionMetadata
          else
            match lexicalThis with
            | some value =>
                if !heap.valueValid value then
                  match value with
                  | .object ref => .error (.invalidRef ref)
                  | .primitive _ => .error .invalidFunctionMetadata
                else if kind != .arrow then .error .invalidFunctionMetadata
                else if constructible then .error .invalidFunctionMetadata
                else .ok (appendFunction heap environment kind constructible prototype homeObject
                  constructorMode lexicalThis)
            | none =>
                if kind = .arrow then .error .invalidFunctionMetadata
                else if kind = .classConstructor && !constructible then .error .invalidFunctionMetadata
                else .ok (appendFunction heap environment kind constructible prototype homeObject
                  constructorMode)

private def dataProperty (value : Value) (writable enumerable configurable : Bool) :
    PropertyDescriptor := .data ⟨value, writable, enumerable, configurable⟩

/-- Atomically allocates a constructible function and its fresh instance prototype. -/
def allocateConstructorPair (heap : Heap) (environment : EnvId)
    (functionPrototype objectPrototype : Option RefId) (classConstructor : Bool := false)
    (constructorMode : ConstructorMode := .base) :
    Except HeapFault (RefId × RefId × Heap) :=
  match validateOptionalRef heap functionPrototype with
  | .error fault => .error fault
  | .ok () =>
      match validateOptionalRef heap objectPrototype with
      | .error fault => .error fault
      | .ok () =>
          if constructorMode = .derived && !classConstructor then
            .error .invalidFunctionMetadata
          else
          let constructorRef : RefId := ⟨heap.objects.size⟩
          let prototypeRef : RefId := ⟨heap.objects.size + 1⟩
          let constructorProperties := OrderedProps.empty.insert
            (.string (JSString.ofLeanString "prototype"))
            (dataProperty (.object prototypeRef) (!classConstructor) false false)
          let prototypeProperties := OrderedProps.empty.insert
            (.string (JSString.ofLeanString "constructor"))
            (dataProperty (.object constructorRef) true false true)
          let kind := if classConstructor then FunctionKind.classConstructor else FunctionKind.ordinary
          let slots : FunctionSlots :=
            ⟨⟨heap.nextFunctionId⟩, environment, kind, true, constructorMode, none, none⟩
          let objects := heap.objects
            |>.push (.mk constructorProperties functionPrototype true (.function slots))
            |>.push (.mk prototypeProperties objectPrototype true .ordinary)
          .ok (constructorRef, prototypeRef, .mk objects (heap.nextFunctionId + 1))

private def validateDescriptorReferences (heap : Heap) (update : DescriptorUpdate) :
    Except DefinePropertyFault Unit := do
  match update.value with
  | .present value => validateValue heap value
  | .absent => pure ()
  match update.get with
  | .present getter => validateAccessor heap getter
  | .absent => pure ()
  match update.set with
  | .present setter => validateAccessor heap setter
  | .absent => pure ()

private def syntheticLengthDescriptor (slots : ArraySlots) : PropertyDescriptor :=
  .data ⟨.primitive (.number (arrayLengthNumber slots.length)), slots.lengthWritable, false, false⟩

private def wrapperString? (slots : PrimitiveWrapperSlots) : Option JSString :=
  match slots.value with
  | .string value => some value
  | _ => none

private def syntheticWrapperDescriptor? (slots : PrimitiveWrapperSlots) (key : PropertyKey) :
    Option PropertyDescriptor :=
  match slots.value, key with
  | .string value, .string stringKey =>
      if stringKey.equal (JSString.ofLeanString "length") then
        some (.data ⟨.primitive (.number (arrayLengthNumber value.length)), false, false, false⟩)
      else
        match PropertyKey.arrayIndex? stringKey with
        | some index =>
            match value.codeUnits[index]? with
            | some unit => some (.data ⟨.primitive (.string ⟨[unit]⟩), false, true, false⟩)
            | none => none
        | none => none
  | _, _ => none

private def wrapperOwnKeys (object : ObjectRecord) (slots : PrimitiveWrapperSlots) : List PropertyKey :=
  match wrapperString? slots with
  | none => object.properties.ownKeys
  | some value =>
      let stored := object.properties.ownKeys
      let storedIndices := stored.filter fun key => match key with
        | .string stringKey => (PropertyKey.arrayIndex? stringKey).isSome
        | .symbol _ => false
      let rest := stored.filter fun key => match key with
        | .string stringKey => (PropertyKey.arrayIndex? stringKey).isNone
        | .symbol _ => true
      (List.range value.length).map (fun index =>
        .string (PropertyKey.arrayIndexString index)) ++ storedIndices ++ lengthPropertyKey :: rest

/-- Reads an own descriptor, including an array's synthetic `length` property. -/
def getOwnProperty (heap : Heap) (ref : RefId) (key : PropertyKey) :
    Except HeapFault (Option PropertyDescriptor) := do
  let object ← heap.get? ref
  match object.kind with
  | .array slots =>
      if key == lengthPropertyKey then pure (some (syntheticLengthDescriptor slots))
      else pure (object.properties.lookup key)
  | .primitiveWrapper slots =>
      pure ((syntheticWrapperDescriptor? slots key).orElse fun _ => object.properties.lookup key)
  | _ => pure (object.properties.lookup key)

/-- Returns own keys in ECMAScript order, inserting synthetic array `length` after indices and
before all other strings and symbols. -/
def ownPropertyKeys (heap : Heap) (ref : RefId) : Except HeapFault (List PropertyKey) :=
  match heap.get? ref with
  | .error fault => .error fault
  | .ok object =>
      let keys := object.properties.ownKeys
      match object.kind with
      | .array _ =>
          let indices := keys.filter fun key => match key with
            | .string value => (PropertyKey.arrayIndex? value).isSome
            | .symbol _ => false
          let rest := keys.filter fun key => match key with
            | .string value => (PropertyKey.arrayIndex? value).isNone
            | .symbol _ => true
          .ok (indices ++ lengthPropertyKey :: rest)
      | .primitiveWrapper slots => .ok (wrapperOwnKeys object slots)
      | _ => .ok keys

private def ordinaryDefineValidated (heap : Heap) (ref : RefId) (object : ObjectRecord)
    (key : PropertyKey) (update : DescriptorUpdate) (kind : DescriptorKind) :
    Except DefinePropertyFault (Bool × Heap) :=
  match update.applyValidatedDescriptor (object.properties.lookup key) object.extensible kind with
  | .error _ => .ok (false, heap)
  | .ok descriptor =>
      heap.replace ref { object with properties := object.properties.insert key descriptor }
        |>.mapError DefinePropertyFault.heap
        |>.map fun next => (true, next)

private def arrayIndexOfKey? : PropertyKey → Option Nat
  | .string value => PropertyKey.arrayIndex? value
  | .symbol _ => none

private def arrayIndexEntry? (key : PropertyKey) : Option (Nat × PropertyKey) :=
  (arrayIndexOfKey? key).map (·, key)

private def arrayIndexEntries (properties : OrderedProps) : List (Nat × PropertyKey) :=
  properties.ownKeys.filterMap arrayIndexEntry?

private theorem arrayIndexEntries_eq (properties : OrderedProps) :
    arrayIndexEntries properties = properties.arrayIndices.map fun index =>
      (index, .string (PropertyKey.arrayIndexString index)) := by
  unfold arrayIndexEntries OrderedProps.arrayIndices
  induction properties.ownKeys with
  | nil => rfl
  | cons key keys ih =>
      simp only [List.filterMap_cons]
      cases key with
      | symbol symbol => simpa [arrayIndexEntry?, arrayIndexOfKey?] using ih
      | string stringKey =>
          cases parsed : PropertyKey.arrayIndex? stringKey with
          | none => simpa [arrayIndexEntry?, arrayIndexOfKey?, parsed] using ih
          | some index =>
              have canonical := PropertyKey.arrayIndex?_sound parsed
              subst stringKey
              simpa [arrayIndexEntry?, arrayIndexOfKey?, parsed] using ih

private def deleteArrayIndexStep (newLength : Nat)
    (state : Option Nat × OrderedProps) (entry : Nat × PropertyKey) :
    Option Nat × OrderedProps :=
  match state.1 with
  | some _ => state
  | none =>
      let index := entry.1
      let key := entry.2
      if index < newLength then state
      else
        match state.2.lookup key with
        | some (.data descriptor) =>
            if descriptor.configurable then (none, state.2.delete key) else (some index, state.2)
        | some (.accessor descriptor) =>
            if descriptor.configurable then (none, state.2.delete key) else (some index, state.2)
        | none => state

private def deleteArrayIndicesFrom (properties : OrderedProps) (newLength : Nat) :
    Option Nat × OrderedProps :=
  let descending := (arrayIndexEntries properties).reverse
  descending.foldl (deleteArrayIndexStep newLength) (none, properties)

private theorem deleteArrayIndicesFold_wellFormed (entries : List (Nat × PropertyKey))
    (newLength : Nat) (blocked : Option Nat) (properties : OrderedProps)
    (valid : properties.WellFormed) :
    (entries.foldl (deleteArrayIndexStep newLength) (blocked, properties)).2.WellFormed := by
  induction entries generalizing blocked properties with
  | nil => exact valid
  | cons entry entries ih =>
      simp only [List.foldl_cons]
      cases blocked with
      | some blocked => exact ih _ _ valid
      | none =>
          by_cases below : entry.1 < newLength
          · simpa [deleteArrayIndexStep, below] using ih none properties valid
          · cases found : properties.lookup entry.2 with
            | none => simpa [deleteArrayIndexStep, below, found] using ih none properties valid
            | some descriptor =>
                cases descriptor with
                | data descriptor =>
                    cases configurable : descriptor.configurable with
                    | false =>
                        simpa [deleteArrayIndexStep, below, found, configurable] using
                          (ih (some entry.1) properties valid)
                    | true =>
                        simpa [deleteArrayIndexStep, below, found, configurable] using
                          (ih none (properties.delete entry.2)
                            (OrderedProps.delete_wellFormed properties entry.2 valid))
                | accessor descriptor =>
                    cases configurable : descriptor.configurable with
                    | false =>
                        simpa [deleteArrayIndexStep, below, found, configurable] using
                          (ih (some entry.1) properties valid)
                    | true =>
                        simpa [deleteArrayIndexStep, below, found, configurable] using
                          (ih none (properties.delete entry.2)
                            (OrderedProps.delete_wellFormed properties entry.2 valid))

private theorem deleteArrayIndicesFold_descriptors_all (entries : List (Nat × PropertyKey))
    (newLength : Nat) (blocked : Option Nat) (properties : OrderedProps)
    (predicate : PropertyDescriptor → Bool) (valid : properties.WellFormed)
    (current : properties.descriptors.all predicate = true) :
    (entries.foldl (deleteArrayIndexStep newLength)
      (blocked, properties)).2.descriptors.all predicate = true := by
  induction entries generalizing blocked properties with
  | nil => exact current
  | cons entry entries ih =>
      simp only [List.foldl_cons]
      cases blocked with
      | some blocked => exact ih _ _ valid current
      | none =>
          by_cases below : entry.1 < newLength
          · simpa [deleteArrayIndexStep, below] using
              (ih none properties valid current)
          · cases found : properties.lookup entry.2 with
            | none =>
                simpa [deleteArrayIndexStep, below, found] using
                  (ih none properties valid current)
            | some descriptor =>
                cases descriptor with
                | data data =>
                    cases configurable : data.configurable with
                    | false =>
                        simpa [deleteArrayIndexStep, below, found, configurable] using
                          (ih (some entry.1) properties valid current)
                    | true =>
                        have nextValid := OrderedProps.delete_wellFormed properties entry.2 valid
                        have nextCurrent := OrderedProps.descriptors_all_delete properties entry.2
                          predicate valid current
                        simpa [deleteArrayIndexStep, below, found, configurable] using
                          (ih none (properties.delete entry.2) nextValid nextCurrent)
                | accessor accessor =>
                    cases configurable : accessor.configurable with
                    | false =>
                        simpa [deleteArrayIndexStep, below, found, configurable] using
                          (ih (some entry.1) properties valid current)
                    | true =>
                        have nextValid := OrderedProps.delete_wellFormed properties entry.2 valid
                        have nextCurrent := OrderedProps.descriptors_all_delete properties entry.2
                          predicate valid current
                        simpa [deleteArrayIndexStep, below, found, configurable] using
                          (ih none (properties.delete entry.2) nextValid nextCurrent)

private theorem deleteArrayIndicesFold_lookup_ne (entries : List (Nat × PropertyKey))
    (newLength : Nat) (blocked : Option Nat) (properties : OrderedProps) (query : PropertyKey)
    (valid : properties.WellFormed)
    (different : ∀ entry ∈ entries, ¬entry.1 < newLength → entry.2 ≠ query) :
    (entries.foldl (deleteArrayIndexStep newLength) (blocked, properties)).2.lookup query =
      properties.lookup query := by
  induction entries generalizing blocked properties with
  | nil => rfl
  | cons entry entries ih =>
      simp only [List.foldl_cons]
      have tailDifferent : ∀ tail ∈ entries, ¬tail.1 < newLength → tail.2 ≠ query :=
        fun tail tailMember => different tail (by simp [tailMember])
      cases blocked with
      | some blocked => exact ih _ _ valid tailDifferent
      | none =>
          by_cases below : entry.1 < newLength
          · simpa [deleteArrayIndexStep, below] using ih none properties valid tailDifferent
          · cases found : properties.lookup entry.2 with
            | none =>
                simpa [deleteArrayIndexStep, below, found] using
                  ih none properties valid tailDifferent
            | some descriptor =>
                cases descriptor with
                | data descriptor =>
                    cases configurable : descriptor.configurable with
                    | false =>
                        simpa [deleteArrayIndexStep, below, found, configurable] using
                          ih (some entry.1) properties valid tailDifferent
                    | true =>
                        rw [show deleteArrayIndexStep newLength (none, properties) entry =
                          (none, properties.delete entry.2) by
                            simp [deleteArrayIndexStep, below, found, configurable]]
                        rw [ih none (properties.delete entry.2)
                          (OrderedProps.delete_wellFormed properties entry.2 valid) tailDifferent]
                        exact OrderedProps.lookup_delete_ne properties entry.2 query
                          (different entry (by simp) below) valid
                | accessor descriptor =>
                    cases configurable : descriptor.configurable with
                    | false =>
                        simpa [deleteArrayIndexStep, below, found, configurable] using
                          ih (some entry.1) properties valid tailDifferent
                    | true =>
                        rw [show deleteArrayIndexStep newLength (none, properties) entry =
                          (none, properties.delete entry.2) by
                            simp [deleteArrayIndexStep, below, found, configurable]]
                        rw [ih none (properties.delete entry.2)
                          (OrderedProps.delete_wellFormed properties entry.2 valid) tailDifferent]
                        exact OrderedProps.lookup_delete_ne properties entry.2 query
                          (different entry (by simp) below) valid

private theorem deleteArrayIndicesFold_lookup_some (entries : List (Nat × PropertyKey))
    (newLength : Nat) (blocked : Option Nat) (properties : OrderedProps)
    (valid : properties.WellFormed) (query : PropertyKey) (descriptor : PropertyDescriptor)
    (found : (entries.foldl (deleteArrayIndexStep newLength)
      (blocked, properties)).2.lookup query = some descriptor) :
    properties.lookup query = some descriptor := by
  induction entries generalizing blocked properties with
  | nil => exact found
  | cons entry entries ih =>
      simp only [List.foldl_cons] at found
      cases blocked with
      | some blocked => exact ih _ _ valid found
      | none =>
          by_cases below : entry.1 < newLength
          · exact ih none properties valid (by
              simpa [deleteArrayIndexStep, below] using found)
          · cases entryFound : properties.lookup entry.2 with
            | none => exact ih none properties valid (by
                simpa [deleteArrayIndexStep, below, entryFound] using found)
            | some entryDescriptor =>
                cases entryDescriptor with
                | data data =>
                    cases configurable : data.configurable with
                    | false => exact ih (some entry.1) properties valid (by
                        simpa [deleteArrayIndexStep, below, entryFound, configurable] using found)
                    | true =>
                        have recursive := ih none (properties.delete entry.2)
                          (OrderedProps.delete_wellFormed properties entry.2 valid) (by
                            simpa [deleteArrayIndexStep, below, entryFound, configurable] using found)
                        by_cases equal : entry.2 = query
                        · subst query
                          rw [OrderedProps.lookup_delete_same properties entry.2 valid] at recursive
                          contradiction
                        · rwa [OrderedProps.lookup_delete_ne properties entry.2 query equal valid] at recursive
                | accessor accessor =>
                    cases configurable : accessor.configurable with
                    | false => exact ih (some entry.1) properties valid (by
                        simpa [deleteArrayIndexStep, below, entryFound, configurable] using found)
                    | true =>
                        have recursive := ih none (properties.delete entry.2)
                          (OrderedProps.delete_wellFormed properties entry.2 valid) (by
                            simpa [deleteArrayIndexStep, below, entryFound, configurable] using found)
                        by_cases equal : entry.2 = query
                        · subst query
                          rw [OrderedProps.lookup_delete_same properties entry.2 valid] at recursive
                          contradiction
                        · rwa [OrderedProps.lookup_delete_ne properties entry.2 query equal valid] at recursive
private theorem arrayIndexEntry?_parsed {key : PropertyKey} {entry : Nat × PropertyKey}
    (mapped : arrayIndexEntry? key = some entry) :
    arrayIndexOfKey? entry.2 = some entry.1 := by
  unfold arrayIndexEntry? at mapped
  cases parsed : arrayIndexOfKey? key with
  | none => simp [parsed] at mapped
  | some index =>
      simp [parsed] at mapped
      cases mapped
      exact parsed

private theorem deleteArrayIndicesFrom_lookup_below (properties : OrderedProps) (newLength : Nat)
    (query : PropertyKey) (index : Nat) (valid : properties.WellFormed)
    (parsed : arrayIndexOfKey? query = some index) (below : index < newLength) :
    (deleteArrayIndicesFrom properties newLength).2.lookup query = properties.lookup query := by
  apply deleteArrayIndicesFold_lookup_ne _ newLength none properties query valid
  intro entry member notBelow equal
  subst query
  rw [List.mem_reverse] at member
  change entry ∈ properties.ownKeys.filterMap arrayIndexEntry? at member
  rw [List.mem_filterMap] at member
  rcases member with ⟨key, keyMember, mapped⟩
  have entryParsed := arrayIndexEntry?_parsed mapped
  rw [parsed] at entryParsed
  have indicesEqual := Option.some.inj entryParsed
  subst index
  exact notBelow below

private theorem deleteArrayIndicesFold_stopped (entries : List (Nat × PropertyKey))
    (newLength blocked : Nat) (properties : OrderedProps) :
    entries.foldl (deleteArrayIndexStep newLength) (some blocked, properties) =
      (some blocked, properties) := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      simpa [deleteArrayIndexStep] using ih

private theorem deleteArrayIndicesFold_blocked (indices : List Nat) (newLength blocked : Nat)
    (properties next : OrderedProps) (valid : properties.WellFormed)
    (nodup : indices.Nodup)
    (parsed : ∀ index ∈ indices,
      PropertyKey.arrayIndex? (PropertyKey.arrayIndexString index) = some index)
    (present : ∀ index ∈ indices,
      (properties.lookup (.string (PropertyKey.arrayIndexString index))).isSome)
    (result : (indices.map fun index =>
      (index, .string (PropertyKey.arrayIndexString index))).foldl
        (deleteArrayIndexStep newLength) (none, properties) = (some blocked, next)) :
    newLength ≤ blocked ∧ blocked ∈ indices ∧
      ∃ descriptor,
        properties.lookup (.string (PropertyKey.arrayIndexString blocked)) = some descriptor ∧
        match descriptor with
        | .data data => data.configurable = false
        | .accessor accessor => accessor.configurable = false := by
  induction indices generalizing properties with
  | nil => simp at result
  | cons index indices ih =>
      have nodupParts := List.nodup_cons.mp nodup
      have tailParsed : ∀ candidate ∈ indices,
          PropertyKey.arrayIndex? (PropertyKey.arrayIndexString candidate) = some candidate :=
        fun candidate member => parsed candidate (by simp [member])
      have tailPresent : ∀ candidate ∈ indices,
          (properties.lookup (.string (PropertyKey.arrayIndexString candidate))).isSome :=
        fun candidate member => present candidate (by simp [member])
      simp only [List.map_cons, List.foldl_cons] at result
      by_cases below : index < newLength
      · have recursive := ih properties valid nodupParts.2 tailParsed tailPresent (by
          simpa [deleteArrayIndexStep, below] using result)
        exact ⟨recursive.1, by simp [recursive.2.1], recursive.2.2⟩
      · let key : PropertyKey := .string (PropertyKey.arrayIndexString index)
        have headPresent := present index (by simp)
        cases found : properties.lookup key with
        | none => simp [key, found] at headPresent
        | some descriptor =>
            cases descriptor with
            | data descriptor =>
                cases configurable : descriptor.configurable with
                | false =>
                    have stopped := deleteArrayIndicesFold_stopped
                      (indices.map fun candidate =>
                        (candidate, .string (PropertyKey.arrayIndexString candidate)))
                      newLength index properties
                    simp [deleteArrayIndexStep, below, key, found, configurable, stopped] at result
                    obtain ⟨rfl, rfl⟩ := result
                    exact ⟨by omega, by simp, ⟨.data descriptor, found, configurable⟩⟩
                | true =>
                    have nextValid := OrderedProps.delete_wellFormed properties key valid
                    have nextPresent : ∀ candidate ∈ indices,
                        ((properties.delete key).lookup
                          (.string (PropertyKey.arrayIndexString candidate))).isSome := by
                      intro candidate member
                      have indicesNe : index ≠ candidate := fun equal =>
                        nodupParts.1 (by simpa [equal] using member)
                      have keysNe : key ≠ .string (PropertyKey.arrayIndexString candidate) := by
                        intro equal
                        have stringEqual := PropertyKey.string.inj equal
                        have parsedHead := parsed index (by simp)
                        have parsedTail := tailParsed candidate member
                        rw [stringEqual] at parsedHead
                        exact indicesNe (Option.some.inj (parsedHead.symm.trans parsedTail))
                      rw [OrderedProps.lookup_delete_ne properties key _ keysNe valid]
                      exact tailPresent candidate member
                    have recursive := ih (properties.delete key) nextValid nodupParts.2 tailParsed
                      nextPresent (by
                        simpa [deleteArrayIndexStep, below, key, found, configurable] using result)
                    rcases recursive with ⟨blockedBound, blockedMember, descriptorFound⟩
                    refine ⟨blockedBound, by simp [blockedMember], ?_⟩
                    rcases descriptorFound with ⟨blockedDescriptor, blockedFound, blockedFixed⟩
                    have indicesNe : index ≠ blocked := fun equal =>
                      nodupParts.1 (by simpa [equal] using blockedMember)
                    have keysNe : key ≠ .string (PropertyKey.arrayIndexString blocked) := by
                      intro equal
                      have stringEqual := PropertyKey.string.inj equal
                      have parsedHead := parsed index (by simp)
                      have parsedBlocked := tailParsed blocked blockedMember
                      rw [stringEqual] at parsedHead
                      exact indicesNe (Option.some.inj (parsedHead.symm.trans parsedBlocked))
                    rw [OrderedProps.lookup_delete_ne properties key _ keysNe valid] at blockedFound
                    exact ⟨blockedDescriptor, blockedFound, blockedFixed⟩

            | accessor descriptor =>
                cases configurable : descriptor.configurable with
                | false =>
                    have stopped := deleteArrayIndicesFold_stopped
                      (indices.map fun candidate =>
                        (candidate, .string (PropertyKey.arrayIndexString candidate)))
                      newLength index properties
                    simp [deleteArrayIndexStep, below, key, found, configurable, stopped] at result
                    obtain ⟨rfl, rfl⟩ := result
                    exact ⟨by omega, by simp, ⟨.accessor descriptor, found, configurable⟩⟩
                | true =>
                    have nextValid := OrderedProps.delete_wellFormed properties key valid
                    have nextPresent : ∀ candidate ∈ indices,
                        ((properties.delete key).lookup
                          (.string (PropertyKey.arrayIndexString candidate))).isSome := by
                      intro candidate member
                      have indicesNe : index ≠ candidate := fun equal =>
                        nodupParts.1 (by simpa [equal] using member)
                      have keysNe : key ≠ .string (PropertyKey.arrayIndexString candidate) := by
                        intro equal
                        have stringEqual := PropertyKey.string.inj equal
                        have parsedHead := parsed index (by simp)
                        have parsedTail := tailParsed candidate member
                        rw [stringEqual] at parsedHead
                        exact indicesNe (Option.some.inj (parsedHead.symm.trans parsedTail))
                      rw [OrderedProps.lookup_delete_ne properties key _ keysNe valid]
                      exact tailPresent candidate member
                    have recursive := ih (properties.delete key) nextValid nodupParts.2 tailParsed
                      nextPresent (by
                        simpa [deleteArrayIndexStep, below, key, found, configurable] using result)
                    rcases recursive with ⟨blockedBound, blockedMember, descriptorFound⟩
                    refine ⟨blockedBound, by simp [blockedMember], ?_⟩
                    rcases descriptorFound with ⟨blockedDescriptor, blockedFound, blockedFixed⟩
                    have indicesNe : index ≠ blocked := fun equal =>
                      nodupParts.1 (by simpa [equal] using blockedMember)
                    have keysNe : key ≠ .string (PropertyKey.arrayIndexString blocked) := by
                      intro equal
                      have stringEqual := PropertyKey.string.inj equal
                      have parsedHead := parsed index (by simp)
                      have parsedBlocked := tailParsed blocked blockedMember
                      rw [stringEqual] at parsedHead
                      exact indicesNe (Option.some.inj (parsedHead.symm.trans parsedBlocked))
                    rw [OrderedProps.lookup_delete_ne properties key _ keysNe valid] at blockedFound
                    exact ⟨blockedDescriptor, blockedFound, blockedFixed⟩

private theorem arrayIndices_canonical_parse (properties : OrderedProps) (index : Nat)
    (member : index ∈ properties.arrayIndices) :
    PropertyKey.arrayIndex? (PropertyKey.arrayIndexString index) = some index := by
  unfold OrderedProps.arrayIndices at member
  rcases List.mem_filterMap.mp member with ⟨key, keyMember, keyParsed⟩
  cases key with
  | symbol symbol => simp at keyParsed
  | string stringKey =>
      rw [← PropertyKey.arrayIndex?_sound keyParsed]
      exact keyParsed

private theorem arrayIndices_lookup_present (properties : OrderedProps) (index : Nat)
    (valid : properties.WellFormed) (member : index ∈ properties.arrayIndices) :
    (properties.lookup (.string (PropertyKey.arrayIndexString index))).isSome := by
  unfold OrderedProps.arrayIndices at member
  rcases List.mem_filterMap.mp member with ⟨key, keyMember, keyParsed⟩
  cases key with
  | symbol symbol => simp at keyParsed
  | string stringKey =>
      have canonical := PropertyKey.arrayIndex?_sound keyParsed
      subst stringKey
      exact (OrderedProps.mem_ownKeys_iff_lookup_isSome properties _ valid).mp keyMember

private theorem deleteArrayIndicesFrom_blocked (properties next : OrderedProps)
    (newLength blocked : Nat) (valid : properties.WellFormed)
    (result : deleteArrayIndicesFrom properties newLength = (some blocked, next)) :
    newLength ≤ blocked ∧
      PropertyKey.arrayIndex? (PropertyKey.arrayIndexString blocked) = some blocked ∧
      ∃ descriptor,
        properties.lookup (.string (PropertyKey.arrayIndexString blocked)) = some descriptor ∧
        match descriptor with
        | .data data => data.configurable = false
        | .accessor accessor => accessor.configurable = false := by
  have characterized := deleteArrayIndicesFold_blocked properties.arrayIndices.reverse
    newLength blocked properties next valid
    ((List.reverse_perm properties.arrayIndices).nodup_iff.mpr
      (OrderedProps.arrayIndices_nodup properties valid))
    (fun index member => arrayIndices_canonical_parse properties index
      (List.mem_reverse.mp member))
    (fun index member => arrayIndices_lookup_present properties index valid
      (List.mem_reverse.mp member)) (by
        unfold deleteArrayIndicesFrom at result
        rw [arrayIndexEntries_eq] at result
        simpa only [List.map_reverse] using result)
  exact ⟨characterized.1,
    arrayIndices_canonical_parse properties blocked (List.mem_reverse.mp characterized.2.1),
    characterized.2.2⟩

private theorem deleteArrayIndicesFrom_lookup_nonIndex (properties : OrderedProps)
    (newLength : Nat) (query : PropertyKey) (valid : properties.WellFormed)
    (nonIndex : arrayIndexOfKey? query = none) :
    (deleteArrayIndicesFrom properties newLength).2.lookup query = properties.lookup query := by
  apply deleteArrayIndicesFold_lookup_ne _ newLength none properties query valid
  intro entry member notBelow equal
  subst query
  rw [List.mem_reverse] at member
  change entry ∈ properties.ownKeys.filterMap arrayIndexEntry? at member
  rw [List.mem_filterMap] at member
  rcases member with ⟨key, keyMember, mapped⟩
  have entryParsed := arrayIndexEntry?_parsed mapped
  rw [nonIndex] at entryParsed
  contradiction

private theorem orderedKeys_delete_index (properties : OrderedProps) (key : PropertyKey)
    (index : Nat) (valid : properties.WellFormed) (parsed : arrayIndexOfKey? key = some index) :
    (properties.delete key).stringKeys = properties.stringKeys ∧
      (properties.delete key).symbolKeys = properties.symbolKeys := by
  have ordered := OrderedProps.orderedKeys_delete properties key valid
  have stringAbsent : key ∉ properties.stringKeys := by
    intro member
    unfold OrderedProps.stringKeys at member
    rcases List.mem_filter.mp member with ⟨keyMember, classification⟩
    cases key with
    | symbol symbol => simp at classification
    | string stringKey =>
        change PropertyKey.arrayIndex? stringKey = some index at parsed
        change (PropertyKey.arrayIndex? stringKey).isNone = true at classification
        rw [parsed] at classification
        contradiction
  have symbolAbsent : key ∉ properties.symbolKeys := by
    intro member
    unfold OrderedProps.symbolKeys at member
    rcases List.mem_filter.mp member with ⟨keyMember, classification⟩
    cases key with
    | string stringKey => simp at classification
    | symbol symbol => simp [arrayIndexOfKey?] at parsed
  simpa [List.erase_eq_self_iff.mpr stringAbsent,
    List.erase_eq_self_iff.mpr symbolAbsent] using ordered

private theorem deleteArrayIndicesFold_order (entries : List (Nat × PropertyKey))
    (newLength : Nat) (blocked : Option Nat) (properties : OrderedProps)
    (valid : properties.WellFormed)
    (parsed : ∀ entry ∈ entries, arrayIndexOfKey? entry.2 = some entry.1) :
    let next := (entries.foldl (deleteArrayIndexStep newLength) (blocked, properties)).2
    next.stringKeys = properties.stringKeys ∧ next.symbolKeys = properties.symbolKeys := by
  induction entries generalizing blocked properties with
  | nil => exact ⟨rfl, rfl⟩
  | cons entry entries ih =>
      simp only [List.foldl_cons]
      have tailParsed : ∀ tail ∈ entries, arrayIndexOfKey? tail.2 = some tail.1 :=
        fun tail member => parsed tail (by simp [member])
      cases blocked with
      | some blocked => exact ih _ _ valid tailParsed
      | none =>
          by_cases below : entry.1 < newLength
          · simpa [deleteArrayIndexStep, below] using ih none properties valid tailParsed
          · cases found : properties.lookup entry.2 with
            | none =>
                simpa [deleteArrayIndexStep, below, found] using
                  ih none properties valid tailParsed
            | some descriptor =>
                cases descriptor with
                | data descriptor =>
                    cases configurable : descriptor.configurable with
                    | false =>
                        simpa [deleteArrayIndexStep, below, found, configurable] using
                          ih (some entry.1) properties valid tailParsed
                    | true =>
                        have deletedOrder := orderedKeys_delete_index properties entry.2 entry.1 valid
                          (parsed entry (by simp))
                        have recursive := ih none (properties.delete entry.2)
                          (OrderedProps.delete_wellFormed properties entry.2 valid) tailParsed
                        simpa [deleteArrayIndexStep, below, found, configurable,
                          deletedOrder.1, deletedOrder.2] using recursive
                | accessor descriptor =>
                    cases configurable : descriptor.configurable with
                    | false =>
                        simpa [deleteArrayIndexStep, below, found, configurable] using
                          ih (some entry.1) properties valid tailParsed
                    | true =>
                        have deletedOrder := orderedKeys_delete_index properties entry.2 entry.1 valid
                          (parsed entry (by simp))
                        have recursive := ih none (properties.delete entry.2)
                          (OrderedProps.delete_wellFormed properties entry.2 valid) tailParsed
                        simpa [deleteArrayIndexStep, below, found, configurable,
                          deletedOrder.1, deletedOrder.2] using recursive

private theorem deleteArrayIndicesFrom_order (properties : OrderedProps) (newLength : Nat)
    (valid : properties.WellFormed) :
    let next := (deleteArrayIndicesFrom properties newLength).2
    next.stringKeys = properties.stringKeys ∧ next.symbolKeys = properties.symbolKeys := by
  apply deleteArrayIndicesFold_order _ newLength none properties valid
  intro entry member
  rw [List.mem_reverse] at member
  change entry ∈ properties.ownKeys.filterMap arrayIndexEntry? at member
  rw [List.mem_filterMap] at member
  rcases member with ⟨key, keyMember, mapped⟩
  exact arrayIndexEntry?_parsed mapped

private theorem deleteArrayIndicesFold_unblocked (indices : List Nat) (newLength : Nat)
    (properties next : OrderedProps) (valid : properties.WellFormed)
    (nodup : indices.Nodup)
    (parsed : ∀ index ∈ indices,
      PropertyKey.arrayIndex? (PropertyKey.arrayIndexString index) = some index)
    (present : ∀ index ∈ indices,
      (properties.lookup (.string (PropertyKey.arrayIndexString index))).isSome)
    (result : (indices.map fun index =>
      (index, .string (PropertyKey.arrayIndexString index))).foldl
        (deleteArrayIndexStep newLength) (none, properties) = (none, next)) :
    ∀ index ∈ indices, newLength ≤ index →
      ∃ descriptor,
        properties.lookup (.string (PropertyKey.arrayIndexString index)) = some descriptor ∧
        (match descriptor with
          | .data data => data.configurable = true
          | .accessor accessor => accessor.configurable = true) ∧
        next.lookup (.string (PropertyKey.arrayIndexString index)) = none := by
  induction indices generalizing properties with
  | nil => simp
  | cons head indices ih =>
      have nodupParts := List.nodup_cons.mp nodup
      have tailParsed : ∀ candidate ∈ indices,
          PropertyKey.arrayIndex? (PropertyKey.arrayIndexString candidate) = some candidate :=
        fun candidate member => parsed candidate (by simp [member])
      have tailPresent : ∀ candidate ∈ indices,
          (properties.lookup (.string (PropertyKey.arrayIndexString candidate))).isSome :=
        fun candidate member => present candidate (by simp [member])
      simp only [List.map_cons, List.foldl_cons] at result
      by_cases below : head < newLength
      · have recursive := ih properties valid nodupParts.2 tailParsed tailPresent (by
          simpa [deleteArrayIndexStep, below] using result)
        intro index member atLeast
        rcases List.mem_cons.mp member with equal | tailMember
        · subst index
          omega
        · exact recursive index tailMember atLeast
      · let key : PropertyKey := .string (PropertyKey.arrayIndexString head)
        have headPresent := present head (by simp)
        cases found : properties.lookup key with
        | none => simp [key, found] at headPresent
        | some descriptor =>
            cases descriptor with
            | data descriptor =>
                cases configurable : descriptor.configurable with
                | false =>
                    have stopped := deleteArrayIndicesFold_stopped
                      (indices.map fun candidate =>
                        (candidate, .string (PropertyKey.arrayIndexString candidate)))
                      newLength head properties
                    simp [deleteArrayIndexStep, below, key, found, configurable, stopped] at result
                | true =>
                    have nextValid := OrderedProps.delete_wellFormed properties key valid
                    have nextPresent : ∀ candidate ∈ indices,
                        ((properties.delete key).lookup
                          (.string (PropertyKey.arrayIndexString candidate))).isSome := by
                      intro candidate member
                      have indicesNe : head ≠ candidate := fun equal =>
                        nodupParts.1 (by simpa [equal] using member)
                      have keysNe : key ≠ .string (PropertyKey.arrayIndexString candidate) := by
                        intro equal
                        have stringEqual := PropertyKey.string.inj equal
                        have parsedHead := parsed head (by simp)
                        have parsedTail := tailParsed candidate member
                        rw [stringEqual] at parsedHead
                        exact indicesNe (Option.some.inj (parsedHead.symm.trans parsedTail))
                      rw [OrderedProps.lookup_delete_ne properties key _ keysNe valid]
                      exact tailPresent candidate member
                    have recursiveResult :
                        (indices.map fun candidate =>
                          (candidate, .string (PropertyKey.arrayIndexString candidate))).foldl
                            (deleteArrayIndexStep newLength) (none, properties.delete key) =
                              (none, next) := by
                      simpa [deleteArrayIndexStep, below, key, found, configurable] using result
                    have recursive := ih (properties.delete key) nextValid nodupParts.2 tailParsed
                      nextPresent recursiveResult
                    intro index member atLeast
                    rcases List.mem_cons.mp member with equal | tailMember
                    · subst index
                      refine ⟨.data descriptor, found, configurable, ?_⟩
                      have preserved := deleteArrayIndicesFold_lookup_ne
                        (indices.map fun candidate =>
                          (candidate, .string (PropertyKey.arrayIndexString candidate)))
                        newLength none (properties.delete key) key nextValid (by
                          intro entry entryMember active equal
                          rcases List.mem_map.mp entryMember with ⟨candidate, candidateMember, pairEqual⟩
                          cases pairEqual
                          have indicesNe : head ≠ candidate := fun indicesEqual =>
                            nodupParts.1 (by simpa [indicesEqual] using candidateMember)
                          apply indicesNe
                          have stringEqual := PropertyKey.string.inj equal.symm
                          have parsedHead := parsed head (by simp)
                          have parsedTail := tailParsed candidate candidateMember
                          rw [stringEqual] at parsedHead
                          exact Option.some.inj (parsedHead.symm.trans parsedTail))
                      rw [recursiveResult] at preserved
                      simpa [OrderedProps.lookup_delete_same properties key valid] using preserved
                    · rcases recursive index tailMember atLeast with
                        ⟨oldDescriptor, oldFound, oldConfigurable, finalAbsent⟩
                      have keysNe : key ≠ .string (PropertyKey.arrayIndexString index) := by
                        intro equal
                        have stringEqual := PropertyKey.string.inj equal
                        have parsedHead := parsed head (by simp)
                        have parsedTail := tailParsed index tailMember
                        rw [stringEqual] at parsedHead
                        exact nodupParts.1 (by
                          have := Option.some.inj (parsedHead.symm.trans parsedTail)
                          simpa [this] using tailMember)
                      rw [OrderedProps.lookup_delete_ne properties key _ keysNe valid] at oldFound
                      exact ⟨oldDescriptor, oldFound, oldConfigurable, finalAbsent⟩

            | accessor descriptor =>
                cases configurable : descriptor.configurable with
                | false =>
                    have stopped := deleteArrayIndicesFold_stopped
                      (indices.map fun candidate =>
                        (candidate, .string (PropertyKey.arrayIndexString candidate)))
                      newLength head properties
                    simp [deleteArrayIndexStep, below, key, found, configurable, stopped] at result
                | true =>
                    have nextValid := OrderedProps.delete_wellFormed properties key valid
                    have nextPresent : ∀ candidate ∈ indices,
                        ((properties.delete key).lookup
                          (.string (PropertyKey.arrayIndexString candidate))).isSome := by
                      intro candidate member
                      have indicesNe : head ≠ candidate := fun equal =>
                        nodupParts.1 (by simpa [equal] using member)
                      have keysNe : key ≠ .string (PropertyKey.arrayIndexString candidate) := by
                        intro equal
                        have stringEqual := PropertyKey.string.inj equal
                        have parsedHead := parsed head (by simp)
                        have parsedTail := tailParsed candidate member
                        rw [stringEqual] at parsedHead
                        exact indicesNe (Option.some.inj (parsedHead.symm.trans parsedTail))
                      rw [OrderedProps.lookup_delete_ne properties key _ keysNe valid]
                      exact tailPresent candidate member
                    have recursiveResult :
                        (indices.map fun candidate =>
                          (candidate, .string (PropertyKey.arrayIndexString candidate))).foldl
                            (deleteArrayIndexStep newLength) (none, properties.delete key) =
                              (none, next) := by
                      simpa [deleteArrayIndexStep, below, key, found, configurable] using result
                    have recursive := ih (properties.delete key) nextValid nodupParts.2 tailParsed
                      nextPresent recursiveResult
                    intro index member atLeast
                    rcases List.mem_cons.mp member with equal | tailMember
                    · subst index
                      refine ⟨.accessor descriptor, found, configurable, ?_⟩
                      have preserved := deleteArrayIndicesFold_lookup_ne
                        (indices.map fun candidate =>
                          (candidate, .string (PropertyKey.arrayIndexString candidate)))
                        newLength none (properties.delete key) key nextValid (by
                          intro entry entryMember active equal
                          rcases List.mem_map.mp entryMember with ⟨candidate, candidateMember, pairEqual⟩
                          cases pairEqual
                          have indicesNe : head ≠ candidate := fun indicesEqual =>
                            nodupParts.1 (by simpa [indicesEqual] using candidateMember)
                          apply indicesNe
                          have stringEqual := PropertyKey.string.inj equal.symm
                          have parsedHead := parsed head (by simp)
                          have parsedTail := tailParsed candidate candidateMember
                          rw [stringEqual] at parsedHead
                          exact Option.some.inj (parsedHead.symm.trans parsedTail))
                      rw [recursiveResult] at preserved
                      simpa [OrderedProps.lookup_delete_same properties key valid] using preserved
                    · rcases recursive index tailMember atLeast with
                        ⟨oldDescriptor, oldFound, oldConfigurable, finalAbsent⟩
                      have keysNe : key ≠ .string (PropertyKey.arrayIndexString index) := by
                        intro equal
                        have stringEqual := PropertyKey.string.inj equal
                        have parsedHead := parsed head (by simp)
                        have parsedTail := tailParsed index tailMember
                        rw [stringEqual] at parsedHead
                        exact nodupParts.1 (by
                          have := Option.some.inj (parsedHead.symm.trans parsedTail)
                          simpa [this] using tailMember)
                      rw [OrderedProps.lookup_delete_ne properties key _ keysNe valid] at oldFound
                      exact ⟨oldDescriptor, oldFound, oldConfigurable, finalAbsent⟩

private theorem deleteArrayIndicesFrom_unblocked (properties next : OrderedProps)
    (newLength : Nat) (valid : properties.WellFormed)
    (result : deleteArrayIndicesFrom properties newLength = (none, next)) :
    ∀ key index descriptor,
      arrayIndexOfKey? key = some index →
      properties.lookup key = some descriptor → newLength ≤ index →
      (match descriptor with
        | .data data => data.configurable = true
        | .accessor accessor => accessor.configurable = true) ∧
      next.lookup key = none := by
  have sweep := deleteArrayIndicesFold_unblocked properties.arrayIndices.reverse newLength
    properties next valid
    ((List.reverse_perm properties.arrayIndices).nodup_iff.mpr
      (OrderedProps.arrayIndices_nodup properties valid))
    (fun index member => arrayIndices_canonical_parse properties index
      (List.mem_reverse.mp member))
    (fun index member => arrayIndices_lookup_present properties index valid
      (List.mem_reverse.mp member)) (by
        unfold deleteArrayIndicesFrom at result
        rw [arrayIndexEntries_eq] at result
        simpa only [List.map_reverse] using result)
  intro key index descriptor parsed found atLeast
  cases key with
  | symbol symbol => simp [arrayIndexOfKey?] at parsed
  | string stringKey =>
      have canonical := PropertyKey.arrayIndex?_sound parsed
      subst stringKey
      have keyMember := (OrderedProps.mem_ownKeys_iff_lookup_isSome properties _ valid).mpr (by
        rw [found]
        rfl)
      have indexMember : index ∈ properties.arrayIndices := by
        unfold OrderedProps.arrayIndices
        apply List.mem_filterMap.mpr
        exact ⟨.string (PropertyKey.arrayIndexString index), keyMember, parsed⟩
      rcases sweep index (List.mem_reverse.mpr indexMember) atLeast with
        ⟨observed, observedFound, configurable, absent⟩
      rw [found] at observedFound
      cases observedFound
      exact ⟨configurable, absent⟩

private theorem deleteArrayIndicesFold_blocked_split (indices : List Nat) (newLength blocked : Nat)
    (properties next : OrderedProps) (valid : properties.WellFormed)
    (nodup : indices.Nodup)
    (parsed : ∀ index ∈ indices,
      PropertyKey.arrayIndex? (PropertyKey.arrayIndexString index) = some index)
    (present : ∀ index ∈ indices,
      (properties.lookup (.string (PropertyKey.arrayIndexString index))).isSome)
    (result : (indices.map fun index =>
      (index, .string (PropertyKey.arrayIndexString index))).foldl
        (deleteArrayIndexStep newLength) (none, properties) = (some blocked, next)) :
    ∃ before after current descriptor,
      indices = before ++ blocked :: after ∧
      (before.map fun index =>
        (index, .string (PropertyKey.arrayIndexString index))).foldl
          (deleteArrayIndexStep newLength) (none, properties) = (none, current) ∧
      current.lookup (.string (PropertyKey.arrayIndexString blocked)) = some descriptor ∧
      (match descriptor with
        | .data data => data.configurable = false
        | .accessor accessor => accessor.configurable = false) ∧ next = current := by
  induction indices generalizing properties with
  | nil => simp at result
  | cons index indices ih =>
      have nodupParts := List.nodup_cons.mp nodup
      have tailParsed : ∀ candidate ∈ indices,
          PropertyKey.arrayIndex? (PropertyKey.arrayIndexString candidate) = some candidate :=
        fun candidate member => parsed candidate (by simp [member])
      have tailPresent : ∀ candidate ∈ indices,
          (properties.lookup (.string (PropertyKey.arrayIndexString candidate))).isSome :=
        fun candidate member => present candidate (by simp [member])
      simp only [List.map_cons, List.foldl_cons] at result
      by_cases below : index < newLength
      · rcases ih properties valid nodupParts.2 tailParsed tailPresent (by
          simpa [deleteArrayIndexStep, below] using result) with
          ⟨before, after, current, descriptor, split, swept, found, fixed, final⟩
        exact ⟨index :: before, after, current, descriptor, by simp [split], by
          simpa [deleteArrayIndexStep, below] using swept, found, fixed, final⟩
      · let key : PropertyKey := .string (PropertyKey.arrayIndexString index)
        have headPresent := present index (by simp)
        cases found : properties.lookup key with
        | none => simp [key, found] at headPresent
        | some descriptor =>
            cases descriptor with
            | data descriptor =>
                cases configurable : descriptor.configurable with
                | false =>
                    have stopped := deleteArrayIndicesFold_stopped
                      (indices.map fun candidate =>
                        (candidate, .string (PropertyKey.arrayIndexString candidate)))
                      newLength index properties
                    simp [deleteArrayIndexStep, below, key, found, configurable, stopped] at result
                    obtain ⟨rfl, rfl⟩ := result
                    exact ⟨[], indices, properties, .data descriptor, rfl, rfl, found,
                      configurable, rfl⟩
                | true =>
                    have deletedValid := OrderedProps.delete_wellFormed properties key valid
                    have deletedPresent : ∀ candidate ∈ indices,
                        ((properties.delete key).lookup
                          (.string (PropertyKey.arrayIndexString candidate))).isSome := by
                      intro candidate member
                      by_cases equal : key = .string (PropertyKey.arrayIndexString candidate)
                      · have stringEqual := PropertyKey.string.inj equal
                        have parsedHead := parsed index (by simp)
                        have parsedTail := tailParsed candidate member
                        rw [stringEqual] at parsedHead
                        exact False.elim (nodupParts.1 (by
                          have := Option.some.inj (parsedHead.symm.trans parsedTail)
                          simpa [this] using member))
                      · rw [OrderedProps.lookup_delete_ne properties key _ equal valid]
                        exact tailPresent candidate member
                    rcases ih (properties.delete key) deletedValid nodupParts.2 tailParsed deletedPresent (by
                      simpa [deleteArrayIndexStep, below, key, found, configurable] using result) with
                      ⟨before, after, current, blockedDescriptor, split, swept, blockedFound,
                        blockedFixed, final⟩
                    exact ⟨index :: before, after, current, blockedDescriptor, by simp [split], by
                      simpa [deleteArrayIndexStep, below, key, found, configurable] using swept,
                      blockedFound, blockedFixed, final⟩
            | accessor descriptor =>
                cases configurable : descriptor.configurable with
                | false =>
                    have stopped := deleteArrayIndicesFold_stopped
                      (indices.map fun candidate =>
                        (candidate, .string (PropertyKey.arrayIndexString candidate)))
                      newLength index properties
                    simp [deleteArrayIndexStep, below, key, found, configurable, stopped] at result
                    obtain ⟨rfl, rfl⟩ := result
                    exact ⟨[], indices, properties, .accessor descriptor, rfl, rfl, found,
                      configurable, rfl⟩
                | true =>
                    have deletedValid := OrderedProps.delete_wellFormed properties key valid
                    have deletedPresent : ∀ candidate ∈ indices,
                        ((properties.delete key).lookup
                          (.string (PropertyKey.arrayIndexString candidate))).isSome := by
                      intro candidate member
                      by_cases equal : key = .string (PropertyKey.arrayIndexString candidate)
                      · have stringEqual := PropertyKey.string.inj equal
                        have parsedHead := parsed index (by simp)
                        have parsedTail := tailParsed candidate member
                        rw [stringEqual] at parsedHead
                        exact False.elim (nodupParts.1 (by
                          have := Option.some.inj (parsedHead.symm.trans parsedTail)
                          simpa [this] using member))
                      · rw [OrderedProps.lookup_delete_ne properties key _ equal valid]
                        exact tailPresent candidate member
                    rcases ih (properties.delete key) deletedValid nodupParts.2 tailParsed deletedPresent (by
                      simpa [deleteArrayIndexStep, below, key, found, configurable] using result) with
                      ⟨before, after, current, blockedDescriptor, split, swept, blockedFound,
                        blockedFixed, final⟩
                    exact ⟨index :: before, after, current, blockedDescriptor, by simp [split], by
                      simpa [deleteArrayIndexStep, below, key, found, configurable] using swept,
                      blockedFound, blockedFixed, final⟩

private theorem pairwise_split_before_gt (before after : List Nat) (blocked : Nat)
    (sorted : (before ++ blocked :: after).Pairwise fun left right => right ≤ left)
    (nodup : (before ++ blocked :: after).Nodup) :
    ∀ index ∈ before, blocked < index := by
  induction before with
  | nil => simp
  | cons head before ih =>
      have sortedParts := List.pairwise_cons.mp sorted
      have nodupParts := List.nodup_cons.mp nodup
      have blockedLe : blocked ≤ head := sortedParts.1 blocked (by simp)
      have headNe : head ≠ blocked := by
        intro equal
        apply nodupParts.1
        simp [equal]
      intro index member
      rcases List.mem_cons.mp member with rfl | tailMember
      · omega
      · exact ih sortedParts.2 nodupParts.2 index tailMember

private theorem pairwise_split_after_le (before after : List Nat) (blocked : Nat)
    (sorted : (before ++ blocked :: after).Pairwise fun left right => right ≤ left) :
    ∀ index ∈ after, index ≤ blocked := by
  induction before with
  | nil =>
      have parts := List.pairwise_cons.mp sorted
      exact parts.1
  | cons head before ih =>
      exact ih (List.pairwise_cons.mp sorted).2

private theorem deleteArrayIndicesFrom_blocked_lookups (properties next : OrderedProps)
    (newLength blocked : Nat) (valid : properties.WellFormed)
    (result : deleteArrayIndicesFrom properties newLength = (some blocked, next)) :
    (∀ key index descriptor, arrayIndexOfKey? key = some index →
      properties.lookup key = some descriptor → blocked < index →
      (match descriptor with
        | .data data => data.configurable = true
        | .accessor accessor => accessor.configurable = true) ∧ next.lookup key = none) ∧
    (∀ key index, arrayIndexOfKey? key = some index → index ≤ blocked →
      next.lookup key = properties.lookup key) := by
  let indices := properties.arrayIndices.reverse
  have nodup : indices.Nodup :=
    (List.reverse_perm properties.arrayIndices).nodup_iff.mpr
      (OrderedProps.arrayIndices_nodup properties valid)
  have parsed : ∀ index ∈ indices,
      PropertyKey.arrayIndex? (PropertyKey.arrayIndexString index) = some index :=
    fun index member => arrayIndices_canonical_parse properties index (List.mem_reverse.mp member)
  have present : ∀ index ∈ indices,
      (properties.lookup (.string (PropertyKey.arrayIndexString index))).isSome :=
    fun index member => arrayIndices_lookup_present properties index valid (List.mem_reverse.mp member)
  have foldResult : (indices.map fun index =>
      (index, .string (PropertyKey.arrayIndexString index))).foldl
        (deleteArrayIndexStep newLength) (none, properties) = (some blocked, next) := by
    unfold indices
    unfold deleteArrayIndicesFrom at result
    rw [arrayIndexEntries_eq] at result
    simpa only [List.map_reverse] using result
  rcases deleteArrayIndicesFold_blocked_split indices newLength blocked properties next valid
      nodup parsed present foldResult with
    ⟨before, after, current, blockedDescriptor, split, swept, blockedFound, blockedFixed, final⟩
  have ascending := OrderedProps.ownKeys_indices_ascending properties valid
  change properties.arrayIndices.Pairwise (· ≤ ·) at ascending
  have descending : indices.Pairwise fun left right => right ≤ left := by
    exact List.pairwise_reverse.mpr ascending
  rw [split] at descending nodup
  have beforeGt := pairwise_split_before_gt before after blocked descending nodup
  have afterLe := pairwise_split_after_le before after blocked descending
  have beforeValid : before.Nodup := (List.nodup_append.mp nodup).1
  have beforeParsed : ∀ index ∈ before,
      PropertyKey.arrayIndex? (PropertyKey.arrayIndexString index) = some index := by
    intro index member
    apply parsed index
    rw [split]
    simp [member]
  have beforePresent : ∀ index ∈ before,
      (properties.lookup (.string (PropertyKey.arrayIndexString index))).isSome := by
    intro index member
    apply present index
    rw [split]
    simp [member]
  have deleted := deleteArrayIndicesFold_unblocked before newLength properties current valid
    beforeValid beforeParsed beforePresent swept
  constructor
  · intro key index descriptor keyParsed found above
    cases key with
    | symbol symbol => simp [arrayIndexOfKey?] at keyParsed
    | string stringKey =>
        have canonical := PropertyKey.arrayIndex?_sound keyParsed
        subst stringKey
        have keyMember := (OrderedProps.mem_ownKeys_iff_lookup_isSome properties _ valid).mpr (by
          rw [found]
          rfl)
        have indexMember : index ∈ properties.arrayIndices := by
          unfold OrderedProps.arrayIndices
          exact List.mem_filterMap.mpr
            ⟨.string (PropertyKey.arrayIndexString index), keyMember, keyParsed⟩
        have descendingMember : index ∈ before ++ blocked :: after := by
          rw [← split]
          exact List.mem_reverse.mpr indexMember
        have beforeMember : index ∈ before := by
          rcases List.mem_append.mp descendingMember with member | member
          · exact member
          · rcases List.mem_cons.mp member with equal | afterMember
            · omega
            · have := afterLe index afterMember
              omega
        rcases deleted index beforeMember (by
          have bound := (deleteArrayIndicesFrom_blocked properties next newLength blocked valid result).1
          omega) with ⟨observed, observedFound, configurable, absent⟩
        rw [found] at observedFound
        cases observedFound
        rw [final]
        exact ⟨configurable, absent⟩
  · intro key index keyParsed atMost
    have preserved := deleteArrayIndicesFold_lookup_ne
      (before.map fun candidate =>
        (candidate, .string (PropertyKey.arrayIndexString candidate)))
      newLength none properties key valid (by
        intro entry member active equal
        rcases List.mem_map.mp member with ⟨candidate, candidateMember, pairEqual⟩
        cases pairEqual
        have candidateGt := beforeGt candidate candidateMember
        subst key
        have candidateParsed := beforeParsed candidate candidateMember
        change PropertyKey.arrayIndex? (PropertyKey.arrayIndexString candidate) = some index at keyParsed
        rw [keyParsed] at candidateParsed
        have := Option.some.inj candidateParsed
        omega)
    rw [swept] at preserved
    rw [final]
    exact preserved

private theorem deleteArrayIndicesFrom_wellFormed (properties : OrderedProps) (newLength : Nat)
    (valid : properties.WellFormed) :
    (deleteArrayIndicesFrom properties newLength).2.WellFormed := by
  exact deleteArrayIndicesFold_wellFormed _ newLength none properties valid

private theorem deleteArrayIndicesFrom_descriptors_all (properties : OrderedProps)
    (newLength : Nat) (predicate : PropertyDescriptor → Bool) (valid : properties.WellFormed)
    (current : properties.descriptors.all predicate = true) :
    (deleteArrayIndicesFrom properties newLength).2.descriptors.all predicate = true := by
  exact deleteArrayIndicesFold_descriptors_all _ newLength none properties predicate valid current

private theorem deleteArrayIndicesFrom_lookup_some (properties : OrderedProps) (newLength : Nat)
    (valid : properties.WellFormed) (query : PropertyKey) (descriptor : PropertyDescriptor)
    (found : (deleteArrayIndicesFrom properties newLength).2.lookup query = some descriptor) :
    properties.lookup query = some descriptor := by
  exact deleteArrayIndicesFold_lookup_some _ newLength none properties valid query descriptor found

private def defineArrayLength (heap : Heap) (ref : RefId) (object : ObjectRecord)
    (slots : ArraySlots) (update : DescriptorUpdate) (kind : DescriptorKind) :
    Except DefinePropertyFault (Bool × Heap) :=
  let requestedLength : Except DefinePropertyFault (Nat × DescriptorUpdate) :=
    match update.value with
    | .absent => .ok (slots.length, update)
    | .present (.primitive (.number number)) =>
        match validArrayLength? number with
        | some length => .ok (length, { update with
            value := .present (.primitive (.number (arrayLengthNumber length))) })
        | none => .error (.invalidArrayLength number)
    | .present value => .error (.invalidArrayLengthValue value)
  match requestedLength with
  | .error fault => .error fault
  | .ok (newLength, normalizedUpdate) =>
      match normalizedUpdate.applyValidatedDescriptor
          (some (syntheticLengthDescriptor slots)) true kind with
      | .error _ => .ok (false, heap)
      | .ok (.accessor _) => .ok (false, heap)
      | .ok (.data descriptor) =>
          if slots.length < newLength then
            heap.replace ref { object with kind := .array ⟨newLength, descriptor.writable⟩ }
              |>.mapError DefinePropertyFault.heap |>.map fun next => (true, next)
          else if slots.length = newLength then
            heap.replace ref { object with kind := .array ⟨newLength, descriptor.writable⟩ }
              |>.mapError DefinePropertyFault.heap |>.map fun next => (true, next)
          else if !slots.lengthWritable then .ok (false, heap)
          else
            let deleted := deleteArrayIndicesFrom object.properties newLength
            match deleted.1 with
            | none =>
                heap.replace ref (.mk deleted.2 object.prototype object.extensible
                    (.array ⟨newLength, descriptor.writable⟩))
                  |>.mapError DefinePropertyFault.heap |>.map fun next => (true, next)
            | some blocked =>
                heap.replace ref (.mk deleted.2 object.prototype object.extensible
                    (.array ⟨blocked + 1, descriptor.writable⟩))
                  |>.mapError DefinePropertyFault.heap |>.map fun next => (false, next)

private def defineArrayIndex (heap : Heap) (ref : RefId) (object : ObjectRecord)
    (slots : ArraySlots) (index : Nat) (key : PropertyKey) (update : DescriptorUpdate)
    (kind : DescriptorKind) : Except DefinePropertyFault (Bool × Heap) :=
  if slots.length ≤ index && !slots.lengthWritable then .ok (false, heap)
  else
    match ordinaryDefineValidated heap ref object key update kind with
    | .error fault => .error fault
    | .ok (false, _) => .ok (false, heap)
    | .ok (true, next) =>
        if index < slots.length then .ok (true, next)
        else
          match next.get? ref with
          | .error fault => .error (.heap fault)
          | .ok nextObject =>
              next.replace ref { nextObject with kind := .array ⟨index + 1, slots.lengthWritable⟩ }
                |>.mapError DefinePropertyFault.heap |>.map fun finalHeap => (true, finalHeap)

private def defineWrapperProperty (heap : Heap) (ref : RefId) (object : ObjectRecord)
    (slots : PrimitiveWrapperSlots) (key : PropertyKey) (update : DescriptorUpdate)
    (kind : DescriptorKind) : Except DefinePropertyFault (Bool × Heap) :=
  match syntheticWrapperDescriptor? slots key with
  | none => ordinaryDefineValidated heap ref object key update kind
  | some current =>
      match update.applyValidatedDescriptor (some current) true kind with
      | .ok _ => .ok (true, heap)
      | .error _ => .ok (false, heap)

/-- Defines an own property through the heap's complete validation boundary. -/
def defineOwnProperty (heap : Heap) (ref : RefId) (key : PropertyKey)
    (update : DescriptorUpdate) : Except DefinePropertyFault (Bool × Heap) :=
  match heap.get? ref with
  | .error fault => .error (.heap fault)
  | .ok object =>
      match update.validateSyntax with
      | .error fault => .error (.syntax fault)
      | .ok kind =>
          match validateDescriptorReferences heap update with
          | .error fault => .error fault
          | .ok () =>
              match object.kind with
              | .array slots =>
                  if key == lengthPropertyKey then defineArrayLength heap ref object slots update kind
                  else
                    match arrayIndexOfKey? key with
                    | some index => defineArrayIndex heap ref object slots index key update kind
                    | none => ordinaryDefineValidated heap ref object key update kind
              | .primitiveWrapper slots =>
                  defineWrapperProperty heap ref object slots key update kind
              | _ => ordinaryDefineValidated heap ref object key update kind

/-- Creates a writable, enumerable, configurable own data property. -/
def createDataProperty (heap : Heap) (ref : RefId) (key : PropertyKey) (value : Value) :
    Except DefinePropertyFault (Bool × Heap) :=
  defineOwnProperty heap ref key {
    value := .present value
    writable := .present true
    enumerable := .present true
    configurable := .present true
  }

private def hasSyntheticNonconfigurableProperty (object : ObjectRecord) (key : PropertyKey) : Bool :=
  match object.kind with
  | .array _ => key == lengthPropertyKey
  | .primitiveWrapper slots => (syntheticWrapperDescriptor? slots key).isSome
  | _ => false

private def deleteStoredProperty (heap : Heap) (ref : RefId) (object : ObjectRecord)
    (key : PropertyKey) : Except HeapFault (Bool × Heap) :=
  match object.properties.lookup key with
  | none => .ok (true, heap)
  | some (.data descriptor) =>
      if descriptor.configurable then
        heap.replace ref { object with properties := object.properties.delete key }
          |>.map fun next => (true, next)
      else .ok (false, heap)
  | some (.accessor descriptor) =>
      if descriptor.configurable then
        heap.replace ref { object with properties := object.properties.delete key }
          |>.map fun next => (true, next)
      else .ok (false, heap)

/-- Deletes a configurable own property through the validated heap boundary. -/
def deleteProperty (heap : Heap) (ref : RefId) (key : PropertyKey) :
    Except HeapFault (Bool × Heap) :=
  match heap.get? ref with
  | .error fault => .error fault
  | .ok object =>
      if hasSyntheticNonconfigurableProperty object key then .ok (false, heap)
      else deleteStoredProperty heap ref object key

private theorem mappedTrue_ne_false (result : Except ε α) (next : α) :
    result.map (fun value => (true, value)) ≠ .ok (false, next) := by
  intro equal
  cases result <;> cases equal

private theorem mappedFalse_ne_true (result : Except ε α) (next : α) :
    result.map (fun value => (false, value)) ≠ .ok (true, next) := by
  intro equal
  cases result <;> cases equal

/-- Every `false` property deletion leaves the heap unchanged, including synthetic array and
primitive-wrapper properties. Array length shrink is a define operation and is not a deletion. -/
theorem failed_delete_preserves_heap
    (heap next : Heap) (ref : RefId) (key : PropertyKey)
    (rejected : heap.deleteProperty ref key = .ok (false, next)) : next = heap := by
  unfold deleteProperty at rejected
  split at rejected <;> try contradiction
  split at rejected
  · simpa using rejected.symm
  · unfold deleteStoredProperty at rejected
    split at rejected
    · cases rejected
    · split at rejected
      · exact (mappedTrue_ne_false _ next rejected).elim
      · simpa using rejected.symm
    · split at rejected
      · exact (mappedTrue_ne_false _ next rejected).elim
      · simpa using rejected.symm

/-- Irreversibly makes an existing object nonextensible. -/
def preventExtensions (heap : Heap) (ref : RefId) : Except HeapFault Heap :=
  match heap.get? ref with
  | .error fault => .error fault
  | .ok object =>
      if object.extensible then heap.replace ref { object with extensible := false }
      else .ok heap

private def reachesWithFuel (heap : Heap) (target : RefId) : Nat → RefId → Except HeapFault Bool
  | 0, _ => .error .cycleOrFuelExhausted
  | fuel + 1, ref =>
      if ref = target then .ok true
      else
        match heap.get? ref with
        | .error _ => .error (.invalidPrototype ref)
        | .ok object =>
            match object.prototype with
            | none => .ok false
            | some parent => reachesWithFuel heap target fuel parent

/-- Implements validated `SetPrototypeOf` ordering and cycle prevention. -/
def setPrototypeOf (heap : Heap) (ref : RefId) (prototype : Option RefId) :
    Except HeapFault (Bool × Heap) :=
  match heap.get? ref with
  | .error fault => .error fault
  | .ok object =>
      if object.prototype = prototype then .ok (true, heap)
      else if !object.extensible then .ok (false, heap)
      else
        match prototype with
        | none => heap.replace ref { object with prototype := none } |>.map fun next => (true, next)
        | some parent =>
            match reachesWithFuel heap ref (heap.size + 1) parent with
            | .error fault => .error fault
            | .ok true => .ok (false, heap)
            | .ok false =>
                heap.replace ref { object with prototype := some parent } |>.map fun next => (true, next)

/-- Prototype mutation preserves every object's internal-method kind. -/
theorem setPrototypeOf_preserves_objectKind (heap next : Heap) (target : RefId)
    (prototype : Option RefId) (success : Bool)
    (updated : heap.setPrototypeOf target prototype = .ok (success, next)) (ref : RefId) :
    next.objectKind? ref = heap.objectKind? ref := by
  unfold setPrototypeOf at updated
  cases foundEq : heap.get? target with
  | error fault => simp [foundEq] at updated
  | ok object =>
      rw [foundEq] at updated
      by_cases same : object.prototype = prototype
      · simp [same] at updated
        obtain ⟨rfl, rfl⟩ := updated
        rfl
      · cases extensibleEq : object.extensible with
        | false =>
          simp [same, extensibleEq] at updated
          obtain ⟨rfl, rfl⟩ := updated
          rfl
        | true => cases prototype with
          | none =>
              simp [same, extensibleEq] at updated
              let replacement := { object with prototype := none, extensible := true }
              cases replaceEq : heap.replace target replacement with
              | error fault =>
                  dsimp [replacement] at replaceEq
                  rw [replaceEq] at updated
                  contradiction
              | ok replacedHeap =>
                  dsimp [replacement] at replaceEq
                  rw [replaceEq] at updated
                  change Except.ok (true, replacedHeap) = Except.ok (success, next) at updated
                  obtain ⟨rfl, rfl⟩ := updated
                  exact replace_preserves_objectKind heap next target ref object
                    { object with prototype := none, extensible := true } foundEq rfl replaceEq
          | some parent =>
              cases reachEq : heap.reachesWithFuel target (heap.size + 1) parent with
              | error fault => simp [same, extensibleEq, reachEq] at updated
              | ok reached =>
                  cases reached with
                  | false =>
                      simp [same, extensibleEq, reachEq] at updated
                      let replacement := { object with prototype := some parent, extensible := true }
                      cases replaceEq : heap.replace target replacement with
                      | error fault =>
                          dsimp [replacement] at replaceEq
                          rw [replaceEq] at updated
                          contradiction
                      | ok replacedHeap =>
                          dsimp [replacement] at replaceEq
                          rw [replaceEq] at updated
                          change Except.ok (true, replacedHeap) = Except.ok (success, next) at updated
                          obtain ⟨rfl, rfl⟩ := updated
                          exact replace_preserves_objectKind heap next target ref object
                            { object with prototype := some parent, extensible := true }
                            foundEq rfl replaceEq
                  | true =>
                      simp [same, extensibleEq, reachEq] at updated
                      obtain ⟨rfl, rfl⟩ := updated
                      rfl

private def callableReferenceValid (heap : Heap) (ref : RefId) : Bool :=
  match heap.isCallable ref with
  | .ok callable => callable
  | .error _ => false

private def descriptorReferencesValid (heap : Heap) : PropertyDescriptor → Bool
  | .data descriptor => heap.valueValid descriptor.value
  | .accessor descriptor =>
      descriptor.get.all (callableReferenceValid heap) &&
      descriptor.set.all (callableReferenceValid heap)

private def functionSlotsValid (heap : Heap) (slots : FunctionSlots) : Bool :=
  slots.functionId.value < heap.functionCount &&
  slots.homeObject.all (fun home => home.value < heap.size) &&
  slots.lexicalThis.all heap.valueValid &&
  !(slots.kind = .arrow && slots.constructible) &&
  !(slots.kind = .classConstructor && !slots.constructible) &&
  !(slots.constructorMode = .derived && slots.kind != .classConstructor) &&
  (if slots.kind = .arrow then slots.lexicalThis.isSome else slots.lexicalThis.isNone)

private def arraySlotsValid (object : ObjectRecord) (slots : ArraySlots) : Bool :=
  slots.length ≤ maxArrayLength && object.properties.keysAll fun key =>
    match arrayIndexOfKey? key with
    | some index => index < slots.length
    | none => key != lengthPropertyKey

private def primitiveWrapperSlotsValid (object : ObjectRecord) (slots : PrimitiveWrapperSlots) : Bool :=
  primitiveBoxable slots.value && object.properties.keysAll fun key =>
    (syntheticWrapperDescriptor? slots key).isNone

private def arrayIteratorSlotsValid (heap : Heap) (slots : ArrayIteratorSlots) : Bool :=
  match heap.objects[slots.target.value]? with
  | some target => match target.kind with
      | .array _ => true
      | _ => false
  | none => false

private def objectReferencesValid (heap : Heap) (object : ObjectRecord) : Bool :=
  object.properties.isWellFormed &&
  object.properties.descriptors.all (descriptorReferencesValid heap) &&
  object.prototype.all (fun prototype => prototype.value < heap.size) &&
  match object.kind with
  | .ordinary => true
  | .function slots => functionSlotsValid heap slots
  | .array slots => arraySlotsValid object slots
  | .arrayIterator slots => arrayIteratorSlotsValid heap slots
  | .primitiveWrapper slots => primitiveWrapperSlotsValid object slots

/-- Function slots in object allocation order. -/
def functionSlotList (heap : Heap) : List FunctionSlots :=
  heap.objects.toList.filterMap fun object =>
    match object.kind with
    | .ordinary | .array _ | .arrayIterator _ | .primitiveWrapper _ => none
    | .function slots => some slots

/-- Captured environments referenced by all function objects. -/
def functionEnvironments (heap : Heap) : List EnvId :=
  heap.functionSlotList.map (·.environment)

private inductive PrototypeColor where
  | unseen
  | visiting
  | done
  deriving DecidableEq

private def finishPrototypePath (colors : Array PrototypeColor) (path : List RefId) :
    Array PrototypeColor :=
  path.foldl (fun current ref => current.setIfInBounds ref.value .done) colors

private def visitPrototype (heap : Heap) : Nat → Array PrototypeColor → List RefId → RefId →
    Option (Array PrototypeColor)
  | 0, _, _, _ => none
  | fuel + 1, colors, path, ref =>
      match colors[ref.value]?, heap.objects[ref.value]? with
      | some .done, some _ => some (finishPrototypePath colors path)
      | some .visiting, some _ => none
      | some .unseen, some object =>
          let nextColors := colors.setIfInBounds ref.value .visiting
          let nextPath := ref :: path
          match object.prototype with
          | none => some (finishPrototypePath nextColors nextPath)
          | some parent => visitPrototype heap fuel nextColors nextPath parent
      | _, _ => none

private def validatePrototypeGraphAux (heap : Heap) : Nat → Nat → Array PrototypeColor → Bool
  | 0, index, _ => index == heap.size
  | remaining + 1, index, colors =>
      match colors[index]? with
      | none => index == heap.size
      | some .done => validatePrototypeGraphAux heap remaining (index + 1) colors
      | some _ =>
          match visitPrototype heap (heap.size + 1) colors [] ⟨index⟩ with
          | none => false
          | some next => validatePrototypeGraphAux heap remaining (index + 1) next

/-- Stack-safe linear prototype graph validation. Each object changes color at most twice. -/
def prototypeGraphAcyclic (heap : Heap) : Bool :=
  validatePrototypeGraphAux heap heap.size 0 (Array.replicate heap.size .unseen)

private def prototypeAt (heap : Heap) (index : Nat) : Option (Option RefId) :=
  (heap.objects[index]?).map (·.prototype)

private def PrototypeEquivalent (left right : Heap) : Prop :=
  left.size = right.size ∧ ∀ index, prototypeAt left index = prototypeAt right index

private theorem visitPrototype_prototypeEquivalent (left right : Heap)
    (equivalent : PrototypeEquivalent left right) (fuel : Nat) (colors : Array PrototypeColor)
    (path : List RefId) (ref : RefId) :
    visitPrototype left fuel colors path ref = visitPrototype right fuel colors path ref := by
  induction fuel generalizing colors path ref with
  | zero => rfl
  | succ fuel ih =>
      unfold visitPrototype
      cases colorFound : colors[ref.value]? with
      | none => rfl
      | some color =>
          cases leftFound : left.objects[ref.value]? with
          | none =>
              have same := equivalent.2 ref.value
              simp [prototypeAt, leftFound] at same
              cases rightFound : right.objects[ref.value]? <;> simp_all
          | some leftObject =>
              have same := equivalent.2 ref.value
              simp [prototypeAt, leftFound] at same
              cases rightFound : right.objects[ref.value]? with
              | none => simp [prototypeAt, rightFound] at same
              | some rightObject =>
                  simp [prototypeAt, rightFound] at same
                  cases color with
                  | done => rfl
                  | visiting => rfl
                  | unseen =>
                      simp only [leftFound, rightFound, colorFound]
                      rw [same]
                      cases rightObject.prototype
                      · rfl
                      · exact ih _ _ _

private theorem validatePrototypeGraphAux_prototypeEquivalent (left right : Heap)
    (equivalent : PrototypeEquivalent left right) (remaining index : Nat)
    (colors : Array PrototypeColor) :
    validatePrototypeGraphAux left remaining index colors =
      validatePrototypeGraphAux right remaining index colors := by
  induction remaining generalizing index colors with
  | zero => simp [validatePrototypeGraphAux, equivalent.1]
  | succ remaining ih =>
      simp only [validatePrototypeGraphAux]
      cases colorFound : colors[index]? with
      | none => simp [equivalent.1]
      | some color =>
          cases color with
          | done => exact ih _ _
          | unseen =>
              rw [equivalent.1]
              rw [visitPrototype_prototypeEquivalent left right equivalent]
              cases right.visitPrototype (right.size + 1) colors [] ⟨index⟩
              · rfl
              · exact ih _ _
          | visiting =>
              rw [equivalent.1]
              rw [visitPrototype_prototypeEquivalent left right equivalent]
              cases right.visitPrototype (right.size + 1) colors [] ⟨index⟩
              · rfl
              · exact ih _ _

private theorem prototypeGraphAcyclic_prototypeEquivalent (left right : Heap)
    (equivalent : PrototypeEquivalent left right) :
    left.prototypeGraphAcyclic = right.prototypeGraphAcyclic := by
  unfold prototypeGraphAcyclic
  rw [equivalent.1]
  exact validatePrototypeGraphAux_prototypeEquivalent left right equivalent _ _ _

private theorem finishPrototypePath_push (colors : Array PrototypeColor) (path : List RefId)
    (valid : ∀ ref ∈ path, ref.value < colors.size) :
    finishPrototypePath (colors.push .unseen) path =
      (finishPrototypePath colors path).push .unseen := by
  unfold finishPrototypePath
  induction path generalizing colors with
  | nil => rfl
  | cons ref path ih =>
      rw [List.foldl_cons, List.foldl_cons]
      have refValid := valid ref (by simp)
      have restValid : ∀ item ∈ path,
          item.value < (colors.setIfInBounds ref.value .done).size := by
        intro item member
        simpa using valid item (by simp [member])
      rw [show (colors.push .unseen).setIfInBounds ref.value .done =
          (colors.setIfInBounds ref.value .done).push .unseen by
        rw [Array.setIfInBounds_def, dif_pos (by simp; omega)]
        rw [Array.setIfInBounds_def, dif_pos refValid]
        rw [Array.set_push, dif_pos refValid]]
      exact ih _ restValid

private theorem visitPrototype_fuel_mono (heap : Heap) (fuel : Nat)
    (colors : Array PrototypeColor) (path : List RefId) (ref : RefId)
    (result : Array PrototypeColor)
    (visited : visitPrototype heap fuel colors path ref = some result) :
    visitPrototype heap (fuel + 1) colors path ref = some result := by
  induction fuel generalizing colors path ref result with
  | zero => simp [visitPrototype] at visited
  | succ fuel ih =>
      simp only [visitPrototype] at visited ⊢
      cases colorFound : colors[ref.value]? with
      | none => simp [colorFound] at visited
      | some color =>
          cases objectFound : heap.objects[ref.value]? with
          | none => simp [colorFound, objectFound] at visited
          | some object =>
              simp only [colorFound, objectFound] at visited
              cases color with
              | done => exact visited
              | visiting => contradiction
              | unseen =>
                  cases prototypeEq : object.prototype with
                  | none => simpa [prototypeEq] using visited
                  | some parent =>
                      simp only [prototypeEq] at visited ⊢
                      exact ih _ _ _ _ visited

private theorem visitPrototype_push (heap : Heap) (newObject : ObjectRecord)
    (nextFunctionId fuel : Nat) (colors : Array PrototypeColor) (path : List RefId)
    (ref : RefId)
    (referencesValid : ∀ (index : Nat) (object : ObjectRecord),
      heap.objects[index]? = some object →
      object.prototype.all (fun prototype => prototype.value < heap.size) = true)
    (colorsSize : colors.size = heap.size)
    (refValid : ref.value < heap.size)
    (pathValid : ∀ item ∈ path, item.value < heap.size) :
    visitPrototype
        (.mk (heap.objects.push newObject) nextFunctionId) fuel
        (colors.push .unseen) path ref =
      (visitPrototype heap fuel colors path ref).map (·.push .unseen) := by
  induction fuel generalizing colors path ref with
  | zero => rfl
  | succ fuel ih =>
      have colorLookup : (colors.push .unseen)[ref.value]? = colors[ref.value]? := by
        rw [Array.getElem?_push, if_neg (by omega)]
      have objectLookup : (heap.objects.push newObject)[ref.value]? =
          heap.objects[ref.value]? := by
        rw [Array.getElem?_push, if_neg (by simpa [size] using Nat.ne_of_lt refValid)]
      simp only [visitPrototype, colorLookup, objectLookup]
      cases colorFound : colors[ref.value]? with
      | none => rfl
      | some color =>
          cases objectFound : heap.objects[ref.value]? with
          | none => cases color <;> rfl
          | some object =>
              cases color with
              | done =>
                  simp only [Option.map_some]
                  rw [finishPrototypePath_push colors path]
                  intro item member
                  rw [colorsSize]
                  exact pathValid item member
              | visiting => simp
              | unseen =>
                  have setPush : (colors.push .unseen).setIfInBounds ref.value .visiting =
                      (colors.setIfInBounds ref.value .visiting).push .unseen := by
                    rw [Array.setIfInBounds_def, dif_pos (by simp; omega)]
                    rw [Array.setIfInBounds_def, dif_pos (by omega)]
                    rw [Array.set_push, dif_pos (by omega)]
                  rw [setPush]
                  cases prototypeEq : object.prototype with
                  | none =>
                      simp only [prototypeEq, Option.map_some]
                      rw [finishPrototypePath_push]
                      intro item member
                      simp only [List.mem_cons] at member
                      cases member with
                      | inl same =>
                          rw [Array.size_setIfInBounds, colorsSize]
                          simpa [same] using refValid
                      | inr member =>
                          rw [Array.size_setIfInBounds, colorsSize]
                          exact pathValid item member
                  | some parent =>
                      simp only [prototypeEq]
                      have parentValid : parent.value < heap.size := by
                        have := referencesValid ref.value object objectFound
                        simp [prototypeEq] at this
                        exact this
                      apply ih (colors := colors.setIfInBounds ref.value .visiting)
                        (path := ref :: path) (ref := parent) (by simpa using colorsSize) parentValid
                      intro item member
                      simp only [List.mem_cons] at member
                      cases member with
                      | inl same => simpa [same] using refValid
                      | inr member => exact pathValid item member

private theorem finishPrototypePath_preserves_done (colors : Array PrototypeColor)
    (path : List RefId) (ref : RefId) (done : colors[ref.value]? = some .done) :
    (finishPrototypePath colors path)[ref.value]? = some .done := by
  unfold finishPrototypePath
  induction path generalizing colors with
  | nil => exact done
  | cons item path ih =>
      rw [List.foldl_cons]
      apply ih
      rw [Array.getElem?_setIfInBounds]
      by_cases same : item.value = ref.value
      · simp [same, (Array.getElem?_eq_some_iff.mp done).choose]
      · simp [same, done]

private theorem finishPrototypePath_done (colors : Array PrototypeColor) (path : List RefId)
    (ref : RefId) (member : ref ∈ path) (valid : ref.value < colors.size) :
    (finishPrototypePath colors path)[ref.value]? = some .done := by
  unfold finishPrototypePath
  induction path generalizing colors with
  | nil => contradiction
  | cons head path ih =>
      rw [List.foldl_cons]
      simp only [List.mem_cons] at member
      cases member with
      | inl same =>
          subst head
          apply finishPrototypePath_preserves_done
          simp [Array.getElem?_setIfInBounds, valid]
      | inr member =>
          apply ih _ member
          simpa using valid

private theorem visitPrototype_preserves_done (heap : Heap) (fuel : Nat)
    (colors result : Array PrototypeColor) (path : List RefId) (start ref : RefId)
    (done : colors[ref.value]? = some .done)
    (visited : visitPrototype heap fuel colors path start = some result) :
    result[ref.value]? = some .done := by
  induction fuel generalizing colors result path start with
  | zero => simp [visitPrototype] at visited
  | succ fuel ih =>
      simp only [visitPrototype] at visited
      cases colorFound : colors[start.value]? with
      | none => simp [colorFound] at visited
      | some color =>
          cases objectFound : heap.objects[start.value]? with
          | none => simp [colorFound, objectFound] at visited
          | some object =>
              simp only [colorFound, objectFound] at visited
              cases color with
              | done =>
                  cases visited
                  exact finishPrototypePath_preserves_done colors path ref done
              | visiting => contradiction
              | unseen =>
                  have nextDone :
                      (colors.setIfInBounds start.value .visiting)[ref.value]? = some .done := by
                    rw [Array.getElem?_setIfInBounds]
                    by_cases same : start.value = ref.value
                    · rw [if_pos same]
                      have inBounds : start.value < colors.size :=
                        (Array.getElem?_eq_some_iff.mp colorFound).choose
                      simp [inBounds]
                      rw [same] at colorFound
                      simp [colorFound] at done
                    · simp [same, done]
                  cases prototypeEq : object.prototype with
                  | none =>
                      simp [prototypeEq] at visited
                      cases visited
                      exact finishPrototypePath_preserves_done _ _ ref nextDone
                  | some parent =>
                      simp [prototypeEq] at visited
                      exact ih _ _ _ _ nextDone visited

private theorem visitPrototype_marks_path_done (heap : Heap) (fuel : Nat)
    (colors result : Array PrototypeColor) (path : List RefId) (start ref : RefId)
    (referencesValid : ∀ (index : Nat) (object : ObjectRecord),
      heap.objects[index]? = some object →
      object.prototype.all (fun prototype => prototype.value < heap.size) = true)
    (colorsSize : colors.size = heap.size) (startValid : start.value < heap.size)
    (pathValid : ∀ item ∈ path, item.value < heap.size)
    (member : ref = start ∨ ref ∈ path)
    (visited : visitPrototype heap fuel colors path start = some result) :
    result[ref.value]? = some .done := by
  induction fuel generalizing colors result path start with
  | zero => simp [visitPrototype] at visited
  | succ fuel ih =>
      simp only [visitPrototype] at visited
      have colorSome : ∃ color, colors[start.value]? = some color := by
        cases found : colors[start.value]? with
        | none =>
            have := Array.getElem?_eq_none_iff.mp found
            omega
        | some color => exact ⟨color, rfl⟩
      obtain ⟨color, colorFound⟩ := colorSome
      have objectSome : ∃ object, heap.objects[start.value]? = some object := by
        cases found : heap.objects[start.value]? with
        | none =>
            have := Array.getElem?_eq_none_iff.mp found
            simp [size] at startValid
            omega
        | some object => exact ⟨object, rfl⟩
      obtain ⟨object, objectFound⟩ := objectSome
      simp only [colorFound, objectFound] at visited
      cases color with
      | visiting => contradiction
      | done =>
          cases visited
          cases member with
          | inl same =>
              exact finishPrototypePath_preserves_done colors path ref (by simpa [same] using colorFound)
          | inr member =>
              apply finishPrototypePath_done colors path ref member
              rw [colorsSize]
              exact pathValid ref member
      | unseen =>
          cases prototypeEq : object.prototype with
          | none =>
              simp [prototypeEq] at visited
              cases visited
              apply finishPrototypePath_done _ (start :: path) ref
              · simpa [member]
              · rw [Array.size_setIfInBounds, colorsSize]
                cases member with
                | inl same => simpa [same] using startValid
                | inr member => exact pathValid ref member
          | some parent =>
              simp [prototypeEq] at visited
              have parentValid : parent.value < heap.size := by
                have := referencesValid start.value object objectFound
                simp [prototypeEq] at this
                exact this
              apply ih (colors := colors.setIfInBounds start.value .visiting)
                (result := result) (path := start :: path) (start := parent)
                (by simpa using colorsSize) parentValid
              · intro item itemMember
                simp only [List.mem_cons] at itemMember
                cases itemMember with
                | inl same => simpa [same] using startValid
                | inr itemMember => exact pathValid item itemMember
              · exact Or.inr (by simpa [member])
              · exact visited

private theorem finishPrototypePath_size (colors : Array PrototypeColor) (path : List RefId) :
    (finishPrototypePath colors path).size = colors.size := by
  unfold finishPrototypePath
  induction path generalizing colors with
  | nil => rfl
  | cons ref path ih =>
      rw [List.foldl_cons, ih]
      simp

private theorem visitPrototype_size (heap : Heap) (fuel : Nat) (colors result : Array PrototypeColor)
    (path : List RefId) (ref : RefId)
    (visited : visitPrototype heap fuel colors path ref = some result) :
    result.size = colors.size := by
  induction fuel generalizing colors result path ref with
  | zero => simp [visitPrototype] at visited
  | succ fuel ih =>
      simp only [visitPrototype] at visited
      cases colorFound : colors[ref.value]? with
      | none => simp [colorFound] at visited
      | some color =>
          cases objectFound : heap.objects[ref.value]? with
          | none => simp [colorFound, objectFound] at visited
          | some object =>
              simp only [colorFound, objectFound] at visited
              cases color with
              | done =>
                  cases visited
                  exact finishPrototypePath_size colors path
              | visiting => contradiction
              | unseen =>
                  cases prototypeEq : object.prototype with
                  | none =>
                      simp [prototypeEq] at visited
                      cases visited
                      rw [finishPrototypePath_size]
                      simp
                  | some parent =>
                      simp [prototypeEq] at visited
                      have sizeEq := ih (colors.setIfInBounds ref.value .visiting) result
                        (ref :: path) parent visited
                      simpa using sizeEq

private theorem validatePrototypeGraphAux_push_end (heap : Heap) (newObject : ObjectRecord)
    (nextFunctionId remaining : Nat) (colors : Array PrototypeColor)
    (newPrototypeValid : newObject.prototype.all
      (fun prototype => prototype.value < heap.size) = true)
    (colorsSize : colors.size = heap.size)
    (allDone : ∀ i < heap.size, colors[i]? = some .done) :
    validatePrototypeGraphAux (.mk (heap.objects.push newObject) nextFunctionId)
      (remaining + 1) heap.size (colors.push .unseen) = true := by
  let next : Heap := .mk (heap.objects.push newObject) nextFunctionId
  change validatePrototypeGraphAux next (remaining + 1) heap.size
    (colors.push .unseen) = true
  have nextSize : next.size = heap.size + 1 := by simp [next, size]
  have lastColor : (colors.push .unseen)[heap.size]? = some .unseen := by
    rw [show heap.size = colors.size by omega]
    simp
  have lastObject : next.objects[heap.size]? = some newObject := by
    simp [next, size]
  have visitNew : ∃ result,
      visitPrototype next (next.size + 1) (colors.push .unseen) [] ⟨heap.size⟩ = some result := by
    cases prototypeEq : newObject.prototype with
    | none =>
        refine ⟨finishPrototypePath
          ((colors.push .unseen).setIfInBounds heap.size .visiting) [⟨heap.size⟩], ?_⟩
        simp [visitPrototype, lastColor, lastObject, prototypeEq]
    | some parent =>
        have parentValid : parent.value < heap.size := by
          simpa [prototypeEq] using newPrototypeValid
        have parentDone : (colors.push .unseen)[parent.value]? = some .done := by
          rw [Array.getElem?_push, if_neg (by omega)]
          exact allDone parent.value parentValid
        have parentObject : ∃ object, next.objects[parent.value]? = some object := by
          cases found : heap.objects[parent.value]? with
          | none =>
              have := Array.getElem?_eq_none_iff.mp found
              simp [size] at parentValid
              omega
          | some object =>
              refine ⟨object, ?_⟩
              simp [next, Array.getElem?_push, show parent.value ≠ heap.objects.size by
                simpa [size] using Nat.ne_of_lt parentValid, found]
        obtain ⟨parentObject, parentFound⟩ := parentObject
        refine ⟨finishPrototypePath
          ((colors.push .unseen).setIfInBounds heap.size .visiting) [⟨heap.size⟩], ?_⟩
        have parentDoneAfter :
            ((colors.push .unseen).setIfInBounds heap.size .visiting)[parent.value]? =
              some .done := by
          rw [Array.getElem?_setIfInBounds]
          simp [show heap.size ≠ parent.value by omega, parentDone]
        rw [visitPrototype]
        rw [lastColor, lastObject]
        simp only [prototypeEq]
        rw [nextSize]
        simp only [visitPrototype]
        rw [parentDoneAfter, parentFound]
  obtain ⟨result, visitNew⟩ := visitNew
  simp only [validatePrototypeGraphAux, lastColor, visitNew]
  have resultSize := visitPrototype_size next (next.size + 1) (colors.push .unseen)
    result [] ⟨heap.size⟩ visitNew
  have pastEnd : result[heap.size + 1]? = none := by
    rw [Array.getElem?_eq_none_iff]
    simp at resultSize
    omega
  cases remaining with
  | zero => simp [validatePrototypeGraphAux, pastEnd, nextSize]
  | succ remaining => simp [validatePrototypeGraphAux, pastEnd, nextSize]

private theorem validatePrototypeGraphAux_push (heap : Heap) (newObject : ObjectRecord)
    (nextFunctionId remaining index : Nat) (colors : Array PrototypeColor)
    (referencesValid : ∀ (i : Nat) (object : ObjectRecord),
      heap.objects[i]? = some object →
      object.prototype.all (fun prototype => prototype.value < heap.size) = true)
    (newPrototypeValid : newObject.prototype.all
      (fun prototype => prototype.value < heap.size) = true)
    (colorsSize : colors.size = heap.size)
    (doneBefore : ∀ i < index, colors[i]? = some .done)
    (valid : validatePrototypeGraphAux heap remaining index colors = true) :
    validatePrototypeGraphAux (.mk (heap.objects.push newObject) nextFunctionId)
      (remaining + 1) index (colors.push .unseen) = true := by
  induction remaining generalizing index colors with
  | zero =>
      simp only [validatePrototypeGraphAux] at valid
      have indexEq : index = heap.size := by simpa using valid
      subst index
      exact validatePrototypeGraphAux_push_end heap newObject nextFunctionId 0 colors
        newPrototypeValid colorsSize doneBefore
  | succ remaining ih =>
      rw [validatePrototypeGraphAux] at valid
      cases colorFound : colors[index]? with
      | none =>
          have indexEq : index = heap.size := by simpa [colorFound] using valid
          subst index
          exact validatePrototypeGraphAux_push_end heap newObject nextFunctionId
            (remaining + 1) colors newPrototypeValid colorsSize doneBefore
      | some color =>
          have indexBound : index < colors.size :=
            (Array.getElem?_eq_some_iff.mp colorFound).choose
          have indexOld : index < heap.size := by simpa [colorsSize] using indexBound
          have indexNe : index ≠ colors.size := Nat.ne_of_lt indexBound
          rw [validatePrototypeGraphAux]
          rw [Array.getElem?_push, if_neg indexNe, colorFound]
          simp only [colorFound] at valid
          cases color with
          | done =>
              apply ih (colors := colors) (index := index + 1) colorsSize
              · intro i before
                by_cases same : i = index
                · simpa [same] using colorFound
                · exact doneBefore i (by omega)
              · exact valid
          | visiting =>
              cases visited : visitPrototype heap (heap.size + 1) colors [] ⟨index⟩ with
              | none => simp [visited] at valid
              | some nextColors =>
                  simp only [visited] at valid
                  have pushedVisit := visitPrototype_push heap newObject nextFunctionId
                    (heap.size + 1) colors [] ⟨index⟩ referencesValid colorsSize indexOld (by simp)
                  rw [visited] at pushedVisit
                  have nextVisited := visitPrototype_fuel_mono
                    (.mk (heap.objects.push newObject) nextFunctionId) (heap.size + 1)
                    (colors.push .unseen) [] ⟨index⟩ (nextColors.push .unseen) (by simpa using pushedVisit)
                  have nextSize : (.mk (heap.objects.push newObject) nextFunctionId : Heap).size + 1 =
                      heap.size + 1 + 1 := by simp [size]
                  have nextVisited' : visitPrototype
                      (.mk (heap.objects.push newObject) nextFunctionId)
                      ((.mk (heap.objects.push newObject) nextFunctionId : Heap).size + 1)
                      (colors.push .unseen) [] ⟨index⟩ = some (nextColors.push .unseen) := by
                    rw [nextSize]
                    exact nextVisited
                  rw [nextVisited']
                  apply ih (colors := nextColors) (index := index + 1)
                  · rw [visitPrototype_size heap (heap.size + 1) colors nextColors [] ⟨index⟩ visited,
                      colorsSize]
                  · intro i before
                    by_cases same : i = index
                    · subst i
                      exact visitPrototype_marks_path_done heap (heap.size + 1) colors nextColors
                        [] ⟨index⟩ ⟨index⟩ referencesValid colorsSize indexOld (by simp)
                        (Or.inl rfl) visited
                    · exact visitPrototype_preserves_done heap (heap.size + 1) colors nextColors
                        [] ⟨index⟩ ⟨i⟩ (doneBefore i (by omega)) visited
                  · exact valid
          | unseen =>
              cases visited : visitPrototype heap (heap.size + 1) colors [] ⟨index⟩ with
              | none => simp [visited] at valid
              | some nextColors =>
                  simp only [visited] at valid
                  have pushedVisit := visitPrototype_push heap newObject nextFunctionId
                    (heap.size + 1) colors [] ⟨index⟩ referencesValid colorsSize indexOld (by simp)
                  rw [visited] at pushedVisit
                  have nextVisited := visitPrototype_fuel_mono
                    (.mk (heap.objects.push newObject) nextFunctionId) (heap.size + 1)
                    (colors.push .unseen) [] ⟨index⟩ (nextColors.push .unseen) (by simpa using pushedVisit)
                  have nextSize : (.mk (heap.objects.push newObject) nextFunctionId : Heap).size + 1 =
                      heap.size + 1 + 1 := by simp [size]
                  have nextVisited' : visitPrototype
                      (.mk (heap.objects.push newObject) nextFunctionId)
                      ((.mk (heap.objects.push newObject) nextFunctionId : Heap).size + 1)
                      (colors.push .unseen) [] ⟨index⟩ = some (nextColors.push .unseen) := by
                    rw [nextSize]
                    exact nextVisited
                  rw [nextVisited']
                  apply ih (colors := nextColors) (index := index + 1)
                  · rw [visitPrototype_size heap (heap.size + 1) colors nextColors [] ⟨index⟩ visited,
                      colorsSize]
                  · intro i before
                    by_cases same : i = index
                    · subst i
                      exact visitPrototype_marks_path_done heap (heap.size + 1) colors nextColors
                        [] ⟨index⟩ ⟨index⟩ referencesValid colorsSize indexOld (by simp)
                        (Or.inl rfl) visited
                    · exact visitPrototype_preserves_done heap (heap.size + 1) colors nextColors
                        [] ⟨index⟩ ⟨i⟩ (doneBefore i (by omega)) visited
                  · exact valid

private theorem prototypeGraphAcyclic_push (heap : Heap) (newObject : ObjectRecord)
    (nextFunctionId : Nat)
    (referencesValid : ∀ (i : Nat) (object : ObjectRecord),
      heap.objects[i]? = some object →
      object.prototype.all (fun prototype => prototype.value < heap.size) = true)
    (newPrototypeValid : newObject.prototype.all
      (fun prototype => prototype.value < heap.size) = true)
    (valid : heap.prototypeGraphAcyclic = true) :
    prototypeGraphAcyclic (.mk (heap.objects.push newObject) nextFunctionId) = true := by
  unfold prototypeGraphAcyclic at valid ⊢
  have pushed := validatePrototypeGraphAux_push heap newObject nextFunctionId heap.size 0
    (Array.replicate heap.size .unseen) referencesValid newPrototypeValid (by simp) (by simp) valid
  simpa [size, Array.replicate_succ] using pushed

private theorem valueValid_push (heap : Heap) (newObject : ObjectRecord)
    (nextFunctionId : Nat) (value : Value) (valid : heap.valueValid value = true) :
    valueValid (.mk (heap.objects.push newObject) nextFunctionId) value = true := by
  cases value with
  | primitive value => rfl
  | object ref =>
      unfold valueValid size at valid ⊢
      simp at valid ⊢
      omega

private theorem callableReferenceValid_push (heap : Heap) (newObject : ObjectRecord)
    (nextFunctionId : Nat) (ref : RefId) (valid : callableReferenceValid heap ref = true) :
    callableReferenceValid (.mk (heap.objects.push newObject) nextFunctionId) ref = true := by
  unfold callableReferenceValid isCallable functionSlots? at valid ⊢
  cases found : heap.get? ref with
  | error fault =>
      simp [found, Bind.bind, Except.instMonad, Monad.toBind, Except.bind] at valid
  | ok object =>
      have refValid : ref.value < heap.size := by
        unfold get? at found
        cases lookup : heap.objects[ref.value]? with
        | none => simp [lookup] at found
        | some current =>
            have := (Array.getElem?_eq_some_iff.mp lookup).choose
            simpa [size] using this
      have nextFound : (.mk (heap.objects.push newObject) nextFunctionId : Heap).get? ref = .ok object := by
        unfold get? at found ⊢
        rw [Array.getElem?_push, if_neg (by simpa [size] using Nat.ne_of_lt refValid)]
        exact found
      rw [nextFound]
      rw [found] at valid
      cases object.kind <;> simp_all

private theorem descriptorReferencesValid_push (heap : Heap) (newObject : ObjectRecord)
    (nextFunctionId : Nat) (descriptor : PropertyDescriptor)
    (valid : descriptorReferencesValid heap descriptor = true) :
    descriptorReferencesValid (.mk (heap.objects.push newObject) nextFunctionId) descriptor = true := by
  cases descriptor with
  | data descriptor => exact valueValid_push heap newObject nextFunctionId descriptor.value valid
  | accessor descriptor =>
      cases descriptor with
      | mk getter setter enumerable configurable =>
          cases getter <;> cases setter <;>
            simp_all [descriptorReferencesValid, callableReferenceValid_push]

private theorem objectReferencesValid_push (heap : Heap) (newObject object : ObjectRecord)
    (nextFunctionId : Nat) (countMono : heap.nextFunctionId ≤ nextFunctionId)
    (valid : objectReferencesValid heap object = true) :
    objectReferencesValid (.mk (heap.objects.push newObject) nextFunctionId) object = true := by
  unfold objectReferencesValid at valid ⊢
  simp only [Bool.and_eq_true] at valid ⊢
  refine ⟨⟨⟨valid.1.1.1, ?_⟩, ?_⟩, ?_⟩
  · rw [List.all_eq_true] at valid ⊢
    intro descriptor member
    exact descriptorReferencesValid_push heap newObject nextFunctionId descriptor
      (valid.1.1.2 descriptor member)
  · cases prototypeEq : object.prototype with
    | none => rfl
    | some prototype =>
        simp only [prototypeEq] at valid ⊢
        simp [size] at valid ⊢
        omega
  · cases kindEq : object.kind with
    | ordinary => simpa [kindEq] using valid.2
    | array slots => simpa [kindEq] using valid.2
    | primitiveWrapper slots => simpa [kindEq] using valid.2
    | function slots =>
        simp only [kindEq] at valid ⊢
        unfold functionSlotsValid at valid ⊢
        simp only [Bool.and_eq_true] at valid ⊢
        refine ⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, valid.2.1.1.1.2⟩,
          valid.2.1.1.2⟩, valid.2.1.2⟩, valid.2.2⟩
        · simp [functionCount] at valid ⊢
          omega
        · cases homeEq : slots.homeObject with
          | none => rfl
          | some home =>
              simp only [homeEq] at valid ⊢
              simp [size] at valid ⊢
              omega
        · cases lexicalEq : slots.lexicalThis with
          | none => rfl
          | some value =>
              simp only [lexicalEq] at valid ⊢
              exact valueValid_push heap newObject nextFunctionId value valid.2.1.1.1.1.2
    | arrayIterator slots =>
        simp only [kindEq, arrayIteratorSlotsValid] at valid ⊢
        have targetNe : slots.target.value ≠ heap.objects.size := by
          cases targetFound : heap.objects[slots.target.value]? with
          | none => simp [targetFound] at valid
          | some target =>
              have inBounds := (Array.getElem?_eq_some_iff.mp targetFound).choose
              exact Nat.ne_of_lt inBounds
        simp [Array.getElem?_push, targetNe, valid]

private theorem objectReferencesValid_push_two (heap : Heap) (first second object : ObjectRecord)
    (nextFunctionId : Nat) (countMono : heap.nextFunctionId ≤ nextFunctionId)
    (valid : objectReferencesValid heap object = true) :
    objectReferencesValid
      (.mk ((heap.objects.push first).push second) nextFunctionId) object = true := by
  exact objectReferencesValid_push
    (.mk (heap.objects.push first) nextFunctionId) second object nextFunctionId (Nat.le_refl _)
    (objectReferencesValid_push heap first object nextFunctionId countMono valid)

private theorem prototypeGraphAcyclic_push_two (heap : Heap) (first second : ObjectRecord)
    (nextFunctionId : Nat)
    (referencesValid : ∀ (i : Nat) (object : ObjectRecord),
      heap.objects[i]? = some object →
      object.prototype.all (fun prototype => prototype.value < heap.size) = true)
    (firstPrototypeValid : first.prototype.all
      (fun prototype => prototype.value < heap.size) = true)
    (secondPrototypeValid : second.prototype.all
      (fun prototype => prototype.value < heap.size) = true)
    (valid : heap.prototypeGraphAcyclic = true) :
    prototypeGraphAcyclic
      (.mk ((heap.objects.push first).push second) nextFunctionId) = true := by
  let afterFirst : Heap := .mk (heap.objects.push first) nextFunctionId
  apply prototypeGraphAcyclic_push afterFirst second nextFunctionId
  · intro index object found
    unfold afterFirst at found ⊢
    rw [Array.getElem?_push] at found
    split at found
    · rename_i last
      subst index
      simp at found
      subst object
      cases prototypeEq : first.prototype with
      | none => rfl
      | some prototype =>
          simp only [prototypeEq] at firstPrototypeValid ⊢
          simp [size] at firstPrototypeValid ⊢
          omega
    · rename_i notLast
      have oldValid := referencesValid index object found
      cases prototypeEq : object.prototype with
      | none => rfl
      | some prototype =>
          simp only [prototypeEq] at oldValid ⊢
          simp [size] at oldValid ⊢
          omega
  · cases prototypeEq : second.prototype with
    | none => rfl
    | some prototype =>
        simp only [prototypeEq] at secondPrototypeValid ⊢
        simp [afterFirst, size] at secondPrototypeValid ⊢
        omega
  · exact prototypeGraphAcyclic_push heap first nextFunctionId referencesValid
      firstPrototypeValid valid

/-- Replacing an object without changing its prototype preserves the prototype graph check. -/
theorem prototypeGraphAcyclic_replace (heap next : Heap) (ref : RefId)
    (current replacement : ObjectRecord) (found : heap.get? ref = .ok current)
    (samePrototype : replacement.prototype = current.prototype)
    (replaced : heap.replace ref replacement = .ok next) :
    next.prototypeGraphAcyclic = heap.prototypeGraphAcyclic := by
  apply prototypeGraphAcyclic_prototypeEquivalent
  constructor
  · exact replace_size heap next ref replacement replaced
  · intro index
    unfold replace at replaced
    split at replaced
    · cases replaced
      unfold prototypeAt
      by_cases sameIndex : index = ref.value
      · subst index
        have currentFound : heap.objects[ref.value]? = some current := by
          cases lookup : heap.objects[ref.value]? with
          | none => simp [get?, lookup] at found
          | some object =>
              simp [get?, lookup] at found
              simpa [found] using lookup
        simp [currentFound, samePrototype]
      · simp [Ne.symm sameIndex]
    · contradiction

private def functionIdsSequential : Nat → List FunctionSlots → Bool
  | _, [] => true
  | expected, slots :: rest =>
      slots.functionId.value == expected && functionIdsSequential (expected + 1) rest

/-- Executable complete heap invariant with linear function-identity and prototype-graph passes.
Captured environments are checked by `Machine.isWellFormed`. -/
def isWellFormed (heap : Heap) : Bool :=
  let slots := heap.functionSlotList
  heap.objects.toList.all (objectReferencesValid heap) &&
  functionIdsSequential 0 slots &&
  slots.length == heap.functionCount &&
  heap.prototypeGraphAcyclic

/-- Complete heap validity represented by its executable checker. -/
def WellFormed (heap : Heap) : Prop := heap.isWellFormed = true

private theorem functionIdsSequential_append (expected : Nat) (slots : List FunctionSlots)
    (newSlots : FunctionSlots) (valid : functionIdsSequential expected slots = true)
    (newId : newSlots.functionId.value = expected + slots.length) :
    functionIdsSequential expected (slots ++ [newSlots]) = true := by
  induction slots generalizing expected with
  | nil => simp [functionIdsSequential, newId]
  | cons slot slots ih =>
      simp [functionIdsSequential] at valid ⊢
      refine ⟨valid.1, ih (expected + 1) valid.2 (by simp at newId ⊢; omega)⟩

private theorem appendObject_preserves_wellFormed (heap : Heap) (newObject : ObjectRecord)
    (nextFunctionId : Nat) (valid : heap.WellFormed)
    (countMono : heap.nextFunctionId ≤ nextFunctionId)
    (newPrototypeValid : newObject.prototype.all
      (fun prototype => prototype.value < heap.size) = true)
    (newValid : objectReferencesValid
      (.mk (heap.objects.push newObject) nextFunctionId) newObject = true)
    (idsValid : functionIdsSequential 0
      (functionSlotList (.mk (heap.objects.push newObject) nextFunctionId)) = true)
    (countValid : (functionSlotList (.mk (heap.objects.push newObject) nextFunctionId)).length =
      nextFunctionId) :
    WellFormed (.mk (heap.objects.push newObject) nextFunctionId) := by
  unfold WellFormed isWellFormed at valid ⊢
  simp only [Bool.and_eq_true] at valid ⊢
  refine ⟨⟨⟨?_, idsValid⟩, by simpa [functionCount] using countValid⟩, ?_⟩
  · rw [Array.toList_push, List.all_append, List.all_cons, List.all_nil]
    simp only [Bool.and_true, Bool.and_eq_true]
    refine ⟨?_, newValid⟩
    rw [List.all_eq_true] at valid ⊢
    intro object member
    exact objectReferencesValid_push heap newObject object nextFunctionId countMono
      (valid.1.1.1 object member)
  · apply prototypeGraphAcyclic_push heap newObject nextFunctionId
    · intro index object found
      have objectValid := valid.1.1.1
      rw [List.all_eq_true] at objectValid
      have member : object ∈ heap.objects.toList := by
        rw [Array.mem_toList_iff]
        exact Array.mem_of_getElem? found
      have references := objectValid object member
      unfold objectReferencesValid at references
      simp only [Bool.and_eq_true] at references
      exact references.1.2
    · exact newPrototypeValid
    · exact valid.2

private theorem appendTwoObjects_preserves_wellFormed (heap : Heap)
    (first second : ObjectRecord) (nextFunctionId : Nat) (valid : heap.WellFormed)
    (countMono : heap.nextFunctionId ≤ nextFunctionId)
    (firstPrototypeValid : first.prototype.all
      (fun prototype => prototype.value < heap.size) = true)
    (secondPrototypeValid : second.prototype.all
      (fun prototype => prototype.value < heap.size) = true)
    (firstValid : objectReferencesValid
      (.mk ((heap.objects.push first).push second) nextFunctionId) first = true)
    (secondValid : objectReferencesValid
      (.mk ((heap.objects.push first).push second) nextFunctionId) second = true)
    (idsValid : functionIdsSequential 0
      (functionSlotList (.mk ((heap.objects.push first).push second) nextFunctionId)) = true)
    (countValid :
      (functionSlotList (.mk ((heap.objects.push first).push second) nextFunctionId)).length =
        nextFunctionId) :
    WellFormed (.mk ((heap.objects.push first).push second) nextFunctionId) := by
  unfold WellFormed isWellFormed at valid ⊢
  simp only [Bool.and_eq_true] at valid ⊢
  refine ⟨⟨⟨?_, idsValid⟩, by simpa [functionCount] using countValid⟩, ?_⟩
  · simp only [Array.toList_push, List.all_append, List.all_cons, List.all_nil,
      Bool.and_true, Bool.and_eq_true]
    refine ⟨⟨?_, firstValid⟩, secondValid⟩
    rw [List.all_eq_true] at valid ⊢
    intro object member
    exact objectReferencesValid_push_two heap first second object nextFunctionId countMono
      (valid.1.1.1 object member)
  · apply prototypeGraphAcyclic_push_two heap first second nextFunctionId
    · intro index object found
      have objectValid := valid.1.1.1
      rw [List.all_eq_true] at objectValid
      have member : object ∈ heap.objects.toList := by
        rw [Array.mem_toList_iff]
        exact Array.mem_of_getElem? found
      have references := objectValid object member
      unfold objectReferencesValid at references
      simp only [Bool.and_eq_true] at references
      exact references.1.2
    · exact firstPrototypeValid
    · exact secondPrototypeValid
    · exact valid.2

/-- Exact propositional form of the descriptor-reference clause in `Heap.isWellFormed`. -/
def DescriptorReferencesValid (heap : Heap) (descriptor : PropertyDescriptor) : Prop :=
  descriptorReferencesValid heap descriptor = true

/-- Reference validity for every value and accessor explicitly supplied by a descriptor update. -/
def DescriptorUpdateReferencesValid (heap : Heap) (update : DescriptorUpdate) : Prop :=
  (match update.value with
    | .absent => True
    | .present value => heap.valueValid value = true) ∧
  (match update.get with
    | .absent => True
    | .present getter => getter.all (callableReferenceValid heap) = true) ∧
  (match update.set with
    | .absent => True
    | .present setter => setter.all (callableReferenceValid heap) = true)

private theorem callableReferenceValid_eq_objectKind (heap : Heap) (ref : RefId) :
    callableReferenceValid heap ref =
      match heap.objectKind? ref with
      | some (.function _) => true
      | _ => false := by
  unfold callableReferenceValid isCallable functionSlots? objectKind?
  cases heap.get? ref with
  | error fault => rfl
  | ok object =>
      cases object
      rename_i properties prototype extensible kind
      cases kind <;> rfl

private theorem validateValue_iff_valueValid (heap : Heap) (value : Value) :
    validateValue heap value = .ok () ↔ heap.valueValid value = true := by
  cases value with
  | primitive value => simp [validateValue, valueValid]
  | object ref =>
      unfold validateValue valueValid size get?
      cases found : heap.objects[ref.value]? with
      | none =>
          have outOfBounds : ¬ref.value < heap.objects.size := by
            simpa [Array.getElem?_eq_none_iff] using found
          simp [found, outOfBounds]
      | some object =>
          have inBounds : ref.value < heap.objects.size :=
            (Array.getElem?_eq_some_iff.mp found).choose
          simp [found, inBounds]

private theorem validateAccessor_iff_valid (heap : Heap) (accessor : Option RefId) :
    validateAccessor heap accessor = .ok () ↔
      accessor.all (callableReferenceValid heap) = true := by
  cases accessor with
  | none => simp [validateAccessor]
  | some ref =>
      change validateAccessor heap (some ref) = .ok () ↔
        callableReferenceValid heap ref = true
      rw [callableReferenceValid_eq_objectKind]
      unfold validateAccessor objectKind?
      cases found : heap.get? ref with
      | error fault => simp [found]
      | ok object =>
          cases object
          rename_i properties prototype extensible kind
          cases kind <;> simp [found]

private theorem except_unit_sequence_ok_iff (first second : Except ε Unit) :
    (do
      let _ ← first
      second) = .ok () ↔ first = .ok () ∧ second = .ok () := by
  unfold Bind.bind Except.instMonad Monad.toBind Except.bind
  dsimp
  cases first with
  | error error =>
      simp only
      simp
  | ok value =>
      cases value
      simp only
      simp

private theorem except_pure_unit_ok : (pure () : Except ε Unit) = .ok () := by
  rfl

/-- The descriptor reference validator is sound and complete for its exact logical predicate. -/
theorem validateDescriptorReferences_iff (heap : Heap) (update : DescriptorUpdate) :
    validateDescriptorReferences heap update = .ok () ↔
      DescriptorUpdateReferencesValid heap update := by
  unfold validateDescriptorReferences DescriptorUpdateReferencesValid
  cases valueField : update.value <;> cases getField : update.get <;>
    cases setField : update.set <;>
    simp [valueField, getField, setField, except_unit_sequence_ok_iff,
      except_pure_unit_ok, validateValue_iff_valueValid, validateAccessor_iff_valid]

private theorem optionAll_iff_policy (predicate : α → Bool) (value : Option α) :
    value.all predicate = true ↔
      match value with | none => True | some item => predicate item = true := by
  cases value <;> simp

private theorem fieldOptionAll_iff_policy (predicate : α → Bool)
    (field : FieldUpdate (Option α)) :
    (match field with
      | .absent => True
      | .present value => value.all predicate = true) ↔
    (match field with
      | .absent => True
      | .present value => match value with
        | none => True
        | some item => predicate item = true) := by
  cases field with
  | absent => rfl
  | present value => exact optionAll_iff_policy predicate value

private theorem descriptorReferencesValid_iff_policy (heap : Heap)
    (descriptor : PropertyDescriptor) :
    descriptorReferencesValid heap descriptor = true ↔
      DescriptorUpdate.DescriptorReferencesValid
        (fun value => heap.valueValid value = true)
        (fun ref => callableReferenceValid heap ref = true) descriptor := by
  cases descriptor with
  | data descriptor => rfl
  | accessor descriptor =>
      cases getEq : descriptor.get <;> cases setEq : descriptor.set <;>
        simp [descriptorReferencesValid, DescriptorUpdate.DescriptorReferencesValid,
          getEq, setEq]

private theorem descriptorUpdateReferencesValid_iff_policy (heap : Heap)
    (update : DescriptorUpdate) :
    DescriptorUpdateReferencesValid heap update ↔
      update.ReferencesValid
        (fun value => heap.valueValid value = true)
        (fun ref => callableReferenceValid heap ref = true) := by
  unfold DescriptorUpdateReferencesValid DescriptorUpdate.ReferencesValid
  constructor
  · rintro ⟨valueValid, getValid, setValid⟩
    refine ⟨by simpa only using valueValid, ?_, ?_⟩
    · cases getEq : update.get with
      | absent => trivial
      | present getter =>
          simp only [getEq] at getValid ⊢
          cases getter <;> simp_all
    · cases setEq : update.set with
      | absent => trivial
      | present setter =>
          simp only [setEq] at setValid ⊢
          cases setter <;> simp_all
  · rintro ⟨valueValid, getValid, setValid⟩
    refine ⟨by simpa only using valueValid, ?_, ?_⟩
    · cases getEq : update.get with
      | absent => trivial
      | present getter =>
          simp only [getEq] at getValid ⊢
          cases getter <;> simp_all
    · cases setEq : update.set with
      | absent => trivial
      | present setter =>
          simp only [setEq] at setValid ⊢
          cases setter <;> simp_all

/-- A validated descriptor update preserves value-reference and accessor-callability validity. -/
theorem applyValidatedDescriptor_referencesValid (heap : Heap) (update : DescriptorUpdate)
    (current : Option PropertyDescriptor) (extensible : Bool) (kind : DescriptorKind)
    (descriptor : PropertyDescriptor)
    (currentValid : current.all (descriptorReferencesValid heap) = true)
    (referencesValid : validateDescriptorReferences heap update = .ok ())
    (applied : update.applyValidatedDescriptor current extensible kind = .ok descriptor) :
    descriptorReferencesValid heap descriptor = true := by
  rw [descriptorReferencesValid_iff_policy]
  apply DescriptorUpdate.applyValidatedDescriptor_referencesValid update current extensible kind
    descriptor (fun value => heap.valueValid value = true)
    (fun ref => callableReferenceValid heap ref = true) (by rfl)
  · exact (descriptorUpdateReferencesValid_iff_policy heap update).mp
      ((validateDescriptorReferences_iff heap update).mp referencesValid)
  · cases current with
    | none => trivial
    | some current =>
        change descriptorReferencesValid heap current = true at currentValid
        exact (descriptorReferencesValid_iff_policy heap current).mp currentValid
  · exact applied

private theorem callableReferenceValid_replace (heap next : Heap) (target ref : RefId)
    (current replacement : ObjectRecord) (found : heap.get? target = .ok current)
    (sameKind : replacement.kind = current.kind)
    (replaced : heap.replace target replacement = .ok next) :
    callableReferenceValid next ref = callableReferenceValid heap ref := by
  rw [callableReferenceValid_eq_objectKind, callableReferenceValid_eq_objectKind,
    replace_preserves_objectKind heap next target ref current replacement found sameKind replaced]

private theorem descriptorReferencesValid_replace (heap next : Heap) (target : RefId)
    (current replacement : ObjectRecord) (found : heap.get? target = .ok current)
    (sameKind : replacement.kind = current.kind)
    (replaced : heap.replace target replacement = .ok next) (descriptor : PropertyDescriptor) :
    descriptorReferencesValid next descriptor = descriptorReferencesValid heap descriptor := by
  cases descriptor with
  | data descriptor =>
      exact valueValid_replace heap next target replacement replaced descriptor.value
  | accessor descriptor =>
    unfold descriptorReferencesValid
    cases descriptor with
    | mk getter setter enumerable configurable =>
        cases getter <;> cases setter <;>
          simp [callableReferenceValid_replace heap next target _ current replacement found sameKind replaced]

private theorem functionSlotsValid_replace (heap next : Heap) (target : RefId)
    (replacement : ObjectRecord) (replaced : heap.replace target replacement = .ok next)
    (slots : FunctionSlots) : functionSlotsValid next slots = functionSlotsValid heap slots := by
  unfold functionSlotsValid
  rw [replace_functionCount heap next target replacement replaced,
    replace_size heap next target replacement replaced]
  cases slots.lexicalThis <;>
    simp [valueValid_replace heap next target replacement replaced]

private theorem arrayIteratorSlotsValid_replace (heap next : Heap) (target : RefId)
    (current replacement : ObjectRecord) (found : heap.get? target = .ok current)
    (sameKind : replacement.kind = current.kind)
    (replaced : heap.replace target replacement = .ok next) (slots : ArrayIteratorSlots) :
    arrayIteratorSlotsValid next slots = arrayIteratorSlotsValid heap slots := by
  unfold arrayIteratorSlotsValid
  by_cases sameRef : slots.target = target
  · subst target
    have currentFound : heap.objects[slots.target.value]? = some current := by
      cases lookup : heap.objects[slots.target.value]? with
      | none => simp [get?, lookup] at found
      | some object =>
          simp [get?, lookup] at found
          simpa [found] using lookup
    unfold replace at replaced
    split at replaced
    · cases replaced
      simp [currentFound, sameKind]
    · contradiction
  · have differentIndex : slots.target.value ≠ target.value := by
      intro equal
      apply sameRef
      cases slots with
      | mk iteratorTarget nextIndex done =>
          cases iteratorTarget
          cases target
          simp_all
    unfold replace at replaced
    split at replaced
    · cases replaced
      simp [Ne.symm differentIndex]
    · contradiction

private theorem objectReferencesValid_replace_heap (heap next : Heap) (target : RefId)
    (current replacement object : ObjectRecord) (found : heap.get? target = .ok current)
    (sameKind : replacement.kind = current.kind)
    (replaced : heap.replace target replacement = .ok next)
    (valid : objectReferencesValid heap object = true) :
    objectReferencesValid next object = true := by
  unfold objectReferencesValid at valid ⊢
  simp only [Bool.and_eq_true] at valid ⊢
  refine ⟨⟨⟨valid.1.1.1, ?_⟩, ?_⟩, ?_⟩
  · rw [List.all_eq_true] at valid ⊢
    intro descriptor member
    rw [descriptorReferencesValid_replace heap next target current replacement found sameKind replaced]
    exact valid.1.1.2 descriptor member
  · simpa [replace_size heap next target replacement replaced] using valid.1.2
  ·
    cases kindEq : object.kind with
    | ordinary => simpa [kindEq] using valid.2
    | function slots =>
        simp only [kindEq] at valid ⊢
        rw [functionSlotsValid_replace heap next target replacement replaced slots]
        exact valid.2
    | array slots => simpa [kindEq] using valid.2
    | arrayIterator slots =>
        simp only [kindEq] at valid ⊢
        rw [arrayIteratorSlotsValid_replace heap next target current replacement found sameKind replaced slots]
        exact valid.2
    | primitiveWrapper slots => simpa [kindEq] using valid.2

private theorem functionSlotList_replace (heap next : Heap) (target : RefId)
    (current replacement : ObjectRecord) (found : heap.get? target = .ok current)
    (sameKind : replacement.kind = current.kind)
    (replaced : heap.replace target replacement = .ok next) :
    next.functionSlotList = heap.functionSlotList := by
  unfold replace at replaced
  split at replaced
  · cases replaced
    unfold functionSlotList
    rw [Array.toList_set]
    have atTarget : heap.objects.toList[target.value]? = some current := by
      cases lookup : heap.objects[target.value]? with
      | none => simp [get?, lookup] at found
      | some object =>
          simp [get?, lookup] at found
          simpa [found] using lookup
    have mapped : (match replacement.kind with
        | .function slots => some slots
        | _ => none) =
      (match current.kind with
        | .function slots => some slots
        | _ => none) := by rw [sameKind]
    let index := target.value
    change List.filterMap _ (heap.objects.toList.set index replacement) = _
    have atIndex : heap.objects.toList[index]? = some current := by simpa [index] using atTarget
    let project : ObjectRecord → Option FunctionSlots := fun object => match object.kind with
      | .ordinary | .array _ | .arrayIterator _ | .primitiveWrapper _ => none
      | .function slots => some slots
    have go : ∀ (objects : List ObjectRecord) (index : Nat),
        objects[index]? = some current →
        List.filterMap project (objects.set index replacement) = List.filterMap project objects := by
      intro objects index atIndex
      induction objects generalizing index with
      | nil => simp at atIndex
      | cons head tail ih =>
          cases index with
          | zero =>
              simp at atIndex
              subst head
              simp only [List.set, List.filterMap_cons]
              rw [show project replacement = project current by
                unfold project
                rw [sameKind]]
          | succ index =>
              simp only [List.getElem?_cons_succ] at atIndex
              simp only [List.set, List.filterMap_cons]
              rw [ih index atIndex]
    simpa [project] using go heap.objects.toList index atIndex
  · contradiction

/-- Replacing one object with a valid record of the same kind and prototype preserves the complete
heap invariant. -/
theorem replace_preserves_wellFormed (heap next : Heap) (target : RefId)
    (current replacement : ObjectRecord) (valid : heap.WellFormed)
    (found : heap.get? target = .ok current) (sameKind : replacement.kind = current.kind)
    (samePrototype : replacement.prototype = current.prototype)
    (replaced : heap.replace target replacement = .ok next)
    (replacementValid : objectReferencesValid next replacement = true) : next.WellFormed := by
  unfold WellFormed isWellFormed at valid ⊢
  simp only [Bool.and_eq_true] at valid ⊢
  have slotsEqual := functionSlotList_replace heap next target current replacement found sameKind replaced
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  ·
    unfold replace at replaced
    split at replaced
    · cases replaced
      rw [Array.toList_set]
      let concrete : Heap :=
        { objects := heap.objects.set target.value replacement ‹_›,
          nextFunctionId := heap.nextFunctionId }
      have atTarget : heap.objects.toList[target.value]? = some current := by
        cases lookup : heap.objects[target.value]? with
        | none => simp [get?, lookup] at found
        | some object =>
            simp [get?, lookup] at found
            simpa [found] using lookup
      have preserveOld : ∀ object, objectReferencesValid heap object = true →
          objectReferencesValid concrete object = true := by
        intro object objectValid
        exact objectReferencesValid_replace_heap heap concrete target current replacement object
          found sameKind (by
            unfold replace
            simp [concrete, ‹target.value < heap.objects.size›]) objectValid
      have go : ∀ (objects : List ObjectRecord) (index : Nat),
          objects[index]? = some current →
          objects.all (objectReferencesValid heap) = true →
          (objects.set index replacement).all (objectReferencesValid concrete) = true := by
        intro objects index atIndex objectsValid
        induction objects generalizing index with
        | nil => simp at atIndex
        | cons head tail ih =>
            rw [List.all_cons] at objectsValid
            have validParts : objectReferencesValid heap head = true ∧
                tail.all (objectReferencesValid heap) = true := by
              simpa only [Bool.and_eq_true] using objectsValid
            cases index with
            | zero =>
                simp at atIndex
                subst head
                rw [List.set, List.all_cons]
                simpa only [Bool.and_eq_true] using And.intro replacementValid
                  (List.all_eq_true.mpr fun object member =>
                    preserveOld object (List.all_eq_true.mp validParts.2 object member))
            | succ index =>
                simp only [List.getElem?_cons_succ] at atIndex
                rw [List.set, List.all_cons]
                simpa only [Bool.and_eq_true] using And.intro (preserveOld head validParts.1)
                  (ih index atIndex validParts.2)
      exact go heap.objects.toList target.value atTarget valid.1.1.1
    · contradiction
  · rw [slotsEqual]
    exact valid.1.1.2
  · rw [slotsEqual, replace_functionCount heap next target replacement replaced]
    exact valid.1.2
  · rw [prototypeGraphAcyclic_replace heap next target current replacement found samePrototype replaced]
    exact valid.2

private theorem wellFormed_object (heap : Heap) (ref : RefId) (object : ObjectRecord)
    (valid : heap.WellFormed) (found : heap.get? ref = .ok object) :
    objectReferencesValid heap object = true := by
  unfold WellFormed isWellFormed at valid
  simp only [Bool.and_eq_true] at valid
  rw [List.all_eq_true] at valid
  apply valid.1.1.1 object
  rw [Array.mem_toList_iff]
  cases lookup : heap.objects[ref.value]? with
  | none => simp [get?, lookup] at found
  | some current =>
      simp [get?, lookup] at found
      subst current
      exact Array.mem_of_getElem? lookup

private theorem replaceArrayRecord_preserves_wellFormed (heap next : Heap) (target : RefId)
    (oldProperties newProperties : OrderedProps) (prototype : Option RefId) (extensible : Bool)
    (oldSlots newSlots : ArraySlots) (valid : heap.WellFormed)
    (found : heap.get? target = .ok (.mk oldProperties prototype extensible (.array oldSlots)))
    (propertiesValid : newProperties.WellFormed)
    (descriptorsValid : newProperties.descriptors.all (descriptorReferencesValid heap) = true)
    (replaced : heap.replace target (.mk newProperties prototype extensible (.array newSlots)) =
      .ok next)
    (slotsValid : arraySlotsValid
      (.mk newProperties prototype extensible (.array newSlots)) newSlots = true) :
    next.WellFormed := by
  let current : ObjectRecord := .mk oldProperties prototype extensible (.array oldSlots)
  let replacement : ObjectRecord := .mk newProperties prototype extensible (.array newSlots)
  have sourceValid := wellFormed_object heap target current valid found
  have callablePreserved : ∀ ref,
      callableReferenceValid next ref = callableReferenceValid heap ref := by
    intro ref
    unfold callableReferenceValid isCallable functionSlots?
    by_cases same : ref = target
    · subst ref
      rw [get?_replace_same heap next target replacement replaced, found]
      rfl
    · rw [get?_replace_ne heap next target ref replacement same replaced]
  have descriptorPreserved : ∀ descriptor,
      descriptorReferencesValid next descriptor = descriptorReferencesValid heap descriptor := by
    intro descriptor
    cases descriptor with
    | data descriptor => exact valueValid_replace heap next target replacement replaced descriptor.value
    | accessor descriptor =>
        unfold descriptorReferencesValid
        cases descriptor with
        | mk getter setter enumerable configurable =>
            cases getter <;> cases setter <;> simp [callablePreserved]
  have preserveOld : ∀ object, objectReferencesValid heap object = true →
      objectReferencesValid next object = true := by
    intro object objectValid
    unfold objectReferencesValid at objectValid ⊢
    simp only [Bool.and_eq_true] at objectValid ⊢
    refine ⟨⟨⟨objectValid.1.1.1, ?_⟩, ?_⟩, ?_⟩
    · rw [List.all_eq_true] at objectValid ⊢
      intro descriptor member
      rw [descriptorPreserved]
      exact objectValid.1.1.2 descriptor member
    · simpa [replace_size heap next target replacement replaced] using objectValid.1.2
    · cases kindEq : object.kind with
      | ordinary => simpa [kindEq] using objectValid.2
      | function slots =>
          simp only [kindEq] at objectValid ⊢
          rw [functionSlotsValid_replace heap next target replacement replaced slots]
          exact objectValid.2
      | array slots => simpa [kindEq] using objectValid.2
      | primitiveWrapper slots => simpa [kindEq] using objectValid.2
      | arrayIterator slots =>
          simp only [kindEq, arrayIteratorSlotsValid] at objectValid ⊢
          by_cases same : slots.target = target
          · subst target
            have currentFound : heap.objects[slots.target.value]? = some current := by
              cases lookup : heap.objects[slots.target.value]? with
              | none => simp [get?, lookup] at found
              | some foundObject =>
                  simp [get?, lookup] at found
                  subst foundObject
                  simpa [current] using lookup
            unfold replace at replaced
            split at replaced
            · cases replaced
              simp [currentFound, replacement]
            · contradiction
          · have differentIndex : slots.target.value ≠ target.value := by
              intro equal
              apply same
              cases slots with
              | mk iteratorTarget nextIndex done =>
                  cases iteratorTarget
                  cases target
                  simp_all
            unfold replace at replaced
            split at replaced
            · cases replaced
              simpa [Ne.symm differentIndex] using objectValid.2
            · contradiction
  have replacementValid : objectReferencesValid next replacement = true := by
    dsimp [current] at sourceValid
    dsimp [replacement]
    unfold objectReferencesValid at sourceValid ⊢
    simp only [Bool.and_eq_true] at sourceValid ⊢
    refine ⟨⟨⟨propertiesValid, ?_⟩, ?_⟩, slotsValid⟩
    · rw [List.all_eq_true] at descriptorsValid ⊢
      intro descriptor member
      rw [descriptorPreserved]
      exact descriptorsValid descriptor member
    · simpa [replace_size heap next target replacement replaced] using sourceValid.1.2
  have slotsEqual : next.functionSlotList = heap.functionSlotList := by
    unfold replace at replaced
    split at replaced
    · cases replaced
      unfold functionSlotList
      rw [Array.toList_set]
      have atTarget : heap.objects.toList[target.value]? = some current := by
        cases lookup : heap.objects[target.value]? with
        | none => simp [get?, lookup] at found
        | some object =>
            simp [get?, lookup] at found
            simpa [found] using lookup
      let project : ObjectRecord → Option FunctionSlots := fun object => match object.kind with
        | .ordinary | .array _ | .arrayIterator _ | .primitiveWrapper _ => none
        | .function slots => some slots
      have go : ∀ (objects : List ObjectRecord) (index : Nat),
          objects[index]? = some current →
          List.filterMap project (objects.set index replacement) = List.filterMap project objects := by
        intro objects index atIndex
        induction objects generalizing index with
        | nil => simp at atIndex
        | cons head tail ih =>
            cases index with
            | zero =>
                simp at atIndex
                subst head
                simp [project, current, replacement]
            | succ index =>
                simp only [List.getElem?_cons_succ] at atIndex
                simp only [List.set, List.filterMap_cons]
                rw [ih index atIndex]
      exact go heap.objects.toList target.value atTarget
    · contradiction
  unfold WellFormed isWellFormed at valid ⊢
  simp only [Bool.and_eq_true] at valid ⊢
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · unfold replace at replaced
    split at replaced
    · cases replaced
      rw [Array.toList_set]
      let concrete : Heap :=
        { objects := heap.objects.set target.value replacement ‹_›,
          nextFunctionId := heap.nextFunctionId }
      have atTarget : heap.objects.toList[target.value]? = some current := by
        cases lookup : heap.objects[target.value]? with
        | none => simp [get?, lookup] at found
        | some object =>
            simp [get?, lookup] at found
            simpa [found] using lookup
      have go : ∀ (objects : List ObjectRecord) (index : Nat),
          objects[index]? = some current →
          objects.all (objectReferencesValid heap) = true →
          (objects.set index replacement).all (objectReferencesValid concrete) = true := by
        intro objects index atIndex objectsValid
        induction objects generalizing index with
        | nil => simp at atIndex
        | cons head tail ih =>
            rw [List.all_cons] at objectsValid
            have validParts : objectReferencesValid heap head = true ∧
                tail.all (objectReferencesValid heap) = true := by
              simpa only [Bool.and_eq_true] using objectsValid
            cases index with
            | zero =>
                simp at atIndex
                subst head
                rw [List.set, List.all_cons]
                simpa only [Bool.and_eq_true] using And.intro replacementValid
                  (List.all_eq_true.mpr fun object member =>
                    preserveOld object (List.all_eq_true.mp validParts.2 object member))
            | succ index =>
                simp only [List.getElem?_cons_succ] at atIndex
                rw [List.set, List.all_cons]
                simpa only [Bool.and_eq_true] using And.intro (preserveOld head validParts.1)
                  (ih index atIndex validParts.2)
      exact go heap.objects.toList target.value atTarget valid.1.1.1
    · contradiction
  · rw [slotsEqual]
    exact valid.1.1.2
  · rw [slotsEqual, replace_functionCount heap next target replacement replaced]
    exact valid.1.2
  · rw [prototypeGraphAcyclic_replace heap next target current replacement found rfl replaced]
    exact valid.2

/-- Replacing an array's slots while preserving its stored properties and object metadata preserves
the complete heap invariant when the replacement slots satisfy the full array constraint. -/
theorem replaceArray_preserves_wellFormed (heap next : Heap) (target : RefId)
    (properties : OrderedProps) (prototype : Option RefId) (extensible : Bool)
    (oldSlots newSlots : ArraySlots) (valid : heap.WellFormed)
    (found : heap.get? target = .ok (.mk properties prototype extensible (.array oldSlots)))
    (replaced : heap.replace target (.mk properties prototype extensible (.array newSlots)) =
      .ok next)
    (slotsValid : arraySlotsValid
      (.mk properties prototype extensible (.array newSlots)) newSlots = true) :
    next.WellFormed := by
  have sourceValid := wellFormed_object heap target
    (.mk properties prototype extensible (.array oldSlots)) valid found
  unfold objectReferencesValid at sourceValid
  simp only [Bool.and_eq_true] at sourceValid
  exact replaceArrayRecord_preserves_wellFormed heap next target properties properties prototype
    extensible oldSlots newSlots valid found sourceValid.1.1.1 sourceValid.1.1.2 replaced slotsValid

private theorem replaceArrayPropertiesAndSlots_preserves_wellFormed
    (heap next : Heap) (target : RefId) (oldProperties newProperties : OrderedProps)
    (prototype : Option RefId) (extensible : Bool) (oldSlots newSlots : ArraySlots)
    (valid : heap.WellFormed)
    (found : heap.get? target = .ok (.mk oldProperties prototype extensible (.array oldSlots)))
    (propertiesValid : newProperties.WellFormed)
    (descriptorsValid : newProperties.descriptors.all (descriptorReferencesValid heap) = true)
    (oldSlotsValid : arraySlotsValid
      (.mk newProperties prototype extensible (.array oldSlots)) oldSlots = true)
    (newSlotsValid : arraySlotsValid
      (.mk newProperties prototype extensible (.array newSlots)) newSlots = true)
    (replaced : heap.replace target
      (.mk newProperties prototype extensible (.array newSlots)) = .ok next) :
    next.WellFormed := by
  let middleRecord : ObjectRecord :=
    .mk newProperties prototype extensible (.array oldSlots)
  let finalRecord : ObjectRecord :=
    .mk newProperties prototype extensible (.array newSlots)
  unfold replace at replaced
  split at replaced
  · rename_i inBounds
    cases replaced
    let middle : Heap := .mk (heap.objects.set target.value middleRecord inBounds)
      heap.nextFunctionId
    have middleReplaced : heap.replace target middleRecord = .ok middle := by
      unfold replace
      simp [middle, inBounds]
    have middleFound : middle.get? target = .ok middleRecord :=
      get?_replace_same heap middle target middleRecord middleReplaced
    have finalReplaced : middle.replace target finalRecord =
        .ok (.mk (heap.objects.set target.value finalRecord inBounds) heap.nextFunctionId) := by
      unfold replace
      have middleBound : target.value < middle.objects.size := by
        simpa [middle] using inBounds
      simp [middleBound, middle, finalRecord, Array.set_set, inBounds]
    have middleValid : middle.WellFormed := by
      apply replace_preserves_wellFormed heap middle target
        (.mk oldProperties prototype extensible (.array oldSlots)) middleRecord valid found rfl rfl
        middleReplaced
      have sourceValid := wellFormed_object heap target
        (.mk oldProperties prototype extensible (.array oldSlots)) valid found
      unfold objectReferencesValid at sourceValid ⊢
      simp only [Bool.and_eq_true] at sourceValid ⊢
      refine ⟨⟨⟨propertiesValid, ?_⟩, ?_⟩, oldSlotsValid⟩
      · rw [List.all_eq_true] at descriptorsValid ⊢
        intro descriptor member
        rw [descriptorReferencesValid_replace heap middle target
          (.mk oldProperties prototype extensible (.array oldSlots)) middleRecord found rfl
          middleReplaced]
        exact descriptorsValid descriptor member
      · simpa [replace_size heap middle target middleRecord middleReplaced] using sourceValid.1.2
    exact replaceArray_preserves_wellFormed middle
      (.mk (heap.objects.set target.value finalRecord inBounds) heap.nextFunctionId) target
      newProperties prototype extensible oldSlots newSlots middleValid middleFound finalReplaced
      newSlotsValid
  · contradiction

private theorem blockedArrayShrinkReplacement_preserves_wellFormed
    (heap next : Heap) (target : RefId) (object : ObjectRecord) (oldSlots : ArraySlots)
    (newLength blocked : Nat) (properties : OrderedProps) (lengthWritable : Bool)
    (valid : heap.WellFormed) (found : heap.get? target = .ok object)
    (arrayKind : object.kind = .array oldSlots)
    (swept : deleteArrayIndicesFrom object.properties newLength = (some blocked, properties))
    (replaced : heap.replace target
      (.mk properties object.prototype object.extensible
        (.array ⟨blocked + 1, lengthWritable⟩)) = .ok next) : next.WellFormed := by
  have sourceValid := wellFormed_object heap target object valid found
  unfold objectReferencesValid at sourceValid
  simp only [Bool.and_eq_true] at sourceValid
  have oldPropertiesValid : object.properties.WellFormed := sourceValid.1.1.1
  have propertiesValid := deleteArrayIndicesFrom_wellFormed object.properties newLength
    oldPropertiesValid
  rw [swept] at propertiesValid
  have descriptorsValid := deleteArrayIndicesFrom_descriptors_all object.properties newLength
    (descriptorReferencesValid heap) oldPropertiesValid sourceValid.1.1.2
  rw [swept] at descriptorsValid
  have oldArrayValid : arraySlotsValid object oldSlots = true := by
    simpa [arrayKind] using sourceValid.2
  unfold arraySlotsValid at oldArrayValid
  simp only [Bool.and_eq_true] at oldArrayValid
  have lookupSpec := deleteArrayIndicesFrom_blocked_lookups object.properties properties
    newLength blocked oldPropertiesValid swept
  have blockedSpec := deleteArrayIndicesFrom_blocked object.properties properties
    newLength blocked oldPropertiesValid swept
  have blockedFound := blockedSpec.2.2.choose_spec.1
  have blockedOldBound := OrderedProps.key_of_lookup_satisfies object.properties
    (fun key => match arrayIndexOfKey? key with
      | some index => index < oldSlots.length
      | none => key != lengthPropertyKey)
    oldArrayValid.2 (.string (PropertyKey.arrayIndexString blocked)) _ blockedFound
  change (match PropertyKey.arrayIndex? (PropertyKey.arrayIndexString blocked) with
    | some index => index < oldSlots.length
    | none => PropertyKey.string (PropertyKey.arrayIndexString blocked) != lengthPropertyKey) = true
    at blockedOldBound
  rw [blockedSpec.2.1] at blockedOldBound
  simp only at blockedOldBound
  have blockedLt : blocked < oldSlots.length := by simpa using blockedOldBound
  have oldLengthBound : oldSlots.length ≤ maxArrayLength := by simpa using oldArrayValid.1
  have oldSlotsForProperties : arraySlotsValid
      (.mk properties object.prototype object.extensible (.array oldSlots)) oldSlots = true := by
    unfold arraySlotsValid
    simp only [Bool.and_eq_true]
    refine ⟨oldArrayValid.1, OrderedProps.keysAll_of_lookup properties _ ?_⟩
    intro key descriptor finalFound
    have oldFound := deleteArrayIndicesFrom_lookup_some object.properties newLength
      oldPropertiesValid key descriptor (by rw [swept]; exact finalFound)
    exact OrderedProps.key_of_lookup_satisfies object.properties _ oldArrayValid.2 key descriptor oldFound
  have newSlotsValid : arraySlotsValid
      (.mk properties object.prototype object.extensible
        (.array ⟨blocked + 1, lengthWritable⟩)) ⟨blocked + 1, lengthWritable⟩ = true := by
    unfold arraySlotsValid
    simp only [Bool.and_eq_true]
    refine ⟨by simp; omega, OrderedProps.keysAll_of_lookup properties _ ?_⟩
    intro key descriptor finalFound
    cases parsed : arrayIndexOfKey? key with
    | none =>
        have oldFound := deleteArrayIndicesFrom_lookup_some object.properties newLength
          oldPropertiesValid key descriptor (by rw [swept]; exact finalFound)
        simpa [parsed] using OrderedProps.key_of_lookup_satisfies object.properties _
          oldArrayValid.2 key descriptor oldFound
    | some index =>
        by_cases above : blocked < index
        · have oldFound := deleteArrayIndicesFrom_lookup_some object.properties newLength
            oldPropertiesValid key descriptor (by rw [swept]; exact finalFound)
          have absent := (lookupSpec.1 key index descriptor parsed oldFound above).2
          rw [finalFound] at absent
          contradiction
        · simp [parsed]
          omega
  apply replaceArrayPropertiesAndSlots_preserves_wellFormed heap next target object.properties
    properties object.prototype object.extensible oldSlots ⟨blocked + 1, lengthWritable⟩ valid
  · have objectEq : ObjectRecord.mk object.properties object.prototype object.extensible
        (.array oldSlots) = object := by
      cases object
      simp_all
    rw [objectEq]
    exact found
  · exact propertiesValid
  · exact descriptorsValid
  · exact oldSlotsForProperties
  · exact newSlotsValid
  · exact replaced

private theorem unblockedArrayShrinkReplacement_preserves_wellFormed
    (heap next : Heap) (target : RefId) (object : ObjectRecord) (oldSlots : ArraySlots)
    (newLength : Nat) (properties : OrderedProps) (lengthWritable : Bool)
    (valid : heap.WellFormed) (found : heap.get? target = .ok object)
    (arrayKind : object.kind = .array oldSlots)
    (shrink : newLength < oldSlots.length)
    (swept : deleteArrayIndicesFrom object.properties newLength = (none, properties))
    (replaced : heap.replace target
      (.mk properties object.prototype object.extensible
        (.array ⟨newLength, lengthWritable⟩)) = .ok next) : next.WellFormed := by
  have sourceValid := wellFormed_object heap target object valid found
  unfold objectReferencesValid at sourceValid
  simp only [Bool.and_eq_true] at sourceValid
  have oldPropertiesValid : object.properties.WellFormed := sourceValid.1.1.1
  have propertiesValid := deleteArrayIndicesFrom_wellFormed object.properties newLength
    oldPropertiesValid
  rw [swept] at propertiesValid
  have descriptorsValid := deleteArrayIndicesFrom_descriptors_all object.properties newLength
    (descriptorReferencesValid heap) oldPropertiesValid sourceValid.1.1.2
  rw [swept] at descriptorsValid
  have oldArrayValid : arraySlotsValid object oldSlots = true := by
    simpa [arrayKind] using sourceValid.2
  unfold arraySlotsValid at oldArrayValid
  simp only [Bool.and_eq_true] at oldArrayValid
  have oldLengthBound : oldSlots.length ≤ maxArrayLength := by simpa using oldArrayValid.1
  have oldSlotsForProperties : arraySlotsValid
      (.mk properties object.prototype object.extensible (.array oldSlots)) oldSlots = true := by
    unfold arraySlotsValid
    simp only [Bool.and_eq_true]
    refine ⟨oldArrayValid.1, OrderedProps.keysAll_of_lookup properties _ ?_⟩
    intro key descriptor finalFound
    have oldFound := deleteArrayIndicesFrom_lookup_some object.properties newLength
      oldPropertiesValid key descriptor (by rw [swept]; exact finalFound)
    exact OrderedProps.key_of_lookup_satisfies object.properties _ oldArrayValid.2 key descriptor oldFound
  have newSlotsValid : arraySlotsValid
      (.mk properties object.prototype object.extensible
        (.array ⟨newLength, lengthWritable⟩)) ⟨newLength, lengthWritable⟩ = true := by
    unfold arraySlotsValid
    simp only [Bool.and_eq_true]
    refine ⟨by simp; omega, OrderedProps.keysAll_of_lookup properties _ ?_⟩
    intro key descriptor finalFound
    cases parsed : arrayIndexOfKey? key with
    | none =>
        have oldFound := deleteArrayIndicesFrom_lookup_some object.properties newLength
          oldPropertiesValid key descriptor (by rw [swept]; exact finalFound)
        simpa [parsed] using OrderedProps.key_of_lookup_satisfies object.properties _
          oldArrayValid.2 key descriptor oldFound
    | some index =>
        by_cases atLeast : newLength ≤ index
        · have oldFound := deleteArrayIndicesFrom_lookup_some object.properties newLength
            oldPropertiesValid key descriptor (by rw [swept]; exact finalFound)
          have absent := (deleteArrayIndicesFrom_unblocked object.properties properties newLength
            oldPropertiesValid swept key index descriptor parsed oldFound atLeast).2
          rw [finalFound] at absent
          contradiction
        · simp [parsed]
          omega
  apply replaceArrayPropertiesAndSlots_preserves_wellFormed heap next target object.properties
    properties object.prototype object.extensible oldSlots ⟨newLength, lengthWritable⟩ valid
  · have objectEq : ObjectRecord.mk object.properties object.prototype object.extensible
        (.array oldSlots) = object := by
      cases object
      simp_all
    rw [objectEq]
    exact found
  · exact propertiesValid
  · exact descriptorsValid
  · exact oldSlotsForProperties
  · exact newSlotsValid
  · exact replaced

private theorem ordinaryDefineValidated_preserves_wellFormed
    (heap next : Heap) (ref : RefId) (object : ObjectRecord) (key : PropertyKey)
    (update : DescriptorUpdate) (kind : DescriptorKind) (success : Bool)
    (valid : heap.WellFormed) (found : heap.get? ref = .ok object)
    (referencesValid : validateDescriptorReferences heap update = .ok ())
    (keyValid : (match object.kind with
      | .array slots => match arrayIndexOfKey? key with
          | some index => index < slots.length
          | none => key != lengthPropertyKey
      | .primitiveWrapper slots => (syntheticWrapperDescriptor? slots key).isNone
      | _ => true) = true)
    (defined : ordinaryDefineValidated heap ref object key update kind = .ok (success, next)) :
    next.WellFormed := by
  unfold ordinaryDefineValidated at defined
  cases applied : update.applyValidatedDescriptor (object.properties.lookup key)
      object.extensible kind with
  | error rejection =>
      simp [applied] at defined
      obtain ⟨rfl, rfl⟩ := defined
      exact valid
  | ok descriptor =>
      simp only [applied] at defined
      cases replaced : heap.replace ref
          { object with properties := object.properties.insert key descriptor } with
      | error fault =>
          rw [replaced] at defined
          contradiction
      | ok replacedHeap =>
          simp [replaced] at defined
          obtain ⟨rfl, rfl⟩ := defined
          apply replace_preserves_wellFormed heap next ref object
            { object with properties := object.properties.insert key descriptor }
            valid found rfl rfl replaced
          have sourceValid := wellFormed_object heap ref object valid found
          unfold objectReferencesValid at sourceValid ⊢
          simp only [Bool.and_eq_true] at sourceValid ⊢
          have currentValid : (object.properties.lookup key).all
              (descriptorReferencesValid heap) = true := by
            cases lookup : object.properties.lookup key with
            | none => rfl
            | some current =>
                exact OrderedProps.descriptor_of_lookup_satisfies object.properties
                  (descriptorReferencesValid heap) sourceValid.1.1.2 key current lookup
          have descriptorValid := applyValidatedDescriptor_referencesValid heap update
            (object.properties.lookup key) object.extensible kind descriptor currentValid
            referencesValid applied
          refine ⟨⟨⟨OrderedProps.insert_wellFormed object.properties key descriptor
            sourceValid.1.1.1, ?_⟩, ?_⟩, ?_⟩
          · have descriptorsValid := OrderedProps.descriptors_all_insert object.properties key
              descriptor (descriptorReferencesValid heap) sourceValid.1.1.2 descriptorValid
            rw [List.all_eq_true] at descriptorsValid ⊢
            intro stored member
            rw [descriptorReferencesValid_replace heap next ref object
              { object with properties := object.properties.insert key descriptor }
              found rfl replaced]
            exact descriptorsValid stored member
          · simpa [replace_size heap next ref
              { object with properties := object.properties.insert key descriptor } replaced]
              using sourceValid.1.2
          · cases kindEq : object.kind with
            | ordinary => rfl
            | function slots =>
                simp only [kindEq] at sourceValid ⊢
                rw [functionSlotsValid_replace heap next ref
                  { object with properties := object.properties.insert key descriptor }
                  replaced slots]
                exact sourceValid.2
            | array slots =>
                simp only [kindEq, arraySlotsValid, Bool.and_eq_true] at sourceValid ⊢
                exact ⟨sourceValid.2.1, OrderedProps.keysAll_insert object.properties key
                  descriptor _ sourceValid.2.2 (by simpa [kindEq] using keyValid)⟩
            | arrayIterator slots =>
                simp only [kindEq] at sourceValid ⊢
                rw [arrayIteratorSlotsValid_replace heap next ref object
                  { object with properties := object.properties.insert key descriptor }
                  found rfl replaced slots]
                exact sourceValid.2
            | primitiveWrapper slots =>
                simp only [kindEq, primitiveWrapperSlotsValid, Bool.and_eq_true]
                  at sourceValid ⊢
                exact ⟨sourceValid.2.1, OrderedProps.keysAll_insert object.properties key
                  descriptor _ sourceValid.2.2 (by simpa [kindEq] using keyValid)⟩

private theorem replace_same_ref_twice (heap middle next : Heap) (ref : RefId)
    (first second : ObjectRecord) (firstReplaced : heap.replace ref first = .ok middle)
    (secondReplaced : middle.replace ref second = .ok next) :
    heap.replace ref second = .ok next := by
  unfold replace at firstReplaced
  split at firstReplaced
  · rename_i inBounds
    cases firstReplaced
    unfold replace at secondReplaced ⊢
    simp [inBounds, Array.set_set] at secondReplaced ⊢
    exact secondReplaced
  · contradiction

private theorem validArrayLength?_bound (number : JSNumber) (length : Nat)
    (decoded : validArrayLength? number = some length) : length ≤ maxArrayLength := by
  unfold validArrayLength? at decoded
  dsimp only at decoded
  split at decoded
  all_goals repeat first | split at decoded
  all_goals simp_all [maxArrayLength]
  all_goals omega

private theorem requestedArrayLength_bound (slots : ArraySlots) (update normalized : DescriptorUpdate)
    (newLength : Nat) (oldBound : slots.length ≤ maxArrayLength)
    (requested : (match update.value with
      | .absent => Except.ok (slots.length, update)
      | .present (.primitive (.number number)) =>
          match validArrayLength? number with
          | some length => Except.ok (length, { update with
              value := .present (.primitive (.number (arrayLengthNumber length))) })
          | none => Except.error (DefinePropertyFault.invalidArrayLength number)
      | .present value => Except.error (DefinePropertyFault.invalidArrayLengthValue value)) =
        Except.ok (newLength, normalized)) : newLength ≤ maxArrayLength := by
  cases valueField : update.value with
  | absent =>
      simp [valueField] at requested
      obtain ⟨rfl, rfl⟩ := requested
      exact oldBound
  | present value =>
      cases value with
      | object ref => simp [valueField] at requested
      | primitive primitive =>
          cases primitive <;> simp [valueField] at requested
          rename_i number
          cases decoded : validArrayLength? number with
          | none => simp [decoded] at requested
          | some length =>
              simp [decoded] at requested
              obtain ⟨rfl, rfl⟩ := requested
              exact validArrayLength?_bound number length decoded

private theorem arrayPropertyReplacement_preserves_wellFormed
    (heap next : Heap) (ref : RefId) (properties : OrderedProps)
    (prototype : Option RefId) (extensible : Bool) (oldSlots newSlots : ArraySlots)
    (key : PropertyKey) (update : DescriptorUpdate) (kind : DescriptorKind)
    (descriptor : PropertyDescriptor) (valid : heap.WellFormed)
    (found : heap.get? ref = .ok (.mk properties prototype extensible (.array oldSlots)))
    (referencesValid : validateDescriptorReferences heap update = .ok ())
    (applied : update.applyValidatedDescriptor (properties.lookup key) extensible kind =
      .ok descriptor)
    (keyValid : (match arrayIndexOfKey? key with
      | some index => index < newSlots.length
      | none => key != lengthPropertyKey) = true)
    (lengthMono : oldSlots.length ≤ newSlots.length)
    (lengthValid : newSlots.length ≤ maxArrayLength)
    (replaced : heap.replace ref
      (.mk (properties.insert key descriptor) prototype extensible (.array newSlots)) = .ok next) :
    next.WellFormed := by
  have sourceValid := wellFormed_object heap ref
    (.mk properties prototype extensible (.array oldSlots)) valid found
  unfold objectReferencesValid at sourceValid
  simp only [Bool.and_eq_true] at sourceValid
  have oldSlotsValid := sourceValid.2
  unfold arraySlotsValid at oldSlotsValid
  simp only [Bool.and_eq_true] at oldSlotsValid
  have currentValid : (properties.lookup key).all (descriptorReferencesValid heap) = true := by
    cases lookup : properties.lookup key with
    | none => rfl
    | some current =>
        exact OrderedProps.descriptor_of_lookup_satisfies properties
          (descriptorReferencesValid heap) sourceValid.1.1.2 key current lookup
  have descriptorValid := applyValidatedDescriptor_referencesValid heap update
    (properties.lookup key) extensible kind descriptor currentValid referencesValid applied
  have oldKeysValid : properties.keysAll (fun key =>
      match arrayIndexOfKey? key with
      | some index => index < newSlots.length
      | none => key != lengthPropertyKey) = true := by
    apply OrderedProps.keysAll_of_lookup
    intro observed stored storedFound
    have oldKey := OrderedProps.key_of_lookup_satisfies properties (fun key =>
      match arrayIndexOfKey? key with
      | some index => index < oldSlots.length
      | none => key != lengthPropertyKey) oldSlotsValid.2 observed stored storedFound
    cases parsed : arrayIndexOfKey? observed with
    | none => simpa [parsed] using oldKey
    | some index =>
        simp [parsed] at oldKey ⊢
        omega
  apply replaceArrayRecord_preserves_wellFormed heap next ref properties
    (properties.insert key descriptor) prototype extensible oldSlots newSlots valid found
  · exact OrderedProps.insert_wellFormed properties key descriptor sourceValid.1.1.1
  · exact OrderedProps.descriptors_all_insert properties key descriptor
      (descriptorReferencesValid heap) sourceValid.1.1.2 descriptorValid
  · exact replaced
  · unfold arraySlotsValid
    simp only [Bool.and_eq_true]
    exact ⟨by simpa, OrderedProps.keysAll_insert properties key descriptor _
      oldKeysValid keyValid⟩

private theorem arrayLengthReplacement_preserves_wellFormed
    (heap next : Heap) (ref : RefId) (properties : OrderedProps)
    (prototype : Option RefId) (extensible : Bool) (oldSlots newSlots : ArraySlots)
    (valid : heap.WellFormed)
    (found : heap.get? ref = .ok (.mk properties prototype extensible (.array oldSlots)))
    (lengthMono : oldSlots.length ≤ newSlots.length)
    (lengthValid : newSlots.length ≤ maxArrayLength)
    (replaced : heap.replace ref (.mk properties prototype extensible (.array newSlots)) =
      .ok next) : next.WellFormed := by
  have sourceValid := wellFormed_object heap ref
    (.mk properties prototype extensible (.array oldSlots)) valid found
  unfold objectReferencesValid arraySlotsValid at sourceValid
  simp only [Bool.and_eq_true] at sourceValid
  apply replaceArray_preserves_wellFormed heap next ref properties prototype extensible
    oldSlots newSlots valid found replaced
  unfold arraySlotsValid
  simp only [Bool.and_eq_true]
  refine ⟨by simpa, OrderedProps.keysAll_of_lookup properties _ ?_⟩
  intro key descriptor descriptorFound
  have oldKey := OrderedProps.key_of_lookup_satisfies properties (fun key =>
    match arrayIndexOfKey? key with
    | some index => index < oldSlots.length
    | none => key != lengthPropertyKey) sourceValid.2.2 key descriptor descriptorFound
  cases parsed : arrayIndexOfKey? key with
  | none => simpa [parsed] using oldKey
  | some index =>
      simp [parsed] at oldKey ⊢
      omega

private theorem defineArrayLength_preserves_wellFormed
    (heap next : Heap) (ref : RefId) (properties : OrderedProps)
    (prototype : Option RefId) (extensible : Bool) (slots : ArraySlots)
    (update : DescriptorUpdate) (kind : DescriptorKind) (success : Bool)
    (valid : heap.WellFormed)
    (found : heap.get? ref = .ok (.mk properties prototype extensible (.array slots)))
    (defined : defineArrayLength heap ref
      (.mk properties prototype extensible (.array slots)) slots update kind = .ok (success, next)) :
    next.WellFormed := by
  unfold defineArrayLength at defined
  let requestedLength : Except DefinePropertyFault (Nat × DescriptorUpdate) :=
    match update.value with
    | .absent => .ok (slots.length, update)
    | .present (.primitive (.number number)) =>
        match validArrayLength? number with
        | some length => .ok (length, { update with
            value := .present (.primitive (.number (arrayLengthNumber length))) })
        | none => .error (.invalidArrayLength number)
    | .present value => .error (.invalidArrayLengthValue value)
  change (match requestedLength with
    | Except.error fault => Except.error fault
    | Except.ok (newLength, normalizedUpdate) =>
        match normalizedUpdate.applyValidatedDescriptor
            (some (syntheticLengthDescriptor slots)) true kind with
        | Except.error _ => Except.ok (false, heap)
        | Except.ok (.accessor _) => Except.ok (false, heap)
        | Except.ok (.data descriptor) =>
            if slots.length < newLength then
              (heap.replace ref (.mk properties prototype extensible
                (.array ⟨newLength, descriptor.writable⟩))).mapError DefinePropertyFault.heap
                |>.map fun next => (true, next)
            else if slots.length = newLength then
              (heap.replace ref (.mk properties prototype extensible
                (.array ⟨newLength, descriptor.writable⟩))).mapError DefinePropertyFault.heap
                |>.map fun next => (true, next)
            else if !slots.lengthWritable then .ok (false, heap)
            else
              let deleted := deleteArrayIndicesFrom properties newLength
              match deleted.1 with
              | none =>
                  (heap.replace ref (.mk deleted.2 prototype extensible
                    (.array ⟨newLength, descriptor.writable⟩))).mapError DefinePropertyFault.heap
                    |>.map fun next => (true, next)
              | some blocked =>
                  (heap.replace ref (.mk deleted.2 prototype extensible
                    (.array ⟨blocked + 1, descriptor.writable⟩))).mapError DefinePropertyFault.heap
                    |>.map fun next => (false, next)) = .ok (success, next) at defined
  cases requested : requestedLength with
  | error fault => simp [requested] at defined
  | ok request =>
      rcases request with ⟨newLength, normalizedUpdate⟩
      simp only [requested] at defined
      cases applied : normalizedUpdate.applyValidatedDescriptor
          (some (syntheticLengthDescriptor slots)) true kind with
      | error rejection =>
          simp [applied] at defined
          obtain ⟨rfl, rfl⟩ := defined
          exact valid
      | ok descriptor =>
          rw [applied] at defined
          cases descriptor with
          | accessor descriptor =>
              simp at defined
              obtain ⟨rfl, rfl⟩ := defined
              exact valid
          | data descriptor =>
              simp only at defined
              by_cases grow : slots.length < newLength
              · simp [grow] at defined
                cases replaced : heap.replace ref
                    (.mk properties prototype extensible
                      (.array ⟨newLength, descriptor.writable⟩)) with
                | error fault =>
                    rw [replaced] at defined
                    contradiction
                | ok replacedHeap =>
                    simp [replaced] at defined
                    obtain ⟨rfl, rfl⟩ := defined
                    exact arrayLengthReplacement_preserves_wellFormed heap next ref properties
                      prototype extensible slots ⟨newLength, descriptor.writable⟩ valid found
                      (by simpa using Nat.le_of_lt grow)
                      (by
                        simpa using (requestedArrayLength_bound slots update normalizedUpdate
                          newLength
                          (by
                            have source := wellFormed_object heap ref
                              (.mk properties prototype extensible (.array slots)) valid found
                            unfold objectReferencesValid arraySlotsValid at source
                            simp only [Bool.and_eq_true] at source
                            simpa using source.2.1)
                          (by simpa [requestedLength] using requested))) replaced
              · by_cases equal : slots.length = newLength
                · simp [grow, equal] at defined
                  cases replaced : heap.replace ref
                      (.mk properties prototype extensible
                        (.array ⟨newLength, descriptor.writable⟩)) with
                  | error fault =>
                      rw [replaced] at defined
                      contradiction
                  | ok replacedHeap =>
                      simp [replaced] at defined
                      obtain ⟨rfl, rfl⟩ := defined
                      have oldBound : slots.length ≤ maxArrayLength := by
                        have source := wellFormed_object heap ref
                          (.mk properties prototype extensible (.array slots)) valid found
                        unfold objectReferencesValid arraySlotsValid at source
                        simp only [Bool.and_eq_true] at source
                        simpa using source.2.1
                      exact arrayLengthReplacement_preserves_wellFormed heap next ref properties
                        prototype extensible slots ⟨newLength, descriptor.writable⟩ valid found
                        (by simp [equal]) (by simpa [equal] using oldBound) replaced
                · cases writable : slots.lengthWritable with
                  | false =>
                      simp [grow, equal, writable] at defined
                      obtain ⟨rfl, rfl⟩ := defined
                      exact valid
                  | true =>
                      simp only [grow, equal, writable, Bool.not_true, ↓reduceIte] at defined
                      cases swept : deleteArrayIndicesFrom properties newLength with
                      | mk blocked finalProperties =>
                          cases blocked with
                          | none =>
                              simp only [swept] at defined
                              cases replaced : heap.replace ref
                                  (.mk finalProperties prototype extensible
                                    (.array ⟨newLength, descriptor.writable⟩)) with
                              | error fault =>
                                  rw [replaced] at defined
                                  contradiction
                              | ok replacedHeap =>
                                  simp [replaced] at defined
                                  obtain ⟨rfl, rfl⟩ := defined
                                  exact unblockedArrayShrinkReplacement_preserves_wellFormed
                                    heap next ref (.mk properties prototype extensible (.array slots))
                                    slots newLength finalProperties descriptor.writable valid found rfl
                                    (by omega) swept replaced
                          | some blocked =>
                              simp only [swept] at defined
                              cases replaced : heap.replace ref
                                  (.mk finalProperties prototype extensible
                                    (.array ⟨blocked + 1, descriptor.writable⟩)) with
                              | error fault =>
                                  rw [replaced] at defined
                                  contradiction
                              | ok replacedHeap =>
                                  simp [replaced] at defined
                                  obtain ⟨rfl, rfl⟩ := defined
                                  exact blockedArrayShrinkReplacement_preserves_wellFormed
                                    heap next ref (.mk properties prototype extensible (.array slots))
                                    slots newLength blocked finalProperties descriptor.writable valid
                                    found rfl swept replaced

/-- Every result returned by the public property-definition boundary preserves the complete heap
invariant, including rejected definitions and blocked array-shrink committed deletions. -/
theorem defineOwnProperty_preserves_wellFormed (heap next : Heap) (ref : RefId)
    (key : PropertyKey) (update : DescriptorUpdate) (success : Bool)
    (valid : heap.WellFormed)
    (defined : heap.defineOwnProperty ref key update = .ok (success, next)) : next.WellFormed := by
  unfold defineOwnProperty at defined
  cases found : heap.get? ref with
  | error fault => simp [found] at defined
  | ok object =>
      simp only [found] at defined
      cases syntaxResult : update.validateSyntax with
      | error fault => simp [syntaxResult] at defined
      | ok kind =>
          simp only [syntaxResult] at defined
          cases references : validateDescriptorReferences heap update with
          | error fault => simp [references] at defined
          | ok unit =>
              cases unit
              simp only [references] at defined
              rcases object with ⟨properties, prototype, extensible, objectKind⟩
              cases objectKind with
              | ordinary =>
                  exact ordinaryDefineValidated_preserves_wellFormed heap next ref
                    (.mk properties prototype extensible .ordinary) key update kind success valid
                    found references rfl defined
              | function slots =>
                  exact ordinaryDefineValidated_preserves_wellFormed heap next ref
                    (.mk properties prototype extensible (.function slots)) key update kind success
                    valid found references rfl defined
              | arrayIterator slots =>
                  exact ordinaryDefineValidated_preserves_wellFormed heap next ref
                    (.mk properties prototype extensible (.arrayIterator slots)) key update kind
                    success valid found references rfl defined
              | primitiveWrapper slots =>
                  unfold defineWrapperProperty at defined
                  cases synthetic : syntheticWrapperDescriptor? slots key with
                  | some current =>
                      cases applied : update.applyValidatedDescriptor (some current) true kind with
                      | error rejection =>
                          simp [synthetic, applied] at defined
                          obtain ⟨rfl, rfl⟩ := defined
                          exact valid
                      | ok descriptor =>
                          simp [synthetic, applied] at defined
                          obtain ⟨rfl, rfl⟩ := defined
                          exact valid
                  | none =>
                      apply ordinaryDefineValidated_preserves_wellFormed heap next ref
                        (.mk properties prototype extensible (.primitiveWrapper slots)) key update
                        kind success valid found references
                      · simpa [synthetic]
                      · simpa [synthetic] using defined
              | array slots =>
                  simp only at defined
                  by_cases lengthKey : key == lengthPropertyKey
                  · rw [if_pos lengthKey] at defined
                    exact defineArrayLength_preserves_wellFormed heap next ref properties prototype
                      extensible slots update kind success valid found defined
                  · rw [if_neg lengthKey] at defined
                    cases parsed : arrayIndexOfKey? key with
                    | none =>
                        apply ordinaryDefineValidated_preserves_wellFormed heap next ref
                          (.mk properties prototype extensible (.array slots)) key update kind success
                          valid found references
                        · simp [parsed]
                          intro equal
                          subst key
                          simp at lengthKey
                        · simpa [parsed] using defined
                    | some index =>
                        simp only [parsed] at defined
                        unfold defineArrayIndex at defined
                        by_cases blocked : slots.length ≤ index && !slots.lengthWritable
                        · simp [blocked] at defined
                          obtain ⟨rfl, rfl⟩ := defined
                          exact valid
                        · rw [if_neg blocked] at defined
                          cases ordinary : ordinaryDefineValidated heap ref
                              (.mk properties prototype extensible (.array slots)) key update kind with
                          | error fault => simp [ordinary] at defined
                          | ok result =>
                              rcases result with ⟨ordinarySuccess, middle⟩
                              cases ordinarySuccess with
                              | false =>
                                  simp [ordinary] at defined
                                  obtain ⟨rfl, rfl⟩ := defined
                                  exact valid
                              | true =>
                                  rw [ordinary] at defined
                                  cases applied : update.applyValidatedDescriptor
                                      (properties.lookup key) extensible kind with
                                  | error rejection =>
                                      unfold ordinaryDefineValidated at ordinary
                                      simp [applied] at ordinary
                                  | ok descriptor =>
                                      have firstReplaced : heap.replace ref
                                          (.mk (properties.insert key descriptor) prototype extensible
                                            (.array slots)) = .ok middle := by
                                        unfold ordinaryDefineValidated at ordinary
                                        simp only [applied] at ordinary
                                        cases replaced : heap.replace ref
                                            (.mk (properties.insert key descriptor) prototype extensible
                                              (.array slots)) with
                                        | error fault =>
                                            rw [replaced] at ordinary
                                            contradiction
                                        | ok replacedHeap =>
                                            rw [replaced] at ordinary
                                            change Except.ok (true, replacedHeap) =
                                              Except.ok (true, middle) at ordinary
                                            exact congrArg Except.ok
                                              (congrArg Prod.snd (Except.ok.inj ordinary))
                                      by_cases inBounds : index < slots.length
                                      · simp [inBounds] at defined
                                        obtain ⟨rfl, rfl⟩ := defined
                                        exact ordinaryDefineValidated_preserves_wellFormed heap middle ref
                                          (.mk properties prototype extensible (.array slots)) key
                                          update kind true valid found references
                                          (by simp [parsed, inBounds]) ordinary
                                      · simp only [inBounds, ↓reduceIte] at defined
                                        have middleFound := get?_replace_same heap middle ref
                                          (.mk (properties.insert key descriptor) prototype extensible
                                            (.array slots)) firstReplaced
                                        cases observed : middle.get? ref with
                                        | error fault => simp [observed] at defined
                                        | ok nextObject =>
                                            rw [observed] at defined
                                            simp only at defined
                                            have nextObjectEq : nextObject =
                                                .mk (properties.insert key descriptor) prototype extensible
                                                  (.array slots) := by
                                              rw [observed] at middleFound
                                              exact Except.ok.inj middleFound
                                            subst nextObject
                                            cases finalReplaced : middle.replace ref
                                                (.mk (properties.insert key descriptor) prototype extensible
                                                  (.array ⟨index + 1, slots.lengthWritable⟩)) with
                                            | error fault =>
                                                rw [finalReplaced] at defined
                                                contradiction
                                            | ok finalHeap =>
                                                simp [finalReplaced] at defined
                                                obtain ⟨rfl, rfl⟩ := defined
                                                have directReplaced := replace_same_ref_twice heap middle
                                                  next ref
                                                  (.mk (properties.insert key descriptor) prototype
                                                    extensible (.array slots))
                                                  (.mk (properties.insert key descriptor) prototype
                                                    extensible
                                                    (.array ⟨index + 1, slots.lengthWritable⟩))
                                                  firstReplaced finalReplaced
                                                apply arrayPropertyReplacement_preserves_wellFormed
                                                  heap next ref properties prototype extensible slots
                                                  ⟨index + 1, slots.lengthWritable⟩ key update kind descriptor
                                                  valid found references applied
                                                · simp [parsed]
                                                · simp
                                                  omega
                                                · have indexBound : index ≤ PropertyKey.maxArrayIndex := by
                                                    cases key with
                                                    | symbol symbol => simp [arrayIndexOfKey?] at parsed
                                                    | string stringKey =>
                                                        change PropertyKey.arrayIndex? stringKey = some index
                                                          at parsed
                                                        exact PropertyKey.arrayIndex?_bound parsed
                                                  unfold PropertyKey.maxArrayIndex at indexBound
                                                  unfold maxArrayLength
                                                  simp only
                                                  omega
                                                · exact directReplaced

/-- `createDataProperty` preserves complete heap validity for every returned Boolean result. -/
theorem createDataProperty_preserves_wellFormed (heap next : Heap) (ref : RefId)
    (key : PropertyKey) (value : Value) (success : Bool) (valid : heap.WellFormed)
    (created : heap.createDataProperty ref key value = .ok (success, next)) : next.WellFormed := by
  exact defineOwnProperty_preserves_wellFormed heap next ref key {
    value := .present value
    writable := .present true
    enumerable := .present true
    configurable := .present true
  } success valid created

/-- Making an object nonextensible preserves the complete heap invariant. -/
theorem preventExtensions_preserves_wellFormed (heap next : Heap) (ref : RefId)
    (valid : heap.WellFormed) (updated : heap.preventExtensions ref = .ok next) :
    next.WellFormed := by
  unfold preventExtensions at updated
  cases found : heap.get? ref with
  | error fault => simp [found] at updated
  | ok object =>
      rw [found] at updated
      cases extensible : object.extensible with
      | false =>
          simp [extensible] at updated
          cases updated
          exact valid
      | true =>
          simp [extensible] at updated
          cases replaced : heap.replace ref { object with extensible := false } with
          | error fault => simp [replaced] at updated
          | ok replacedHeap =>
              rw [replaced] at updated
              cases updated
              apply replace_preserves_wellFormed heap next ref object
                { object with extensible := false } valid found rfl rfl replaced
              have oldValid := wellFormed_object heap ref object valid found
              have preserved := objectReferencesValid_replace_heap heap next ref object
                { object with extensible := false } object found rfl replaced oldValid
              simpa [objectReferencesValid] using preserved

private theorem deleteReplacement_referencesValid (heap next : Heap) (ref : RefId)
    (object : ObjectRecord) (key : PropertyKey) (valid : heap.WellFormed)
    (found : heap.get? ref = .ok object)
    (replaced : heap.replace ref { object with properties := object.properties.delete key } =
      .ok next) :
    objectReferencesValid next { object with properties := object.properties.delete key } = true := by
  have sourceValid := wellFormed_object heap ref object valid found
  unfold objectReferencesValid at sourceValid ⊢
  simp only [Bool.and_eq_true] at sourceValid ⊢
  refine ⟨⟨⟨OrderedProps.delete_wellFormed object.properties key sourceValid.1.1.1, ?_⟩,
    ?_⟩, ?_⟩
  · have descriptors := OrderedProps.descriptors_all_delete object.properties key
      (descriptorReferencesValid heap) sourceValid.1.1.1 sourceValid.1.1.2
    rw [List.all_eq_true] at descriptors ⊢
    intro descriptor member
    rw [descriptorReferencesValid_replace heap next ref object
      { object with properties := object.properties.delete key } found rfl replaced]
    exact descriptors descriptor member
  · simpa [replace_size heap next ref
      { object with properties := object.properties.delete key } replaced] using sourceValid.1.2
  · cases kindEq : object.kind with
    | ordinary => simpa [kindEq] using sourceValid.2
    | function slots =>
        simp only [kindEq] at sourceValid ⊢
        rw [functionSlotsValid_replace heap next ref
          { object with properties := object.properties.delete key } replaced slots]
        exact sourceValid.2
    | array slots =>
        simp only [kindEq, arraySlotsValid, Bool.and_eq_true] at sourceValid ⊢
        exact ⟨sourceValid.2.1, OrderedProps.keysAll_delete object.properties key _
          sourceValid.1.1.1 sourceValid.2.2⟩
    | arrayIterator slots =>
        simp only [kindEq] at sourceValid ⊢
        rw [arrayIteratorSlotsValid_replace heap next ref object
          { object with properties := object.properties.delete key } found rfl replaced slots]
        exact sourceValid.2
    | primitiveWrapper slots =>
        simp only [kindEq, primitiveWrapperSlotsValid, Bool.and_eq_true] at sourceValid ⊢
        exact ⟨sourceValid.2.1, OrderedProps.keysAll_delete object.properties key _
          sourceValid.1.1.1 sourceValid.2.2⟩

/-- Every successful property deletion result preserves the complete heap invariant. -/
theorem deleteProperty_preserves_wellFormed (heap next : Heap) (ref : RefId) (key : PropertyKey)
    (success : Bool) (valid : heap.WellFormed)
    (deleted : heap.deleteProperty ref key = .ok (success, next)) : next.WellFormed := by
  unfold deleteProperty at deleted
  cases found : heap.get? ref with
  | error fault => simp [found] at deleted
  | ok object =>
      rw [found] at deleted
      simp_all only [Except.ok.injEq]
      split at deleted
      · cases deleted
        exact valid
      · unfold deleteStoredProperty at deleted
        cases lookup : object.properties.lookup key with
        | none =>
            simp [lookup] at deleted
            cases deleted
            subst next
            exact valid
        | some descriptor =>
            cases descriptor with
            | data descriptor =>
                rw [lookup] at deleted
                cases configurable : descriptor.configurable with
                | false =>
                    simp [configurable] at deleted
                    cases deleted
                    subst next
                    exact valid
                | true =>
                    simp [configurable] at deleted
                    cases replaced : heap.replace ref
                        { object with properties := object.properties.delete key } with
                    | error fault =>
                        rw [replaced] at deleted
                        change Except.error fault = Except.ok (success, next) at deleted
                        contradiction
                    | ok replacedHeap =>
                        rw [replaced] at deleted
                        cases deleted
                        apply replace_preserves_wellFormed heap next ref object
                          { object with properties := object.properties.delete key }
                          valid found rfl rfl replaced
                        exact deleteReplacement_referencesValid heap next ref object key valid found replaced
            | accessor descriptor =>
                rw [lookup] at deleted
                cases configurable : descriptor.configurable with
                | false =>
                    simp [configurable] at deleted
                    cases deleted
                    subst next
                    exact valid
                | true =>
                    simp [configurable] at deleted
                    cases replaced : heap.replace ref
                        { object with properties := object.properties.delete key } with
                    | error fault =>
                        rw [replaced] at deleted
                        change Except.error fault = Except.ok (success, next) at deleted
                        contradiction
                    | ok replacedHeap =>
                        rw [replaced] at deleted
                        cases deleted
                        apply replace_preserves_wellFormed heap next ref object
                          { object with properties := object.properties.delete key }
                          valid found rfl rfl replaced
                        exact deleteReplacement_referencesValid heap next ref object key valid found replaced

/-- A rejected delete preserves complete heap validity because it preserves the heap exactly. -/
theorem failed_delete_preserves_wellFormed
    (heap next : Heap) (ref : RefId) (key : PropertyKey) (valid : heap.WellFormed)
    (rejected : heap.deleteProperty ref key = .ok (false, next)) : next.WellFormed := by
  rw [failed_delete_preserves_heap heap next ref key rejected]
  exact valid

/-- The empty heap satisfies the complete executable invariant. -/
theorem empty_wellFormed : WellFormed empty := by
  rfl

/-- Every successful ordinary allocation preserves the complete heap invariant. -/
theorem allocate_preserves_wellFormed (heap next : Heap) (prototype : Option RefId)
    (extensible : Bool) (ref : RefId) (valid : heap.WellFormed)
    (allocated : heap.allocate prototype extensible = .ok (ref, next)) : next.WellFormed := by
  unfold allocate at allocated
  split at allocated
  · rcases allocated with ⟨rfl, rfl⟩
    apply appendObject_preserves_wellFormed heap
      (.mk OrderedProps.empty prototype extensible .ordinary) heap.nextFunctionId valid
      (by omega)
    · cases prototype <;> simp_all [validPrototype, size]
    · unfold objectReferencesValid
      simp [OrderedProps.empty_wellFormed, size]
      cases prototype <;> simp_all [validPrototype, size] <;> omega
    · unfold functionSlotList
      simp
      unfold WellFormed isWellFormed at valid
      simp only [Bool.and_eq_true] at valid
      exact valid.1.1.2
    · unfold functionSlotList
      simp
      unfold WellFormed isWellFormed at valid
      simp only [Bool.and_eq_true] at valid
      simpa [functionCount] using valid.1.2
  · cases prototype <;> simp_all

/-- Every successful primitive-wrapper allocation preserves the complete heap invariant. -/
theorem allocatePrimitiveWrapper_preserves_wellFormed (heap next : Heap) (value : Primitive)
    (prototype : Option RefId) (ref : RefId) (valid : heap.WellFormed)
    (allocated : heap.allocatePrimitiveWrapper value prototype = .ok (ref, next)) :
    next.WellFormed := by
  unfold allocatePrimitiveWrapper at allocated
  split at allocated <;> try contradiction
  split at allocated
  · rcases allocated with ⟨rfl, rfl⟩
    apply appendObject_preserves_wellFormed heap
      (.mk OrderedProps.empty prototype true (.primitiveWrapper ⟨value⟩))
      heap.nextFunctionId valid (by omega)
    · cases prototype <;> simp_all [validPrototype, size]
    · unfold objectReferencesValid primitiveWrapperSlotsValid
      cases prototype <;> simp_all [validPrototype, primitiveBoxable, size]
      all_goals omega
    · unfold functionSlotList
      simp
      unfold WellFormed isWellFormed at valid
      simp only [Bool.and_eq_true] at valid
      exact valid.1.1.2
    · unfold functionSlotList
      simp
      unfold WellFormed isWellFormed at valid
      simp only [Bool.and_eq_true] at valid
      simpa [functionCount] using valid.1.2
  · cases prototype <;> simp_all

private theorem arrayElementFold_preserves_validity (heap : Heap)
    (elements : List (Option Value)) (index length : Nat) (properties : OrderedProps)
    (propertiesValid : properties.WellFormed)
    (descriptorsValid : properties.descriptors.all (descriptorReferencesValid heap) = true)
    (keysValid : properties.keysAll (fun key =>
      match arrayIndexOfKey? key with
      | some storedIndex => storedIndex < length
      | none => key != lengthPropertyKey) = true)
    (valuesValid : elements.all (fun element => element.all heap.valueValid) = true)
    (lengthBound : length ≤ maxArrayLength)
    (withinLength : index + elements.length ≤ length) :
    let result := elements.foldl (fun state element =>
      let nextIndex := state.1
      let nextProperties := match element with
        | none => state.2
        | some value => state.2.insert (.string (PropertyKey.arrayIndexString nextIndex))
            (.data ⟨value, true, true, true⟩)
      (nextIndex + 1, nextProperties)) (index, properties)
    result.1 = index + elements.length ∧
      result.2.WellFormed ∧
      result.2.descriptors.all (descriptorReferencesValid heap) = true ∧
      result.2.keysAll (fun key =>
        match arrayIndexOfKey? key with
        | some storedIndex => storedIndex < length
        | none => key != lengthPropertyKey) = true := by
  induction elements generalizing index properties with
  | nil => exact ⟨rfl, propertiesValid, descriptorsValid, keysValid⟩
  | cons element rest ih =>
      simp only [List.all_cons, Bool.and_eq_true] at valuesValid
      simp only [List.length_cons] at withinLength
      have restWithin : index + 1 + rest.length ≤ length := by
        omega
      have indexLt : index < length := by omega
      cases element with
      | none =>
          simpa [List.foldl_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            ih (index + 1) properties propertiesValid descriptorsValid keysValid valuesValid.2
              restWithin
      | some value =>
          let key : PropertyKey := .string (PropertyKey.arrayIndexString index)
          let descriptor : PropertyDescriptor := .data ⟨value, true, true, true⟩
          have keyValid : (match arrayIndexOfKey? key with
              | some storedIndex => storedIndex < length
              | none => key != lengthPropertyKey) = true := by
            unfold key arrayIndexOfKey?
            have parsed : PropertyKey.arrayIndex? (PropertyKey.arrayIndexString index) = some index := by
              apply PropertyKey.arrayIndex?_arrayIndexString
              unfold maxArrayLength at lengthBound
              unfold PropertyKey.maxArrayIndex
              omega
            simp [parsed, indexLt]
          have nextPropertiesValid := OrderedProps.insert_wellFormed properties key descriptor
            propertiesValid
          have nextDescriptorsValid := OrderedProps.descriptors_all_insert properties key descriptor
            (descriptorReferencesValid heap) descriptorsValid (by
              simpa [descriptor, descriptorReferencesValid] using valuesValid.1)
          have nextKeysValid := OrderedProps.keysAll_insert properties key descriptor _ keysValid keyValid
          simpa [List.foldl_cons, key, descriptor, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using
            ih (index + 1) (properties.insert key descriptor) nextPropertiesValid
              nextDescriptorsValid nextKeysValid valuesValid.2 restWithin

private theorem arrayInvalidFold_started (heap : Heap) (elements : List (Option Value))
    (ref : RefId) :
    elements.foldl (fun found element =>
      match found, element with
      | some ref, _ => some ref
      | none, some (.object ref) => if ref.value < heap.size then none else some ref
      | none, _ => none) (some ref) = some ref := by
  induction elements with
  | nil => rfl
  | cons element rest ih => simpa [List.foldl_cons] using ih

private theorem arrayInvalidFold_none_valuesValid (heap : Heap)
    (elements : List (Option Value))
    (checked : elements.foldl (fun found element =>
      match found, element with
      | some ref, _ => some ref
      | none, some (.object ref) => if ref.value < heap.size then none else some ref
      | none, _ => none) none = none) :
    elements.all (fun element => element.all heap.valueValid) = true := by
  induction elements with
  | nil => rfl
  | cons element rest ih =>
      cases element with
      | none =>
          simp only [List.foldl_cons] at checked
          simpa [List.all_cons] using ih checked
      | some value =>
          cases value with
          | primitive value =>
              simp only [List.foldl_cons] at checked
              simpa [List.all_cons, valueValid] using ih checked
          | object ref =>
              by_cases inBounds : ref.value < heap.size
              · simp only [List.foldl_cons] at checked
                simp [inBounds] at checked
                have restValid := ih checked
                simp [List.all_cons, valueValid, inBounds, restValid]
              · simp only [List.foldl_cons] at checked
                simp [inBounds, arrayInvalidFold_started heap rest ref] at checked

private theorem appendArray_preserves_wellFormed (heap : Heap)
    (elements : Array (Option Value)) (prototype : Option RefId) (valid : heap.WellFormed)
    (lengthBound : elements.size ≤ maxArrayLength)
    (prototypeValid : prototype.all (fun ref => ref.value < heap.size) = true)
    (valuesValid : elements.toList.all (fun element => element.all heap.valueValid) = true) :
    (appendArray heap prototype elements).2.WellFormed := by
  unfold appendArray
  rw [← Array.foldl_toList]
  let properties := elements.toList.foldl (fun state element =>
    let index := state.1
    let properties := match element with
      | none => state.2
      | some value => state.2.insert (.string (PropertyKey.arrayIndexString index))
          (.data ⟨value, true, true, true⟩)
    (index + 1, properties)) (0, OrderedProps.empty) |>.2
  have folded := arrayElementFold_preserves_validity heap elements.toList 0 elements.size
    OrderedProps.empty OrderedProps.empty_wellFormed (by simp) (by simp) valuesValid
    lengthBound (by simp)
  change WellFormed (.mk (heap.objects.push (.mk properties prototype true
    (.array ⟨elements.size, true⟩))) heap.nextFunctionId)
  apply appendObject_preserves_wellFormed heap
    (.mk properties prototype true (.array ⟨elements.size, true⟩)) heap.nextFunctionId
    valid (by omega) prototypeValid
  · unfold objectReferencesValid arraySlotsValid
    simp only [Bool.and_eq_true]
    refine ⟨⟨⟨folded.2.1, ?_⟩, ?_⟩, (by simpa using lengthBound), folded.2.2.2⟩
    · have oldDescriptors := folded.2.2.1
      rw [List.all_eq_true] at oldDescriptors ⊢
      intro descriptor member
      exact descriptorReferencesValid_push heap
        (.mk properties prototype true (.array ⟨elements.size, true⟩))
        heap.nextFunctionId descriptor (oldDescriptors descriptor member)
    · cases prototype with
      | none => rfl
      | some ref =>
          simp [size] at prototypeValid ⊢
          omega
  · unfold functionSlotList
    simp
    unfold WellFormed isWellFormed at valid
    simp only [Bool.and_eq_true] at valid
    exact valid.1.1.2
  · unfold functionSlotList
    simp
    unfold WellFormed isWellFormed at valid
    simp only [Bool.and_eq_true] at valid
    simpa [functionCount] using valid.1.2

/-- Every successful list-input array allocation preserves the complete heap invariant. -/
theorem allocateArray_preserves_wellFormed (heap next : Heap)
    (elements : List (Option Value)) (prototype : Option RefId) (ref : RefId)
    (valid : heap.WellFormed)
    (allocated : heap.allocateArray elements prototype = .ok (ref, next)) :
    next.WellFormed := by
  unfold allocateArray allocateArrayFromArray at allocated
  split at allocated <;> try contradiction
  cases prototype with
  | none =>
      simp only at allocated
      rw [← Array.foldl_toList] at allocated
      simp only at allocated
      cases invalid : elements.foldl (fun found element =>
        match found, element with
        | some ref, _ => some ref
        | none, some (.object ref) => if ref.value < heap.size then none else some ref
        | none, _ => none) none with
      | some invalidRef => simp [invalid] at allocated
      | none =>
          simp [invalid] at allocated
          rcases allocated with ⟨rfl, rfl⟩
          apply appendArray_preserves_wellFormed heap elements.toArray none valid
            (by simpa using ‹¬elements.length > maxArrayLength›) rfl
          simpa using arrayInvalidFold_none_valuesValid heap elements invalid
  | some prototype =>
      simp only at allocated
      cases prototypeFound : heap.get? prototype with
      | error fault => simp [prototypeFound] at allocated
      | ok object =>
          rw [prototypeFound, ← Array.foldl_toList] at allocated
          simp only at allocated
          cases invalid : elements.foldl (fun found element =>
            match found, element with
            | some ref, _ => some ref
            | none, some (.object ref) => if ref.value < heap.size then none else some ref
            | none, _ => none) none with
          | some invalidRef => simp [prototypeFound, invalid] at allocated
          | none =>
              simp [prototypeFound, invalid] at allocated
              rcases allocated with ⟨rfl, rfl⟩
              have prototypeValid : prototype.value < heap.size := by
                unfold get? at prototypeFound
                cases lookup : heap.objects[prototype.value]? with
                | none => simp [lookup] at prototypeFound
                | some current =>
                    simpa [size] using (Array.getElem?_eq_some_iff.mp lookup).choose
              apply appendArray_preserves_wellFormed heap elements.toArray (some prototype) valid
                (by simpa using ‹¬elements.length > maxArrayLength›) (by simpa)
              simpa using arrayInvalidFold_none_valuesValid heap elements invalid

/-- Every successful array-input allocation preserves the complete heap invariant. -/
theorem allocateArrayFromArray_preserves_wellFormed (heap next : Heap)
    (elements : Array (Option Value)) (prototype : Option RefId) (ref : RefId)
    (valid : heap.WellFormed)
    (allocated : heap.allocateArrayFromArray elements prototype = .ok (ref, next)) :
    next.WellFormed := by
  apply allocateArray_preserves_wellFormed heap next elements.toList prototype ref valid
  simpa [allocateArray] using allocated

private theorem validateOptionalRef_valid (heap : Heap) (ref : Option RefId) (unit : Unit)
    (checked : validateOptionalRef heap ref = .ok unit) :
    ref.all (fun value => value.value < heap.size) = true := by
  cases ref with
  | none => rfl
  | some ref =>
      unfold validateOptionalRef validateRef at checked
      cases found : heap.get? ref with
      | error fault => simp [found] at checked
      | ok object =>
          unfold get? at found
          cases lookup : heap.objects[ref.value]? with
          | none => simp [lookup] at found
          | some current =>
              have inBounds := (Array.getElem?_eq_some_iff.mp lookup).choose
              simpa [size] using inBounds

/-- Every successful function allocation, for every supported metadata mode, preserves the complete
heap invariant. Captured-environment validity remains a machine-layer obligation. -/
theorem allocateFunction_preserves_wellFormed (heap next : Heap) (environment : EnvId)
    (kind : FunctionKind) (constructible : Bool) (prototype homeObject : Option RefId)
    (constructorMode : ConstructorMode) (lexicalThis : Option Value) (ref : RefId)
    (valid : heap.WellFormed)
    (allocated : heap.allocateFunction environment kind constructible prototype homeObject
      constructorMode lexicalThis = .ok (ref, next)) : next.WellFormed := by
  unfold allocateFunction at allocated
  all_goals (split at allocated <;> try simp_all)
  all_goals (split at allocated <;> try simp_all)
  all_goals (split at allocated <;> try simp_all)
  cases lexicalEq : lexicalThis with
  | some lexicalValue =>
      all_goals (split at allocated <;> try simp_all)
      all_goals (split at allocated <;> try simp_all)
      all_goals (split at allocated <;> try simp_all)
      split at allocated <;> try contradiction
      rcases allocated with ⟨rfl, rfl⟩
      apply appendObject_preserves_wellFormed heap
        (.mk OrderedProps.empty prototype true
          (.function ⟨⟨heap.nextFunctionId⟩, environment, .arrow, false,
            constructorMode, homeObject, some lexicalValue⟩))
        (heap.nextFunctionId + 1) valid (by omega)
      · apply validateOptionalRef_valid heap prototype
        assumption
      · unfold objectReferencesValid functionSlotsValid
        have prototypeValid := validateOptionalRef_valid heap prototype _ (by assumption)
        have homeValid := validateOptionalRef_valid heap homeObject _ (by assumption)
        have prototypeNext : prototype.all
            (fun ref => ref.value < heap.objects.size + 1) = true := by
          cases prototype <;> simp_all [size] <;> omega
        have homeNext : homeObject.all
            (fun ref => ref.value < heap.objects.size + 1) = true := by
          cases homeObject <;> simp_all [size] <;> omega
        have lexicalOld : heap.valueValid lexicalValue = true := by assumption
        have lexicalNext := valueValid_push heap
          (.mk OrderedProps.empty prototype true
            (.function ⟨⟨heap.nextFunctionId⟩, environment, .arrow, false,
              constructorMode, homeObject, some lexicalValue⟩))
          (heap.nextFunctionId + 1) lexicalValue lexicalOld
        simp_all [functionCount, size, valueValid]
      · unfold functionSlotList
        simp
        apply functionIdsSequential_append 0 heap.functionSlotList
        · unfold WellFormed isWellFormed at valid
          simp only [Bool.and_eq_true] at valid
          exact valid.1.1.2
        · unfold WellFormed isWellFormed at valid
          simp only [Bool.and_eq_true] at valid
          exact Eq.symm (by simpa [functionCount] using valid.1.2)
      · unfold functionSlotList
        simp
        unfold WellFormed isWellFormed at valid
        simp only [Bool.and_eq_true] at valid
        simpa [functionCount] using valid.1.2

  | none =>
      all_goals (split at allocated <;> try simp_all)
      all_goals (split at allocated <;> try simp_all)
      split at allocated <;> try contradiction
      rcases allocated with ⟨rfl, rfl⟩
      apply appendObject_preserves_wellFormed heap
        (.mk OrderedProps.empty prototype true
          (.function ⟨⟨heap.nextFunctionId⟩, environment, kind, constructible,
            constructorMode, homeObject, none⟩))
        (heap.nextFunctionId + 1) valid (by omega)
      · apply validateOptionalRef_valid heap prototype
        assumption
      · unfold objectReferencesValid functionSlotsValid
        have prototypeValid := validateOptionalRef_valid heap prototype _ (by assumption)
        have homeValid := validateOptionalRef_valid heap homeObject _ (by assumption)
        have prototypeNext : prototype.all
            (fun ref => ref.value < heap.objects.size + 1) = true := by
          cases prototype <;> simp_all [size] <;> omega
        have homeNext : homeObject.all
            (fun ref => ref.value < heap.objects.size + 1) = true := by
          cases homeObject <;> simp_all [size] <;> omega
        simp_all [functionCount, size, valueValid]
        constructor
        · by_cases classKind : kind = .classConstructor <;> simp_all
        · by_cases derivedMode : constructorMode = .derived <;> simp_all
      · unfold functionSlotList
        simp
        apply functionIdsSequential_append 0 heap.functionSlotList
        · unfold WellFormed isWellFormed at valid
          simp only [Bool.and_eq_true] at valid
          exact valid.1.1.2
        · unfold WellFormed isWellFormed at valid
          simp only [Bool.and_eq_true] at valid
          exact Eq.symm (by simpa [functionCount] using valid.1.2)
      · unfold functionSlotList
        simp
        unfold WellFormed isWellFormed at valid
        simp only [Bool.and_eq_true] at valid
        simpa [functionCount] using valid.1.2

/-- Atomic constructor/prototype allocation preserves the complete heap invariant for ordinary and
class constructors. Captured-environment validity remains a machine-layer obligation. -/
theorem allocateConstructorPair_preserves_wellFormed (heap next : Heap) (environment : EnvId)
    (functionPrototype objectPrototype : Option RefId) (classConstructor : Bool)
    (constructorMode : ConstructorMode) (constructor prototype : RefId)
    (valid : heap.WellFormed)
    (allocated : heap.allocateConstructorPair environment functionPrototype objectPrototype
      classConstructor constructorMode = .ok (constructor, prototype, next)) : next.WellFormed := by
  unfold allocateConstructorPair at allocated
  split at allocated <;> try contradiction
  split at allocated <;> try contradiction
  split at allocated <;> try contradiction
  rcases allocated with ⟨rfl, rfl, rfl⟩
  let constructorRef : RefId := ⟨heap.objects.size⟩
  let prototypeRef : RefId := ⟨heap.objects.size + 1⟩
  let constructorDescriptor : PropertyDescriptor :=
    dataProperty (.object prototypeRef) (!classConstructor) false false
  let prototypeDescriptor : PropertyDescriptor :=
    dataProperty (.object constructorRef) true false true
  let constructorProperties := OrderedProps.empty.insert
    (.string (JSString.ofLeanString "prototype")) constructorDescriptor
  let prototypeProperties := OrderedProps.empty.insert
    (.string (JSString.ofLeanString "constructor")) prototypeDescriptor
  let kind := if classConstructor then FunctionKind.classConstructor else FunctionKind.ordinary
  let slots : FunctionSlots :=
    ⟨⟨heap.nextFunctionId⟩, environment, kind, true, constructorMode, none, none⟩
  let constructorObject : ObjectRecord :=
    .mk constructorProperties functionPrototype true (.function slots)
  let prototypeObject : ObjectRecord :=
    .mk prototypeProperties objectPrototype true .ordinary
  apply appendTwoObjects_preserves_wellFormed heap constructorObject prototypeObject
    (heap.nextFunctionId + 1) valid (by omega)
  · exact validateOptionalRef_valid heap functionPrototype _ (by assumption)
  · exact validateOptionalRef_valid heap objectPrototype _ (by assumption)
  · unfold constructorObject objectReferencesValid
    simp only [Bool.and_eq_true]
    refine ⟨⟨⟨OrderedProps.insert_wellFormed _ _ _ OrderedProps.empty_wellFormed, ?_⟩,
      ?_⟩, ?_⟩
    · apply OrderedProps.descriptors_all_insert
      · simp [constructorProperties]
      · simp [constructorDescriptor, dataProperty, descriptorReferencesValid, valueValid,
          prototypeRef, size]
    · have prototypeValid := validateOptionalRef_valid heap functionPrototype _ (by assumption)
      cases functionPrototype <;> simp_all [size]
      omega
    · unfold functionSlotsValid
      have modeValid : constructorMode = .derived → classConstructor = true := by
        intro derived
        simp_all
      simp [slots, kind, functionCount, size]
      by_cases isClass : classConstructor = true <;> simp_all
  · unfold prototypeObject objectReferencesValid
    simp only [Bool.and_eq_true]
    refine ⟨⟨⟨OrderedProps.insert_wellFormed _ _ _ OrderedProps.empty_wellFormed, ?_⟩,
      ?_⟩, trivial⟩
    · apply OrderedProps.descriptors_all_insert
      · simp [prototypeProperties]
      · simp [prototypeDescriptor, dataProperty, descriptorReferencesValid, valueValid,
          constructorRef, size]
        omega
    · have prototypeValid := validateOptionalRef_valid heap objectPrototype _ (by assumption)
      cases objectPrototype <;> simp_all [size]
      omega
  · unfold functionSlotList constructorObject prototypeObject
    simp
    apply functionIdsSequential_append 0 heap.functionSlotList
    · unfold WellFormed isWellFormed at valid
      simp only [Bool.and_eq_true] at valid
      exact valid.1.1.2
    · unfold slots
      unfold WellFormed isWellFormed at valid
      simp only [Bool.and_eq_true] at valid
      exact Eq.symm (by simpa [functionCount] using valid.1.2)
  · unfold functionSlotList constructorObject prototypeObject
    simp
    unfold WellFormed isWellFormed at valid
    simp only [Bool.and_eq_true] at valid
    simpa [functionCount] using valid.1.2

/-- Every successful array-iterator allocation preserves the complete heap invariant. -/
theorem allocateArrayIterator_preserves_wellFormed (heap next : Heap) (target : RefId)
    (prototype : Option RefId) (ref : RefId) (valid : heap.WellFormed)
    (allocated : heap.allocateArrayIterator target prototype = .ok (ref, next)) :
    next.WellFormed := by
  unfold allocateArrayIterator at allocated
  simp only [Bind.bind, Except.instMonad, Monad.toBind, Except.bind] at allocated
  cases targetFound : heap.get? target with
  | error fault => simp [targetFound] at allocated
  | ok targetObject =>
      cases targetKind : targetObject.kind with
      | ordinary => simp [targetFound, targetKind] at allocated
      | function slots => simp [targetFound, targetKind] at allocated
      | arrayIterator slots => simp [targetFound, targetKind] at allocated
      | primitiveWrapper slots => simp [targetFound, targetKind] at allocated
      | array slots =>
          cases prototype with
          | none =>
              simp [targetFound, targetKind] at allocated
              rcases allocated with ⟨rfl, rfl⟩
              apply appendObject_preserves_wellFormed heap
                (.mk OrderedProps.empty none true (.arrayIterator ⟨target, 0, false⟩))
                heap.nextFunctionId valid (by omega) (by rfl)
              · unfold objectReferencesValid arrayIteratorSlotsValid
                unfold get? at targetFound
                cases lookup : heap.objects[target.value]? with
                | none => simp [lookup] at targetFound
                | some object =>
                    simp [lookup] at targetFound
                    subst object
                    have targetNe : target.value ≠ heap.objects.size :=
                      Nat.ne_of_lt (Array.getElem?_eq_some_iff.mp lookup).choose
                    simp [Array.getElem?_push, targetNe, lookup, targetKind]
              · unfold functionSlotList
                simp
                unfold WellFormed isWellFormed at valid
                simp only [Bool.and_eq_true] at valid
                exact valid.1.1.2
              · unfold functionSlotList
                simp
                unfold WellFormed isWellFormed at valid
                simp only [Bool.and_eq_true] at valid
                simpa [functionCount] using valid.1.2
          | some prototype =>
              cases prototypeFound : heap.get? prototype with
              | error fault =>
                  simp [targetFound, targetKind, prototypeFound, Bind.bind, Except.bind,
                    Pure.pure, Except.pure] at allocated
              | ok prototypeObject =>
                  simp [targetFound, targetKind, prototypeFound] at allocated
                  rcases allocated with ⟨rfl, rfl⟩
                  have prototypeValid := validateOptionalRef_valid heap (some prototype) () (by
                    simp [validateOptionalRef, validateRef, prototypeFound])
                  apply appendObject_preserves_wellFormed heap
                    (.mk OrderedProps.empty (some prototype) true
                      (.arrayIterator ⟨target, 0, false⟩))
                    heap.nextFunctionId valid (by omega) prototypeValid
                  · unfold objectReferencesValid arrayIteratorSlotsValid
                    unfold get? at targetFound
                    cases lookup : heap.objects[target.value]? with
                    | none => simp [lookup] at targetFound
                    | some object =>
                        simp [lookup] at targetFound
                        subst object
                        have targetNe : target.value ≠ heap.objects.size :=
                          Nat.ne_of_lt (Array.getElem?_eq_some_iff.mp lookup).choose
                        have prototypeNext : prototype.value < heap.objects.size + 1 := by
                          have prototypeOld : prototype.value < heap.objects.size := by
                            simpa [size] using prototypeValid
                          omega
                        simp [size, Array.getElem?_push, targetNe, lookup, targetKind,
                          prototypeNext]
                  · unfold functionSlotList
                    simp
                    unfold WellFormed isWellFormed at valid
                    simp only [Bool.and_eq_true] at valid
                    exact valid.1.1.2
                  · unfold functionSlotList
                    simp
                    unfold WellFormed isWellFormed at valid
                    simp only [Bool.and_eq_true] at valid
                    simpa [functionCount] using valid.1.2

/-- A rejected normalized array-length shrink exposes the first descending nonconfigurable index,
commits all higher configurable deletions and the accepted writability, and changes no other object. -/
theorem defineOwnProperty_blocked_array_shrink
    (heap next : Heap) (target : RefId) (object : ObjectRecord) (slots : ArraySlots)
    (update normalizedUpdate : DescriptorUpdate) (kind : DescriptorKind) (number : JSNumber)
    (newLength : Nat) (lengthDescriptor : DataDescriptor)
    (valid : heap.WellFormed) (found : heap.get? target = .ok object)
    (arrayKind : object.kind = .array slots)
    (syntaxValid : update.validateSyntax = .ok kind)
    (valueField : update.value = .present (.primitive (.number number)))
    (decoded : validArrayLength? number = some newLength)
    (normalized : normalizedUpdate = { update with
      value := .present (.primitive (.number (arrayLengthNumber newLength))) })
    (accepted : normalizedUpdate.applyValidatedDescriptor
      (some (.data ⟨.primitive (.number (arrayLengthNumber slots.length)),
        slots.lengthWritable, false, false⟩)) true kind =
        Except.ok (.data lengthDescriptor))
    (shrink : newLength < slots.length) (writable : slots.lengthWritable = true)
    (defined : heap.defineOwnProperty target lengthPropertyKey update = .ok (false, next)) :
    ∃ blocked finalProperties finalObject,
      newLength ≤ blocked ∧
      (∃ descriptor,
        object.properties.lookup (.string (PropertyKey.arrayIndexString blocked)) = some descriptor ∧
        match descriptor with
        | .data data => data.configurable = false
        | .accessor accessor => accessor.configurable = false) ∧
      (∀ stringKey index descriptor, PropertyKey.arrayIndex? stringKey = some index →
        object.properties.lookup (.string stringKey) = some descriptor → blocked < index →
        (match descriptor with
          | .data data => data.configurable = true
          | .accessor accessor => accessor.configurable = true) ∧
        finalProperties.lookup (.string stringKey) = none) ∧
      (∀ stringKey index, PropertyKey.arrayIndex? stringKey = some index → index ≤ blocked →
        finalProperties.lookup (.string stringKey) = object.properties.lookup (.string stringKey)) ∧
      (∀ stringKey, PropertyKey.arrayIndex? stringKey = none →
        finalProperties.lookup (.string stringKey) = object.properties.lookup (.string stringKey)) ∧
      (∀ symbolKey, finalProperties.lookup (.symbol symbolKey) =
        object.properties.lookup (.symbol symbolKey)) ∧
      finalProperties.stringKeys = object.properties.stringKeys ∧
      finalProperties.symbolKeys = object.properties.symbolKeys ∧
      next.get? target = .ok finalObject ∧
      finalObject.properties = finalProperties ∧
      finalObject.prototype = object.prototype ∧
      finalObject.extensible = object.extensible ∧
      finalObject.kind = .array ⟨blocked + 1, lengthDescriptor.writable⟩ ∧
      next.getOwnProperty target lengthPropertyKey = .ok (some (.data
        ⟨.primitive (.number (arrayLengthNumber (blocked + 1))),
          lengthDescriptor.writable, false, false⟩)) ∧
      (∀ ref, ref ≠ target → next.get? ref = heap.get? ref) ∧
      lengthDescriptor.writable = normalizedUpdate.writable.apply slots.lengthWritable ∧
      (update.writable = .present false → lengthDescriptor.writable = false) ∧
      next.WellFormed := by
  unfold defineOwnProperty at defined
  rw [found, syntaxValid] at defined
  cases references : validateDescriptorReferences heap update with
  | error fault => simp [references] at defined
  | ok unit =>
      cases unit
      simp [references, arrayKind] at defined
      unfold defineArrayLength at defined
      unfold syntheticLengthDescriptor at defined
      have writableResult := DescriptorUpdate.applyValidatedDescriptor_data_writable
        normalizedUpdate
        ⟨.primitive (.number (arrayLengthNumber slots.length)), slots.lengthWritable,
          false, false⟩ lengthDescriptor true kind accepted
      rw [valueField] at defined
      simp [decoded] at defined
      rw [← normalized, accepted] at defined
      have notGrow : ¬slots.length < newLength := by omega
      have notEqual : slots.length ≠ newLength := by omega
      simp [notGrow, notEqual, writable] at defined
      cases swept : deleteArrayIndicesFrom object.properties newLength with
      | mk blocked properties =>
          cases blocked with
          | none =>
              exact False.elim (mappedTrue_ne_false _ next (by simpa [swept] using defined))
          | some blocked =>
              simp only [swept] at defined
              cases replaced : heap.replace target
                (.mk properties object.prototype object.extensible
                  (.array ⟨blocked + 1, lengthDescriptor.writable⟩)) with
              | error fault =>
                  rw [replaced] at defined
                  change Except.error (DefinePropertyFault.heap fault) =
                    Except.ok (false, next) at defined
                  contradiction
              | ok replacedHeap =>
                  rw [replaced] at defined
                  change Except.ok (false, replacedHeap) = Except.ok (false, next) at defined
                  cases defined
                  have oldPropertiesValid := wellFormed_object heap target object valid found
                  unfold objectReferencesValid at oldPropertiesValid
                  simp only [Bool.and_eq_true] at oldPropertiesValid
                  have blockedSpec := deleteArrayIndicesFrom_blocked object.properties properties
                    newLength blocked oldPropertiesValid.1.1.1 swept
                  have lookupSpec := deleteArrayIndicesFrom_blocked_lookups object.properties properties
                    newLength blocked oldPropertiesValid.1.1.1 swept
                  have nonIndex := deleteArrayIndicesFrom_lookup_nonIndex object.properties
                    newLength
                  have order := deleteArrayIndicesFrom_order object.properties newLength
                    oldPropertiesValid.1.1.1
                  have targetFound := get?_replace_same heap next target _ replaced
                  refine ⟨blocked, properties,
                    (.mk properties object.prototype object.extensible
                      (.array ⟨blocked + 1, lengthDescriptor.writable⟩)),
                    blockedSpec.1, blockedSpec.2.2,
                    ?_, ?_, ?_, ?_, ?_, ?_, targetFound, rfl, rfl, rfl, rfl, ?_, ?_,
                    writableResult, ?_, ?_⟩
                  · intro stringKey index descriptor parsed oldFound above
                    exact lookupSpec.1 (.string stringKey) index descriptor parsed oldFound above
                  · intro stringKey index parsed below
                    exact lookupSpec.2 (.string stringKey) index parsed below
                  · intro stringKey keyNonIndex
                    have preserved := nonIndex (.string stringKey)
                      oldPropertiesValid.1.1.1 keyNonIndex
                    rw [swept] at preserved
                    exact preserved
                  · intro symbolKey
                    have preserved := nonIndex (.symbol symbolKey)
                      oldPropertiesValid.1.1.1 rfl
                    rw [swept] at preserved
                    exact preserved
                  · simpa [swept] using order.1
                  · simpa [swept] using order.2
                  · unfold getOwnProperty
                    rw [targetFound]
                    rfl
                  · intro ref different
                    exact get?_replace_ne heap next target ref _ different replaced
                  · intro requested
                    have normalizedWritable : normalizedUpdate.writable = update.writable := by
                      rw [normalized]
                    rw [writableResult, normalizedWritable, requested]
                    rfl
                  · exact blockedArrayShrinkReplacement_preserves_wellFormed heap next target object
                      slots newLength blocked properties lengthDescriptor.writable valid found arrayKind
                      swept replaced

/-- A successful normalized array-length shrink deletes every old configurable index at or above
the new length, preserves lower and non-index properties exactly, and changes no other object. -/
theorem defineOwnProperty_unblocked_array_shrink
    (heap next : Heap) (target : RefId) (object : ObjectRecord) (slots : ArraySlots)
    (update normalizedUpdate : DescriptorUpdate) (kind : DescriptorKind) (number : JSNumber)
    (newLength : Nat) (lengthDescriptor : DataDescriptor)
    (valid : heap.WellFormed) (found : heap.get? target = .ok object)
    (arrayKind : object.kind = .array slots)
    (syntaxValid : update.validateSyntax = .ok kind)
    (valueField : update.value = .present (.primitive (.number number)))
    (decoded : validArrayLength? number = some newLength)
    (normalized : normalizedUpdate = { update with
      value := .present (.primitive (.number (arrayLengthNumber newLength))) })
    (accepted : normalizedUpdate.applyValidatedDescriptor
      (some (.data ⟨.primitive (.number (arrayLengthNumber slots.length)),
        slots.lengthWritable, false, false⟩)) true kind = Except.ok (.data lengthDescriptor))
    (shrink : newLength < slots.length) (writable : slots.lengthWritable = true)
    (defined : heap.defineOwnProperty target lengthPropertyKey update = .ok (true, next)) :
    ∃ finalProperties finalObject,
      (∀ stringKey index descriptor, PropertyKey.arrayIndex? stringKey = some index →
        object.properties.lookup (.string stringKey) = some descriptor → newLength ≤ index →
        (match descriptor with
          | .data data => data.configurable = true
          | .accessor accessor => accessor.configurable = true) ∧
        finalProperties.lookup (.string stringKey) = none) ∧
      (∀ stringKey index, PropertyKey.arrayIndex? stringKey = some index → index < newLength →
        finalProperties.lookup (.string stringKey) = object.properties.lookup (.string stringKey)) ∧
      (∀ stringKey, PropertyKey.arrayIndex? stringKey = none →
        finalProperties.lookup (.string stringKey) = object.properties.lookup (.string stringKey)) ∧
      (∀ symbolKey, finalProperties.lookup (.symbol symbolKey) =
        object.properties.lookup (.symbol symbolKey)) ∧
      finalProperties.stringKeys = object.properties.stringKeys ∧
      finalProperties.symbolKeys = object.properties.symbolKeys ∧
      next.get? target = .ok finalObject ∧
      finalObject.properties = finalProperties ∧
      finalObject.prototype = object.prototype ∧
      finalObject.extensible = object.extensible ∧
      finalObject.kind = .array ⟨newLength, lengthDescriptor.writable⟩ ∧
      next.getOwnProperty target lengthPropertyKey = .ok (some (.data
        ⟨.primitive (.number (arrayLengthNumber newLength)),
          lengthDescriptor.writable, false, false⟩)) ∧
      (∀ ref, ref ≠ target → next.get? ref = heap.get? ref) ∧
      lengthDescriptor.writable = normalizedUpdate.writable.apply slots.lengthWritable ∧
      (update.writable = .present false → lengthDescriptor.writable = false) ∧
      next.WellFormed := by
  unfold defineOwnProperty at defined
  rw [found, syntaxValid] at defined
  cases references : validateDescriptorReferences heap update with
  | error fault => simp [references] at defined
  | ok unit =>
      cases unit
      simp [references, arrayKind] at defined
      unfold defineArrayLength at defined
      unfold syntheticLengthDescriptor at defined
      have writableResult := DescriptorUpdate.applyValidatedDescriptor_data_writable
        normalizedUpdate
        ⟨.primitive (.number (arrayLengthNumber slots.length)), slots.lengthWritable,
          false, false⟩ lengthDescriptor true kind accepted
      rw [valueField] at defined
      simp [decoded] at defined
      rw [← normalized, accepted] at defined
      have notGrow : ¬slots.length < newLength := by omega
      have notEqual : slots.length ≠ newLength := by omega
      simp [notGrow, notEqual, writable] at defined
      cases swept : deleteArrayIndicesFrom object.properties newLength with
      | mk blocked properties =>
          cases blocked with
          | some blocked =>
              exact False.elim (mappedFalse_ne_true _ next (by simpa [swept] using defined))
          | none =>
              cases replaced : heap.replace target
                (.mk properties object.prototype object.extensible
                  (.array ⟨newLength, lengthDescriptor.writable⟩)) with
              | error fault =>
                  rw [swept, replaced] at defined
                  change Except.error (DefinePropertyFault.heap fault) =
                    Except.ok (true, next) at defined
                  contradiction
              | ok replacedHeap =>
                  rw [swept, replaced] at defined
                  change Except.ok (true, replacedHeap) = Except.ok (true, next) at defined
                  cases defined
                  have oldPropertiesValid := wellFormed_object heap target object valid found
                  unfold objectReferencesValid at oldPropertiesValid
                  simp only [Bool.and_eq_true] at oldPropertiesValid
                  have deleted := deleteArrayIndicesFrom_unblocked object.properties properties
                    newLength oldPropertiesValid.1.1.1 swept
                  have nonIndex := deleteArrayIndicesFrom_lookup_nonIndex object.properties newLength
                  have order := deleteArrayIndicesFrom_order object.properties newLength
                    oldPropertiesValid.1.1.1
                  have targetFound := get?_replace_same heap next target _ replaced
                  refine ⟨properties,
                    (.mk properties object.prototype object.extensible
                      (.array ⟨newLength, lengthDescriptor.writable⟩)),
                    ?_, ?_, ?_, ?_, ?_, ?_, targetFound, rfl, rfl, rfl, rfl, ?_, ?_,
                    writableResult, ?_, ?_⟩
                  · intro stringKey index descriptor parsed oldFound atLeast
                    exact deleted (.string stringKey) index descriptor parsed oldFound atLeast
                  · intro stringKey index parsed below
                    have preserved := deleteArrayIndicesFrom_lookup_below object.properties newLength
                      (.string stringKey) index oldPropertiesValid.1.1.1 parsed below
                    rw [swept] at preserved
                    exact preserved
                  · intro stringKey keyNonIndex
                    have preserved := nonIndex (.string stringKey)
                      oldPropertiesValid.1.1.1 keyNonIndex
                    rw [swept] at preserved
                    exact preserved
                  · intro symbolKey
                    have preserved := nonIndex (.symbol symbolKey)
                      oldPropertiesValid.1.1.1 rfl
                    rw [swept] at preserved
                    exact preserved
                  · simpa [swept] using order.1
                  · simpa [swept] using order.2
                  · unfold getOwnProperty
                    rw [targetFound]
                    rfl
                  · intro ref different
                    exact get?_replace_ne heap next target ref _ different replaced
                  · intro requested
                    have normalizedWritable : normalizedUpdate.writable = update.writable := by
                      rw [normalized]
                    rw [writableResult, normalizedWritable, requested]
                    rfl
                  · exact unblockedArrayShrinkReplacement_preserves_wellFormed heap next target object
                      slots newLength properties lengthDescriptor.writable valid found arrayKind shrink
                      swept replaced

private def shrinkFixtureDescriptor (index : Nat) (configurable : Bool) : PropertyDescriptor :=
  .data ⟨.primitive (.bigint index), true, true, configurable⟩

private def blockedShrinkFixtureProperties : OrderedProps :=
  OrderedProps.empty
    |>.insert (.string (PropertyKey.arrayIndexString 0)) (shrinkFixtureDescriptor 0 true)
    |>.insert (.string (PropertyKey.arrayIndexString 1)) (shrinkFixtureDescriptor 1 true)
    |>.insert (.string (PropertyKey.arrayIndexString 2)) (shrinkFixtureDescriptor 2 false)
    |>.insert (.string (PropertyKey.arrayIndexString 3)) (shrinkFixtureDescriptor 3 true)

private def unblockedShrinkFixtureProperties : OrderedProps :=
  OrderedProps.empty
    |>.insert (.string (PropertyKey.arrayIndexString 0)) (shrinkFixtureDescriptor 0 true)
    |>.insert (.string (PropertyKey.arrayIndexString 1)) (shrinkFixtureDescriptor 1 true)
    |>.insert (.string (PropertyKey.arrayIndexString 2)) (shrinkFixtureDescriptor 2 true)

private def blockedShrinkFixtureObject : ObjectRecord :=
  .mk blockedShrinkFixtureProperties none true (.array ⟨4, true⟩)

private def unblockedShrinkFixtureObject : ObjectRecord :=
  .mk unblockedShrinkFixtureProperties none true (.array ⟨3, true⟩)

private def blockedShrinkFixtureHeap : Heap := .mk #[blockedShrinkFixtureObject] 0
private def unblockedShrinkFixtureHeap : Heap := .mk #[unblockedShrinkFixtureObject] 0

private def shrinkFixtureUpdate : DescriptorUpdate := {
  value := .present (.primitive (.number (arrayLengthNumber 1)))
  writable := .present false
}

private def blockedShrinkFixtureSucceeds : Bool :=
  match blockedShrinkFixtureHeap.defineOwnProperty ⟨0⟩ lengthPropertyKey shrinkFixtureUpdate with
  | .ok (false, _) => true
  | _ => false

private def unblockedShrinkFixtureSucceeds : Bool :=
  match unblockedShrinkFixtureHeap.defineOwnProperty ⟨0⟩ lengthPropertyKey shrinkFixtureUpdate with
  | .ok (true, _) => true
  | _ => false

/-- The public blocked-shrink theorem has a concrete writable-to-nonwritable witness. -/
private theorem defineOwnProperty_blocked_array_shrink_nonvacuous :
    ∃ next blocked,
      blockedShrinkFixtureHeap.defineOwnProperty ⟨0⟩ lengthPropertyKey shrinkFixtureUpdate =
        .ok (false, next) ∧
      next.arrayLength ⟨0⟩ = .ok (blocked + 1) ∧
      next.getOwnProperty ⟨0⟩ lengthPropertyKey = .ok (some (.data
        ⟨.primitive (.number (arrayLengthNumber (blocked + 1))), false, false, false⟩)) ∧
      next.WellFormed := by
  set_option maxRecDepth 100000 in
    have succeeds : blockedShrinkFixtureSucceeds = true := by native_decide
    cases run : blockedShrinkFixtureHeap.defineOwnProperty ⟨0⟩ lengthPropertyKey
        shrinkFixtureUpdate with
    | error fault => simp [blockedShrinkFixtureSucceeds, run] at succeeds
    | ok result =>
        rcases result with ⟨success, next⟩
        cases success with
        | true => simp [blockedShrinkFixtureSucceeds, run] at succeeds
        | false =>
            have lifted := defineOwnProperty_blocked_array_shrink
              blockedShrinkFixtureHeap next ⟨0⟩ blockedShrinkFixtureObject ⟨4, true⟩
              shrinkFixtureUpdate shrinkFixtureUpdate .data (arrayLengthNumber 1) 1
              ⟨.primitive (.number (arrayLengthNumber 1)), false, false, false⟩
              (by unfold WellFormed; native_decide) (by rfl) (by rfl) (by rfl) (by rfl)
              (by rfl) (by rfl) (by rfl) (by decide) (by rfl) run
            rcases lifted with
              ⟨blocked, properties, finalObject, bound, blocker, higher, lower, strings, symbols,
                stringOrder, symbolOrder, targetFound, propertiesEq, prototypeEq, extensibleEq,
                kindEq, lengthFound, otherObjects, writableExact, writableFalse, finalValid⟩
            have lengthResult : next.arrayLength ⟨0⟩ = .ok (blocked + 1) := by
              unfold arrayLength
              simp only [Bind.bind, Except.bind, targetFound]
              rw [kindEq]
              rfl
            exact ⟨next, blocked, rfl, lengthResult, lengthFound, finalValid⟩

/-- The public unblocked-shrink theorem has a concrete successful nonwritable witness. -/
private theorem defineOwnProperty_unblocked_array_shrink_nonvacuous :
    ∃ next,
      unblockedShrinkFixtureHeap.defineOwnProperty ⟨0⟩ lengthPropertyKey shrinkFixtureUpdate =
        .ok (true, next) ∧
      next.arrayLength ⟨0⟩ = .ok 1 ∧
      next.getOwnProperty ⟨0⟩ lengthPropertyKey = .ok (some (.data
        ⟨.primitive (.number (arrayLengthNumber 1)), false, false, false⟩)) ∧
      next.WellFormed := by
  set_option maxRecDepth 100000 in
    have succeeds : unblockedShrinkFixtureSucceeds = true := by native_decide
    cases run : unblockedShrinkFixtureHeap.defineOwnProperty ⟨0⟩ lengthPropertyKey
        shrinkFixtureUpdate with
    | error fault => simp [unblockedShrinkFixtureSucceeds, run] at succeeds
    | ok result =>
        rcases result with ⟨success, next⟩
        cases success with
        | false => simp [unblockedShrinkFixtureSucceeds, run] at succeeds
        | true =>
            have lifted := defineOwnProperty_unblocked_array_shrink
              unblockedShrinkFixtureHeap next ⟨0⟩ unblockedShrinkFixtureObject ⟨3, true⟩
              shrinkFixtureUpdate shrinkFixtureUpdate .data (arrayLengthNumber 1) 1
              ⟨.primitive (.number (arrayLengthNumber 1)), false, false, false⟩
              (by unfold WellFormed; native_decide) (by rfl) (by rfl) (by rfl) (by rfl)
              (by rfl) (by rfl) (by rfl) (by decide) (by rfl) run
            rcases lifted with
              ⟨properties, finalObject, deleted, lower, strings, symbols, stringOrder, symbolOrder,
                targetFound, propertiesEq, prototypeEq, extensibleEq, kindEq, lengthFound,
                otherObjects, writableExact, writableFalse, finalValid⟩
            have lengthResult : next.arrayLength ⟨0⟩ = .ok 1 := by
              unfold arrayLength
              simp only [Bind.bind, Except.bind, targetFound]
              rw [kindEq]
              rfl
            exact ⟨next, rfl, lengthResult, lengthFound, finalValid⟩

private def publicMutationFixtureUpdate : DescriptorUpdate := {
  value := .present (.primitive (.bigint 7))
  writable := .present true
  enumerable := .present true
  configurable := .present true
}

private def ordinaryMutationFixtureHeap : Heap :=
  .mk #[.mk OrderedProps.empty none true .ordinary] 0

private def arrayExtensionFixtureHeap : Heap :=
  .mk #[.mk OrderedProps.empty none true (.array ⟨0, true⟩)] 0

private def wrapperMutationFixtureHeap : Heap :=
  .mk #[.mk OrderedProps.empty none true
    (.primitiveWrapper ⟨.string (JSString.ofLeanString "a")⟩)] 0

private def objectValueFixtureHeap : Heap :=
  .mk #[.mk OrderedProps.empty none true .ordinary,
    .mk OrderedProps.empty none true .ordinary] 0

private def operationReturns (expected : Bool)
    (operation : Except DefinePropertyFault (Bool × Heap)) : Bool :=
  match operation with
  | .ok (success, _) => success == expected
  | .error _ => false

/-- Ordinary public definition has a successful witness covered by the general theorem. -/
private theorem defineOwnProperty_ordinary_nonvacuous :
    ∃ next, ordinaryMutationFixtureHeap.defineOwnProperty ⟨0⟩
      (.string (JSString.ofLeanString "x")) publicMutationFixtureUpdate = .ok (true, next) ∧
      next.WellFormed := by
  have succeeds : operationReturns true (ordinaryMutationFixtureHeap.defineOwnProperty ⟨0⟩
      (.string (JSString.ofLeanString "x")) publicMutationFixtureUpdate) = true := by native_decide
  cases run : ordinaryMutationFixtureHeap.defineOwnProperty ⟨0⟩
      (.string (JSString.ofLeanString "x")) publicMutationFixtureUpdate with
  | error fault => simp [operationReturns, run] at succeeds
  | ok result =>
      rcases result with ⟨success, next⟩
      cases success with
      | false => simp [operationReturns, run] at succeeds
      | true =>
          exact ⟨next, rfl, defineOwnProperty_preserves_wellFormed _ _ _ _ _ _
            (by unfold WellFormed; native_decide) run⟩

/-- Public array-index extension has a witness covered by the general theorem. -/
private theorem defineOwnProperty_array_extension_nonvacuous :
    ∃ next, arrayExtensionFixtureHeap.defineOwnProperty ⟨0⟩
      (.string (PropertyKey.arrayIndexString 0)) publicMutationFixtureUpdate = .ok (true, next) ∧
      next.WellFormed := by
  have succeeds : operationReturns true (arrayExtensionFixtureHeap.defineOwnProperty ⟨0⟩
      (.string (PropertyKey.arrayIndexString 0)) publicMutationFixtureUpdate) = true := by native_decide
  cases run : arrayExtensionFixtureHeap.defineOwnProperty ⟨0⟩
      (.string (PropertyKey.arrayIndexString 0)) publicMutationFixtureUpdate with
  | error fault => simp [operationReturns, run] at succeeds
  | ok result =>
      rcases result with ⟨success, next⟩
      cases success with
      | false => simp [operationReturns, run] at succeeds
      | true =>
          exact ⟨next, rfl, defineOwnProperty_preserves_wellFormed _ _ _ _ _ _
            (by unfold WellFormed; native_decide) run⟩

/-- Primitive-wrapper synthetic rejection and ordinary storage both instantiate the public theorem. -/
private theorem defineOwnProperty_wrapper_nonvacuous :
    (∃ next, wrapperMutationFixtureHeap.defineOwnProperty ⟨0⟩
      (.string (PropertyKey.arrayIndexString 0)) publicMutationFixtureUpdate = .ok (false, next) ∧
      next.WellFormed) ∧
    (∃ next, wrapperMutationFixtureHeap.defineOwnProperty ⟨0⟩
      (.string (JSString.ofLeanString "x")) publicMutationFixtureUpdate = .ok (true, next) ∧
      next.WellFormed) := by
  constructor
  · have succeeds : operationReturns false (wrapperMutationFixtureHeap.defineOwnProperty ⟨0⟩
        (.string (PropertyKey.arrayIndexString 0)) publicMutationFixtureUpdate) = true := by
      native_decide
    cases run : wrapperMutationFixtureHeap.defineOwnProperty ⟨0⟩
        (.string (PropertyKey.arrayIndexString 0)) publicMutationFixtureUpdate with
    | error fault => simp [operationReturns, run] at succeeds
    | ok result =>
        rcases result with ⟨success, next⟩
        cases success with
        | true => simp [operationReturns, run] at succeeds
        | false =>
            exact ⟨next, rfl, defineOwnProperty_preserves_wellFormed _ _ _ _ _ _
              (by unfold WellFormed; native_decide) run⟩
  · have succeeds : operationReturns true (wrapperMutationFixtureHeap.defineOwnProperty ⟨0⟩
        (.string (JSString.ofLeanString "x")) publicMutationFixtureUpdate) = true := by native_decide
    cases run : wrapperMutationFixtureHeap.defineOwnProperty ⟨0⟩
        (.string (JSString.ofLeanString "x")) publicMutationFixtureUpdate with
    | error fault => simp [operationReturns, run] at succeeds
    | ok result =>
        rcases result with ⟨success, next⟩
        cases success with
        | false => simp [operationReturns, run] at succeeds
        | true =>
            exact ⟨next, rfl, defineOwnProperty_preserves_wellFormed _ _ _ _ _ _
              (by unfold WellFormed; native_decide) run⟩

/-- Object-valued public data-property creation has a reference-valid witness. -/
private theorem createDataProperty_object_reference_nonvacuous :
    ∃ next, objectValueFixtureHeap.createDataProperty ⟨0⟩
      (.string (JSString.ofLeanString "peer")) (.object ⟨1⟩) = .ok (true, next) ∧
      next.WellFormed := by
  have succeeds : operationReturns true (objectValueFixtureHeap.createDataProperty ⟨0⟩
      (.string (JSString.ofLeanString "peer")) (.object ⟨1⟩)) = true := by native_decide
  cases run : objectValueFixtureHeap.createDataProperty ⟨0⟩
      (.string (JSString.ofLeanString "peer")) (.object ⟨1⟩) with
  | error fault => simp [operationReturns, run] at succeeds
  | ok result =>
      rcases result with ⟨success, next⟩
      cases success with
      | false => simp [operationReturns, run] at succeeds
      | true =>
          exact ⟨next, rfl, createDataProperty_preserves_wellFormed _ _ _ _ _ _
            (by unfold WellFormed; native_decide) run⟩

/-- A blocked false commit is covered directly by the result-oriented public theorem. -/
private theorem defineOwnProperty_blocked_false_preservation_nonvacuous :
    ∃ next, blockedShrinkFixtureHeap.defineOwnProperty ⟨0⟩ lengthPropertyKey shrinkFixtureUpdate =
      .ok (false, next) ∧ next.WellFormed := by
  have succeeds : blockedShrinkFixtureSucceeds = true := by native_decide
  cases run : blockedShrinkFixtureHeap.defineOwnProperty ⟨0⟩ lengthPropertyKey
      shrinkFixtureUpdate with
  | error fault => simp [blockedShrinkFixtureSucceeds, run] at succeeds
  | ok result =>
      rcases result with ⟨success, next⟩
      cases success with
      | true => simp [blockedShrinkFixtureSucceeds, run] at succeeds
      | false =>
          exact ⟨next, rfl, defineOwnProperty_preserves_wellFormed _ _ _ _ _ _
            (by unfold WellFormed; native_decide) run⟩

-- Registry of proved allocation, property-definition, deletion, and extensibility preservation
-- theorems. Iterator advancement and prototype mutation remain explicit obligations below.
namespace PublicMutationPreservation

export Heap (allocate_preserves_wellFormed allocatePrimitiveWrapper_preserves_wellFormed
  allocateArray_preserves_wellFormed allocateArrayFromArray_preserves_wellFormed
  allocateFunction_preserves_wellFormed allocateConstructorPair_preserves_wellFormed
  allocateArrayIterator_preserves_wellFormed defineOwnProperty_preserves_wellFormed
  createDataProperty_preserves_wellFormed deleteProperty_preserves_wellFormed
  preventExtensions_preserves_wellFormed)

end PublicMutationPreservation

-- TODO(theorem): prove iterator advancement and `setPrototypeOf` preserve `WellFormed`.

end Heap
end TSLean.JS
