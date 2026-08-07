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

private def deleteArrayIndicesFrom (properties : OrderedProps) (newLength : Nat) :
    Option Nat × OrderedProps :=
  let descending := properties.ownKeys.filterMap arrayIndexEntry? |>.reverse
  descending.foldl (fun state entry =>
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
          | none => state) (none, properties)

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

/-- A rejected delete preserves complete heap validity because it preserves the heap exactly. -/
theorem failed_delete_preserves_wellFormed
    (heap next : Heap) (ref : RefId) (key : PropertyKey) (valid : heap.WellFormed)
    (rejected : heap.deleteProperty ref key = .ok (false, next)) : next.WellFormed := by
  rw [failed_delete_preserves_heap heap next ref key rejected]
  exact valid

/-- The empty heap satisfies the complete executable invariant. -/
theorem empty_wellFormed : WellFormed empty := by
  rfl

/-- Empty-heap ordinary allocation preserves the complete executable heap invariant. -/
theorem empty_allocate_wellFormed :
    match Heap.empty.allocate none true with
    | .ok (_, next) => next.WellFormed
    | .error _ => False := by
  simp [allocate, validPrototype, empty, WellFormed, isWellFormed, functionSlotList,
    objectReferencesValid, prototypeGraphAcyclic, validatePrototypeGraphAux, visitPrototype,
    finishPrototypePath, functionIdsSequential, size, functionCount]

/-- Empty-heap arrow allocation preserves the complete executable heap invariant. -/
theorem empty_arrow_allocate_wellFormed :
    match Heap.empty.allocateFunction ⟨0⟩ .arrow false none none .base
        (some (.primitive .undefined)) with
    | .ok (_, next) => next.WellFormed
    | .error _ => False := by
  simp [allocateFunction, validateOptionalRef, appendFunction, empty, WellFormed, isWellFormed,
    functionSlotList, objectReferencesValid, functionSlotsValid, valueValid,
    prototypeGraphAcyclic, validatePrototypeGraphAux, visitPrototype, finishPrototypePath,
    functionIdsSequential, size, functionCount]

/-- Empty-array allocation preserves the complete executable heap invariant. -/
theorem empty_array_allocate_wellFormed :
    match Heap.empty.allocateArray [] with
    | .ok (_, next) => next.WellFormed
    | .error _ => False := by
  simp [allocateArray, allocateArrayFromArray, appendArray, empty, WellFormed, isWellFormed,
    functionSlotList, objectReferencesValid, arraySlotsValid,
    prototypeGraphAcyclic, validatePrototypeGraphAux, visitPrototype, finishPrototypePath,
    functionIdsSequential, size, functionCount, maxArrayLength]

/-- Empty-heap primitive wrapper allocation preserves the complete executable heap invariant. -/
theorem empty_primitive_wrapper_allocate_wellFormed :
    match Heap.empty.allocatePrimitiveWrapper (.boolean true) with
    | .ok (_, next) => next.WellFormed
    | .error _ => False := by
  simp [allocatePrimitiveWrapper, primitiveBoxable, validPrototype, empty, WellFormed,
    isWellFormed, functionSlotList, objectReferencesValid, primitiveWrapperSlotsValid,
    prototypeGraphAcyclic, validatePrototypeGraphAux, visitPrototype,
    finishPrototypePath, functionIdsSequential, size, functionCount]

-- TODO(theorem): prove general successful `defineOwnProperty`, `createDataProperty`,
-- `deleteProperty`, iterator advancement, `preventExtensions`, and `setPrototypeOf` preserve
-- `WellFormed`; blocked array shrink requires its separate partial-commit characterization.

end Heap
end TSLean.JS
