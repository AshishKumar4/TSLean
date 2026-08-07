import TSLean.JS.Equality

namespace TSLean.JS

/-- An ordinary ECMAScript data property descriptor. -/
structure DataDescriptor where
  value : Value
  writable : Bool
  enumerable : Bool
  configurable : Bool

/-- An ordinary ECMAScript accessor property descriptor. -/
structure AccessorDescriptor where
  get : Option RefId
  set : Option RefId
  enumerable : Bool
  configurable : Bool

/-- A complete own-property descriptor. -/
inductive PropertyDescriptor where
  | data (descriptor : DataDescriptor)
  | accessor (descriptor : AccessorDescriptor)

/-- A descriptor update field, preserving the distinction between absent and present. -/
inductive FieldUpdate (α : Type) where
  | absent
  | present (value : α)

namespace FieldUpdate

/-- Applies a present field and otherwise retains the current value. -/
def apply (current : α) : FieldUpdate α → α
  | .absent => current
  | .present value => value

/-- Reports whether an update field is present. -/
def isPresent : FieldUpdate α → Bool
  | .absent => false
  | .present _ => true

end FieldUpdate

/-- The fields supplied to `DefineProperty`; a present `undefined` value remains present. -/
structure DescriptorUpdate where
  value : FieldUpdate Value := .absent
  writable : FieldUpdate Bool := .absent
  get : FieldUpdate (Option RefId) := .absent
  set : FieldUpdate (Option RefId) := .absent
  enumerable : FieldUpdate Bool := .absent
  configurable : FieldUpdate Bool := .absent

/-- Classification of a syntactically valid descriptor update. -/
inductive DescriptorKind where
  | generic
  | data
  | accessor
  deriving DecidableEq

/-- Descriptor syntax failures that complete abruptly in the model. -/
inductive DescriptorSyntaxFault where
  | mixedDescriptor
  deriving DecidableEq

/-- Ordinary descriptor invariant rejections, represented by a `false` operation result. -/
inductive DescriptorRejection where
  | nonExtensible
  | nonConfigurable
  | nonWritable
  deriving DecidableEq

namespace DescriptorUpdate

/-- Classifies an update, rejecting mixed data and accessor fields. -/
def validateSyntax (update : DescriptorUpdate) : Except DescriptorSyntaxFault DescriptorKind :=
  let data := update.value.isPresent || update.writable.isPresent
  let accessor := update.get.isPresent || update.set.isPresent
  if data && accessor then .error .mixedDescriptor
  else if data then .ok .data
  else if accessor then .ok .accessor
  else .ok .generic

private def boolChanged (current : Bool) : FieldUpdate Bool → Bool
  | .absent => false
  | .present value => value != current

private def valueChanged (current : Value) : FieldUpdate Value → Bool
  | .absent => false
  | .present value => !sameValue current value

private def refChanged (current : Option RefId) : FieldUpdate (Option RefId) → Bool
  | .absent => false
  | .present value => decide (value ≠ current)

private def descriptorConfigurable : PropertyDescriptor → Bool
  | .data descriptor => descriptor.configurable
  | .accessor descriptor => descriptor.configurable

private def descriptorEnumerable : PropertyDescriptor → Bool
  | .data descriptor => descriptor.enumerable
  | .accessor descriptor => descriptor.enumerable

private def applyCommon
    (update : DescriptorUpdate) (enumerable configurable : Bool) : Bool × Bool :=
  (update.enumerable.apply enumerable, update.configurable.apply configurable)

private def newDescriptor (kind : DescriptorKind) (update : DescriptorUpdate) : PropertyDescriptor :=
  let common := applyCommon update false false
  match kind with
  | .accessor => .accessor {
      get := update.get.apply none
      set := update.set.apply none
      enumerable := common.1
      configurable := common.2
    }
  | .generic | .data => .data {
      value := update.value.apply (.primitive .undefined)
      writable := update.writable.apply false
      enumerable := common.1
      configurable := common.2
    }

private def applySameKind
    (current : PropertyDescriptor) (update : DescriptorUpdate) : PropertyDescriptor :=
  match current with
  | .data descriptor => .data {
      value := update.value.apply descriptor.value
      writable := update.writable.apply descriptor.writable
      enumerable := update.enumerable.apply descriptor.enumerable
      configurable := update.configurable.apply descriptor.configurable
    }
  | .accessor descriptor => .accessor {
      get := update.get.apply descriptor.get
      set := update.set.apply descriptor.set
      enumerable := update.enumerable.apply descriptor.enumerable
      configurable := update.configurable.apply descriptor.configurable
    }

private def transition
    (current : PropertyDescriptor) (kind : DescriptorKind)
    (update : DescriptorUpdate) : PropertyDescriptor :=
  let common := applyCommon update (descriptorEnumerable current) (descriptorConfigurable current)
  match kind with
  | .accessor => .accessor {
      get := update.get.apply none
      set := update.set.apply none
      enumerable := common.1
      configurable := common.2
    }
  | .data => .data {
      value := update.value.apply (.primitive .undefined)
      writable := update.writable.apply false
      enumerable := common.1
      configurable := common.2
    }
  | .generic => applySameKind current update

/-- Applies ordinary descriptor invariants after syntax and accessor validation. -/
def applyValidatedDescriptor
    (current : Option PropertyDescriptor) (extensible : Bool)
    (update : DescriptorUpdate) (kind : DescriptorKind) :
    Except DescriptorRejection PropertyDescriptor := do
  match current with
  | none =>
      if extensible then pure (newDescriptor kind update) else throw .nonExtensible
  | some descriptor =>
      if !descriptorConfigurable descriptor then
        match update.configurable with
        | .present true => throw .nonConfigurable
        | _ => pure ()
        if boolChanged (descriptorEnumerable descriptor) update.enumerable then throw .nonConfigurable
      match descriptor, kind with
      | .data _, .accessor | .accessor _, .data =>
          if descriptorConfigurable descriptor then pure (transition descriptor kind update)
          else throw .nonConfigurable
      | .data data, .data =>
          if !data.configurable && !data.writable then
            match update.writable with
            | .present true => throw .nonWritable
            | _ => pure ()
            if valueChanged data.value update.value then throw .nonWritable
          pure (applySameKind descriptor update)
      | .accessor accessor, .accessor =>
          if !accessor.configurable &&
              (refChanged accessor.get update.get || refChanged accessor.set update.set) then
            throw .nonConfigurable
          pure (applySameKind descriptor update)
      | _, .generic => pure (applySameKind descriptor update)

/-- Reference validity for a complete descriptor, parameterized by value and accessor policies. -/
def DescriptorReferencesValid (valueValid : Value → Prop)
    (accessorValid : RefId → Prop) : PropertyDescriptor → Prop
  | .data descriptor => valueValid descriptor.value
  | .accessor descriptor =>
      (match descriptor.get with | none => True | some ref => accessorValid ref) ∧
      (match descriptor.set with | none => True | some ref => accessorValid ref)

/-- Reference validity for fields explicitly supplied by a descriptor update. -/
def ReferencesValid (valueValid : Value → Prop) (accessorValid : RefId → Prop)
    (update : DescriptorUpdate) : Prop :=
  (match update.value with
    | .absent => True
    | .present value => valueValid value) ∧
  (match update.get with
    | .absent => True
    | .present getter => match getter with | none => True | some ref => accessorValid ref) ∧
  (match update.set with
    | .absent => True
    | .present setter => match setter with | none => True | some ref => accessorValid ref)

private theorem newDescriptor_referencesValid (update : DescriptorUpdate) (kind : DescriptorKind)
    (valueValid : Value → Prop) (accessorValid : RefId → Prop)
    (defaultValueValid : valueValid (.primitive .undefined))
    (valid : update.ReferencesValid valueValid accessorValid) :
    DescriptorReferencesValid valueValid accessorValid (newDescriptor kind update) := by
  cases update
  rename_i value writable get set enumerable configurable
  simp only [ReferencesValid] at valid
  cases kind <;> cases value <;> cases get <;> cases set <;>
    simp_all [newDescriptor, applyCommon, DescriptorReferencesValid, FieldUpdate.apply]

private theorem applySameKind_referencesValid (update : DescriptorUpdate)
    (current : PropertyDescriptor) (valueValid : Value → Prop) (accessorValid : RefId → Prop)
    (updateValid : update.ReferencesValid valueValid accessorValid)
    (currentValid : DescriptorReferencesValid valueValid accessorValid current) :
    DescriptorReferencesValid valueValid accessorValid (applySameKind current update) := by
  cases update
  rename_i value writable get set enumerable configurable
  simp only [ReferencesValid] at updateValid
  cases current <;> cases value <;> cases get <;> cases set <;>
    simp_all [applySameKind, DescriptorReferencesValid, FieldUpdate.apply]

private theorem transition_referencesValid (update : DescriptorUpdate)
    (current : PropertyDescriptor) (kind : DescriptorKind)
    (valueValid : Value → Prop) (accessorValid : RefId → Prop)
    (defaultValueValid : valueValid (.primitive .undefined))
    (updateValid : update.ReferencesValid valueValid accessorValid)
    (currentValid : DescriptorReferencesValid valueValid accessorValid current) :
    DescriptorReferencesValid valueValid accessorValid (transition current kind update) := by
  cases update
  rename_i value writable get set enumerable configurable
  simp only [ReferencesValid] at updateValid
  cases kind <;> cases current <;> cases value <;> cases get <;> cases set <;>
    simp_all [transition, applySameKind, applyCommon, DescriptorReferencesValid, FieldUpdate.apply]

private def validatedResult (current : PropertyDescriptor) (kind : DescriptorKind)
    (update : DescriptorUpdate) : Except DescriptorRejection PropertyDescriptor :=
  match current, kind with
  | .data _, .accessor | .accessor _, .data =>
      if descriptorConfigurable current then pure (transition current kind update)
      else throw .nonConfigurable
  | .data data, .data => do
      if !data.configurable && !data.writable then
        match update.writable with
        | .present true => throw .nonWritable
        | _ => pure ()
        if valueChanged data.value update.value then throw .nonWritable
      pure (applySameKind current update)
  | .accessor accessor, .accessor => do
      if !accessor.configurable &&
          (refChanged accessor.get update.get || refChanged accessor.set update.set) then
        throw .nonConfigurable
      pure (applySameKind current update)
  | _, .generic => pure (applySameKind current update)

private def OkSatisfies (predicate : α → Prop) : Except ε α → Prop
  | .error _ => True
  | .ok value => predicate value

private theorem okSatisfies_bind (result : Except ε α) (next : α → Except ε β)
    (predicate : β → Prop) (valid : ∀ value, OkSatisfies predicate (next value)) :
    OkSatisfies predicate (result.bind next) := by
  cases result with
  | error error => trivial
  | ok value => exact valid value

private theorem okSatisfies_pure (predicate : α → Prop) (value : α) (valid : predicate value) :
    OkSatisfies predicate (Except.pure value : Except ε α) := valid

private theorem okSatisfies_throw (predicate : α → Prop) (error : ε) :
    OkSatisfies predicate (Except.error error : Except ε α) := trivial

private theorem okSatisfies_then (result : Except ε α) (next : Except ε β)
    (predicate : β → Prop) (valid : OkSatisfies predicate next) :
    OkSatisfies predicate (do
      let _ ← result
      next) := by
  exact okSatisfies_bind result (fun _ => next) predicate fun _ => valid

private theorem validatedResult_okSatisfies (update : DescriptorUpdate)
    (current : PropertyDescriptor) (kind : DescriptorKind) (predicate : PropertyDescriptor → Prop)
    (sameValid : predicate (applySameKind current update))
    (transitionValid : predicate (transition current kind update)) :
    OkSatisfies predicate (validatedResult current kind update) := by
  revert sameValid transitionValid
  cases current with
  | data data =>
      cases kind with
      | generic =>
          intro sameValid _
          exact okSatisfies_pure predicate _ sameValid
      | accessor =>
          intro _ transitionValid
          simp only [validatedResult]
          split
          · exact okSatisfies_pure predicate _ transitionValid
          · exact okSatisfies_throw predicate _
      | data =>
          intro sameValid _
          simp only [validatedResult]
          split
          · cases update.writable with
            | absent =>
                apply okSatisfies_then (predicate := predicate)
                split <;> apply okSatisfies_then (predicate := predicate) <;>
                  exact okSatisfies_pure predicate _ sameValid
            | present writable =>
                cases writable with
                | false =>
                    apply okSatisfies_then (predicate := predicate)
                    split <;> apply okSatisfies_then (predicate := predicate) <;>
                      exact okSatisfies_pure predicate _ sameValid
                | true =>
                    apply okSatisfies_then (predicate := predicate)
                    split <;> apply okSatisfies_then (predicate := predicate) <;>
                      exact okSatisfies_pure predicate _ sameValid
          · apply okSatisfies_then (predicate := predicate)
            exact okSatisfies_pure predicate _ sameValid
  | accessor accessor =>
      cases kind with
      | generic =>
          intro sameValid _
          exact okSatisfies_pure predicate _ sameValid
      | data =>
          intro _ transitionValid
          simp only [validatedResult]
          split
          · exact okSatisfies_pure predicate _ transitionValid
          · exact okSatisfies_throw predicate _
      | accessor =>
          intro sameValid _
          simp only [validatedResult]
          split <;> apply okSatisfies_then (predicate := predicate) <;>
            exact okSatisfies_pure predicate _ sameValid

private theorem existingChecks_okSatisfies (update : DescriptorUpdate)
    (current : PropertyDescriptor) (final : Except DescriptorRejection α)
    (predicate : α → Prop) (finalValid : OkSatisfies predicate final) :
    OkSatisfies predicate (do
      if !descriptorConfigurable current then
        match update.configurable with
        | .present true => throw .nonConfigurable
        | _ => pure ()
        if boolChanged (descriptorEnumerable current) update.enumerable then
          throw .nonConfigurable
      final) := by
  split
  · cases update.configurable with
    | absent =>
        apply okSatisfies_then (predicate := predicate)
        split <;> apply okSatisfies_then (predicate := predicate) <;> exact finalValid
    | present configurable =>
        cases configurable <;> apply okSatisfies_then (predicate := predicate) <;>
          (split <;> apply okSatisfies_then (predicate := predicate) <;> exact finalValid)
  · apply okSatisfies_then (predicate := predicate)
    exact finalValid

private theorem applyValidatedDescriptor_some_okSatisfies (update : DescriptorUpdate)
    (current : PropertyDescriptor) (extensible : Bool) (kind : DescriptorKind)
    (predicate : PropertyDescriptor → Prop)
    (sameValid : predicate (applySameKind current update))
    (transitionValid : predicate (transition current kind update)) :
    OkSatisfies predicate (update.applyValidatedDescriptor (some current) extensible kind) := by
  simp only [applyValidatedDescriptor]
  apply existingChecks_okSatisfies
  simpa only [validatedResult] using
    validatedResult_okSatisfies update current kind predicate sameValid transitionValid

/-- Successful validated descriptor application preserves all supplied reference-validity policies. -/
theorem applyValidatedDescriptor_referencesValid (update : DescriptorUpdate)
    (current : Option PropertyDescriptor) (extensible : Bool) (kind : DescriptorKind)
    (descriptor : PropertyDescriptor) (valueValid : Value → Prop) (accessorValid : RefId → Prop)
    (defaultValueValid : valueValid (.primitive .undefined))
    (updateValid : update.ReferencesValid valueValid accessorValid)
    (currentValid : match current with
      | none => True
      | some current => DescriptorReferencesValid valueValid accessorValid current)
    (applied : update.applyValidatedDescriptor current extensible kind = .ok descriptor) :
    DescriptorReferencesValid valueValid accessorValid descriptor := by
  let predicate := DescriptorReferencesValid valueValid accessorValid
  have preserved : OkSatisfies predicate
      (update.applyValidatedDescriptor current extensible kind) := by
    cases currentEq : current with
    | none =>
        cases extensible with
        | false =>
            simp only [applyValidatedDescriptor, Bool.false_eq_true, ↓reduceIte]
            exact okSatisfies_throw predicate _
        | true =>
            simp only [applyValidatedDescriptor, ↓reduceIte]
            exact okSatisfies_pure predicate _
              (newDescriptor_referencesValid update kind valueValid accessorValid defaultValueValid updateValid)
    | some previous =>
        simp only [currentEq] at currentValid
        have previousValid : predicate previous := currentValid
        have sameValid : predicate (applySameKind previous update) :=
          applySameKind_referencesValid update previous valueValid accessorValid updateValid previousValid
        have transitionedValid : predicate (transition previous kind update) :=
          transition_referencesValid update previous kind valueValid accessorValid defaultValueValid
            updateValid previousValid
        exact applyValidatedDescriptor_some_okSatisfies update previous extensible kind predicate
          sameValid transitionedValid
  rw [applied] at preserved
  exact preserved

end DescriptorUpdate
end TSLean.JS
