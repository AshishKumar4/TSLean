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

end DescriptorUpdate
end TSLean.JS
