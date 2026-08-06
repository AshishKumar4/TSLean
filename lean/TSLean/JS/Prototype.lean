import TSLean.JS.OrdinaryObject

namespace TSLean.JS

/-- Failures while traversing a prototype chain. -/
inductive PrototypeFault where
  | heap (fault : HeapFault)
  | cycleOrFuelExhausted
  deriving DecidableEq

namespace Prototype

private def lookupWithFuel (heap : Heap) (key : PropertyKey) : Nat → RefId →
    Except PrototypeFault (Option (RefId × PropertyDescriptor))
  | 0, _ => .error .cycleOrFuelExhausted
  | fuel + 1, ref =>
      match heap.get? ref with
      | .error fault => .error (.heap fault)
      | .ok object =>
          match object.properties.lookup key with
          | some descriptor => .ok (some (ref, descriptor))
          | none =>
              match object.prototype with
              | none => .ok none
              | some parent => lookupWithFuel heap key fuel parent

/-- Finds the nearest property; absence and exhausted malformed traversal are distinct. -/
def lookup (heap : Heap) (ref : RefId) (key : PropertyKey) :
    Except PrototypeFault (Option (RefId × PropertyDescriptor)) :=
  lookupWithFuel heap key (heap.size + 1) ref

/-- Validity and acyclicity of all prototype chains. -/
def WellFormed (heap : Heap) : Prop := heap.WellFormed

end Prototype
end TSLean.JS
