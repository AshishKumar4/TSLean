import TSLean.JS.Heap

namespace TSLean.JS

/-! Read-only ordinary-object operations. Semantic mutations are owned by `Heap`. -/

namespace OrdinaryObject

/-- Reads an own property descriptor. -/
def getOwnProperty (heap : Heap) (ref : RefId) (key : PropertyKey) :
    Except HeapFault (Option PropertyDescriptor) := do
  let object ← heap.get? ref
  pure (object.properties.lookup key)

/-- Returns own property keys in ECMAScript order. -/
def ownPropertyKeys (heap : Heap) (ref : RefId) : Except HeapFault (List PropertyKey) := do
  let object ← heap.get? ref
  pure object.properties.ownKeys

end OrdinaryObject
end TSLean.JS
