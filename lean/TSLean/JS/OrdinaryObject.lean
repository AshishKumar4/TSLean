import TSLean.JS.Heap

namespace TSLean.JS

/-! Read-only ordinary-object operations. Semantic mutations are owned by `Heap`. -/

namespace OrdinaryObject

/-- Reads an own property descriptor. -/
def getOwnProperty (heap : Heap) (ref : RefId) (key : PropertyKey) :
    Except HeapFault (Option PropertyDescriptor) := heap.getOwnProperty ref key

/-- Returns own property keys in ECMAScript order. -/
def ownPropertyKeys (heap : Heap) (ref : RefId) : Except HeapFault (List PropertyKey) := do
  heap.ownPropertyKeys ref

end OrdinaryObject
end TSLean.JS
