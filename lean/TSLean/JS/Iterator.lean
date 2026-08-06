import TSLean.JS.ObjectAccess

namespace TSLean.JS

/-- The observable payload of iterator `next`. Allocating ECMAScript iterator-result objects is a
later object-model boundary; iteration semantics do not depend on that wrapper identity. -/
structure IteratorResult where
  value : Value
  done : Bool
  deriving DecidableEq

namespace Iterator

private def undefined : Value := .primitive .undefined

private def heapFault (fault : HeapFault) : ModelFault := .runtime (.heap fault)

/-- Allocates a fresh array iterator with stable target identity. -/
def arrayValues (target : RefId) : JSM P RefId := fun machine =>
  match machine.heap.allocateArrayIterator target with
  | .error fault => .fault (heapFault fault) machine
  | .ok (iterator, heap) => .done (.normal iterator) (machine.setHeap heap)

/-- Advances an array iterator, re-reading target length and performing ordinary `Get` for every
index. Appends before completion are therefore visible, and holes materialize as `undefined`. -/
def next (hook : BodyHook P) (iterator : RefId) : JSM P IteratorResult := fun machine =>
  match machine.heap.advanceArrayIterator iterator with
  | .error fault => .fault (heapFault fault) machine
  | .ok (none, heap) => .done (.normal ⟨undefined, true⟩) (machine.setHeap heap)
  | .ok (some (target, index), heap) =>
      let nextMachine := machine.setHeap heap
      match ObjectAccess.get hook target (.string (PropertyKey.arrayIndexString index))
          (.object target) nextMachine with
      | .done (.normal value) finalMachine => .done (.normal ⟨value, false⟩) finalMachine
      | .done (.thrown value) finalMachine => .done (.thrown value) finalMachine
      | .done (.returned _) finalMachine | .done (.break _) finalMachine |
          .done (.continue _) finalMachine => .fault (.runtime .escapingFunctionControl) finalMachine
      | .exhausted finalMachine => .exhausted finalMachine
      | .fault fault finalMachine => .fault fault finalMachine

end Iterator
end TSLean.JS
