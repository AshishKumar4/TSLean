import TSLean.JS.Iterator

namespace TSLean.JS

namespace ArrayCopy

private def heapFault (fault : HeapFault) : ModelFault := .runtime (.heap fault)

private def allocateCollected (prototype : Option RefId) (values : List (Option Value)) :
    JSM P RefId := fun machine =>
  match machine.heap.allocateArray values.reverse prototype with
  | .error (.heap fault) => .fault (heapFault fault) machine
  | .error (.invalidValueRef ref) | .error (.invalidAccessor ref) |
      .error (.nonCallableAccessor ref) => .fault (heapFault (.invalidRef ref)) machine
  | .error (.arrayTooLong _) | .error (.invalidArrayLength _) =>
      ObjectAccess.throwRangeError "invalid array length" machine
  | .error (.invalidArrayLengthValue _) | .error (.syntax _) =>
      ObjectAccess.throwTypeError "invalid array allocation" machine
  | .ok (ref, heap) => .done (.normal ref) (machine.setHeap heap)

private def collectSlice (hook : BodyHook P) (source : RefId) (stop : Nat) :
    Nat → List (Option Value) → JSM P (List (Option Value))
  | index, values =>
      if stop ≤ index then pure values
      else do
        let heap ← JSM.readHeap
        let key := PropertyKey.string (PropertyKey.arrayIndexString index)
        match Prototype.lookup heap source key with
        | .error (.heap fault) => JSM.fail (heapFault fault)
        | .error .cycleOrFuelExhausted => JSM.fail (heapFault .cycleOrFuelExhausted)
        | .ok none => collectSlice hook source stop (index + 1) (none :: values)
        | .ok (some _) =>
            let value ← ObjectAccess.get hook source key (.object source)
            collectSlice hook source stop (index + 1) (some value :: values)

/-- Creates a fresh array for `[start, end)`. Absent properties remain holes; inherited numeric
properties and accessors are observed as required by ordinary `Get`. Nested references are shared. -/
def slice (hook : BodyHook P) (source : RefId) (start : Nat := 0)
    (endIndex : Option Nat := none) : JSM P RefId := do
  let heap ← JSM.readHeap
  let length ← match heap.arrayLength source with
    | .ok length => pure length
    | .error fault => JSM.fail (heapFault fault)
  let first := min start length
  let stop := min (endIndex.getD length) length
  let values ← collectSlice hook source stop first []
  allocateCollected none values

private def collectIterator (hook : BodyHook P) (iterator : RefId) :
    Nat → List (Option Value) → JSM P (List (Option Value))
  | 0, _ => JSM.fail (heapFault .cycleOrFuelExhausted)
  | fuel + 1, values => do
      let result ← Iterator.next hook iterator
      if result.done then pure values
      else collectIterator hook iterator fuel (some result.value :: values)

/-- Consumes the live array iterator into a fresh array. Iterator `Get` turns holes into explicit
`undefined`, and length is re-read between steps so getter-driven appends are observed. -/
def spread (hook : BodyHook P) (source : RefId) : JSM P RefId := do
  let iterator ← Iterator.arrayValues source
  let values ← collectIterator hook iterator (Heap.maxArrayLength + 1) []
  allocateCollected none values

end ArrayCopy
end TSLean.JS
