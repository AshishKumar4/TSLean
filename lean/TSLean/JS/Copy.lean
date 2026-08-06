import TSLean.JS.ObjectAccess

namespace TSLean.JS

namespace Copy

private def heapFault (fault : HeapFault) : ModelFault := .runtime (.heap fault)

private def excluded (exclusions : List PropertyKey) (key : PropertyKey) : Bool :=
  exclusions.any (PropertyKey.equal key)

private def enumerable : PropertyDescriptor → Bool
  | .data descriptor => descriptor.enumerable
  | .accessor descriptor => descriptor.enumerable

private def createData (target : RefId) (key : PropertyKey) (value : Value) : JSM P Unit :=
  do
    if ← ObjectAccess.createDataProperty target key value then pure ()
    else ObjectAccess.throwTypeError "CreateDataProperty rejected"

private def copyKeys (hook : BodyHook P) (target source : RefId)
    (exclusions : List PropertyKey) : List PropertyKey → JSM P Unit
  | [] => pure ()
  | key :: rest => do
      if excluded exclusions key then copyKeys hook target source exclusions rest
      else
        let heap ← JSM.readHeap
        match OrdinaryObject.getOwnProperty heap source key with
        | .error fault => JSM.fail (heapFault fault)
        | .ok none => copyKeys hook target source exclusions rest
        | .ok (some descriptor) =>
            if !enumerable descriptor then copyKeys hook target source exclusions rest
            else
              let value ← ObjectAccess.get hook source key (.object source)
              createData target key value
              copyKeys hook target source exclusions rest

/-- Copies enumerable own properties from a snapshotted key list. Each descriptor and value is read
at its turn; accessors run, symbols participate, and nested object references remain unchanged. -/
def copyDataProperties (hook : BodyHook P) (target source : RefId)
    (exclusions : List PropertyKey := []) : JSM P Unit := do
  let heap ← JSM.readHeap
  match heap.get? target with
  | .error fault => JSM.fail (heapFault fault)
  | .ok _ => pure ()
  match heap.get? source with
  | .error fault => JSM.fail (heapFault fault)
  | .ok _ => pure ()
  match OrdinaryObject.ownPropertyKeys heap source with
  | .error fault => JSM.fail (heapFault fault)
  | .ok keys => copyKeys hook target source exclusions keys

private def assignKeys (hook : BodyHook P) (target source : RefId) :
    List PropertyKey → JSM P Unit
  | [] => pure ()
  | key :: rest => do
      let heap ← JSM.readHeap
      match OrdinaryObject.getOwnProperty heap source key with
      | .error fault => JSM.fail (heapFault fault)
      | .ok none => assignKeys hook target source rest
      | .ok (some descriptor) =>
          if !enumerable descriptor then assignKeys hook target source rest
          else
            let value ← ObjectAccess.get hook source key (.object source)
            ObjectAccess.setStrict hook target key value (.object target)
            assignKeys hook target source rest

private def boxPrimitive (value : Primitive) : JSM P RefId := fun machine =>
  match machine.heap.allocatePrimitiveWrapper value with
  | .ok (ref, heap) => .done (.normal ref) (machine.setHeap heap)
  | .error (.cannotBoxPrimitive _) =>
      ObjectAccess.throwTypeError "cannot convert nullish value to object" machine
  | .error fault => .fault (heapFault fault) machine

private def toObject : Value → JSM P RefId
  | .object ref => do
      let heap ← JSM.readHeap
      match heap.get? ref with
      | .ok _ => pure ref
      | .error fault => JSM.fail (heapFault fault)
  | .primitive value => boxPrimitive value

private def assignSource (hook : BodyHook P) (target : RefId) : Value → JSM P Unit
  | .primitive .null | .primitive .undefined => pure ()
  | sourceValue => do
      let source ← toObject sourceValue
      let heap ← JSM.readHeap
      match OrdinaryObject.ownPropertyKeys heap source with
      | .error fault => JSM.fail (heapFault fault)
      | .ok keys => assignKeys hook target source keys

private def assignSources (hook : BodyHook P) (target : RefId) : List Value → JSM P Unit
  | [] => pure ()
  | source :: rest => do
      assignSource hook target source
      assignSources hook target rest

/-- Mutates an object target or a fresh wrapper for a primitive target and returns that same object.
Nullish targets throw TypeError; nullish sources are skipped and all other primitives are boxed. -/
def objectAssign (hook : BodyHook P) (target : Value) (sources : List Value) : JSM P Value :=
  match target with
  | .primitive .null | .primitive .undefined =>
      ObjectAccess.throwTypeError "cannot convert nullish target to object"
  | .primitive primitive => do
      let targetRef ← boxPrimitive primitive
      assignSources hook targetRef sources
      pure (.object targetRef)
  | .object targetRef => do
      let heap ← JSM.readHeap
      match heap.get? targetRef with
      | .error fault => JSM.fail (heapFault fault)
      | .ok _ => pure ()
      assignSources hook targetRef sources
      pure target

private def spreadSources (hook : BodyHook P) (target : RefId)
    (exclusions : List PropertyKey) : List Value → JSM P Unit
  | [] => pure ()
  | .primitive .null :: rest | .primitive .undefined :: rest =>
      spreadSources hook target exclusions rest
  | sourceValue :: rest => do
      let source ← toObject sourceValue
      copyDataProperties hook target source exclusions
      spreadSources hook target exclusions rest

/-- Allocates a fresh ordinary object and copies sources left-to-right with CreateDataProperty, so
target prototype setters cannot intercept writes and source prototypes are not copied. -/
def objectSpread (hook : BodyHook P) (sources : List Value)
    (exclusions : List PropertyKey := []) : JSM P RefId := fun machine =>
  match machine.heap.allocate none true with
  | .error fault => .fault (heapFault fault) machine
  | .ok (target, heap) =>
      match spreadSources hook target exclusions sources (machine.setHeap heap) with
      | .done (.normal ()) next => .done (.normal target) next
      | .done (.thrown value) next => .done (.thrown value) next
      | .done (.returned _) next | .done (.break _) next | .done (.continue _) next =>
          .fault (.runtime .escapingFunctionControl) next
      | .exhausted next => .exhausted next
      | .fault fault next => .fault fault next

end Copy
end TSLean.JS
