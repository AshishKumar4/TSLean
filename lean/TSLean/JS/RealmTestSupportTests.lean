import TSLean.JS.AbstractOperations

namespace TSLean.JS.RealmTestSupport

/-- Primitive wrapper family implemented by an explicit test builtin. -/
inductive WrapperFamily where
  | boolean
  | number
  | string
  | bigint
  | symbol
  deriving DecidableEq

/-- Builtin operation attached to a represented callable function reference. -/
inductive WrapperBuiltin where
  | valueOf (family : WrapperFamily)
  | toString (family : WrapperFamily)
  deriving DecidableEq

/-- Explicit function-reference registry used by the test evaluator boundary. -/
structure BuiltinRegistry where
  entries : List (RefId × WrapperBuiltin)

namespace BuiltinRegistry

private def lookup (registry : BuiltinRegistry) (ref : RefId) : Option WrapperBuiltin :=
  registry.entries.findSome? fun entry => if entry.1 = ref then some entry.2 else none

private def familyMatches : WrapperFamily → Primitive → Bool
  | .boolean, .boolean _ => true
  | .number, .number _ => true
  | .string, .string _ => true
  | .bigint, .bigint _ => true
  | .symbol, .symbol _ => true
  | _, _ => false

private def receiverPrimitive (family : WrapperFamily) (receiver : Value) : JSM P Primitive := do
  let primitive ← match receiver with
    | .primitive primitive => pure primitive
    | .object ref =>
        let heap ← JSM.readHeap
        match heap.get? ref with
        | .error fault => JSM.fail (.runtime (.heap fault))
        | .ok object =>
            match object.kind with
            | .primitiveWrapper slots => pure slots.value
            | _ => ObjectAccess.throwTypeError "incompatible wrapper receiver"
  if familyMatches family primitive then pure primitive
  else ObjectAccess.throwTypeError "incompatible wrapper receiver"

private def symbolString : SymbolId → JSString
  | _ => JSString.ofLeanString "Symbol()"

private def builtinToString : Primitive → JSM P JSString
  | .symbol id => pure (symbolString id)
  | primitive =>
      match primitive.toString with
      | .ok value => pure value
      | .error fault => JSM.throwJS fault.toThrownValue

/-- Evaluates only functions represented in the explicit builtin registry. -/
def bodyHook (registry : BuiltinRegistry) : BodyHook P := fun ref receiver _ => do
  match registry.lookup ref with
  | none => pure ()
  | some (.valueOf family) =>
      JSM.returnJS (.primitive (← receiverPrimitive family receiver))
  | some (.toString family) =>
      let primitive ← receiverPrimitive family receiver
      JSM.returnJS (.primitive (.string (← builtinToString primitive)))

end BuiltinRegistry

/-- A configured realm and the explicit builtin metadata installed on its primitive prototypes. -/
structure Fixture (P : Platform) where
  machine : Machine P
  intrinsics : RealmIntrinsics
  builtins : BuiltinRegistry

namespace Fixture

/-- The checked evaluator hook for the fixture's represented builtins. -/
def bodyHook (fixture : Fixture P) : BodyHook P := fixture.builtins.bodyHook

end Fixture

private def allocateObject (heap : Heap) (prototype : Option RefId := none) :
    Except RuntimeFault (RefId × Heap) :=
  heap.allocate prototype |>.mapError RuntimeFault.heap

private def allocateWrapper (heap : Heap) (primitive : Primitive) (prototype : RefId) :
    Except RuntimeFault (RefId × Heap) :=
  heap.allocatePrimitiveWrapper primitive (some prototype) |>.mapError RuntimeFault.heap

private def allocateMethod (machine : Machine P) (heap : Heap) :
    Except RuntimeFault (RefId × Heap) :=
  heap.allocateFunction machine.globalEnv .ordinary false none |>.mapError RuntimeFault.heap

private def defineMethod (heap : Heap) (prototype method : RefId) (name : String) :
    Except RuntimeFault Heap :=
  match heap.defineOwnProperty prototype (.string (JSString.ofLeanString name)) {
      value := .present (.object method)
      writable := .present true
      enumerable := .present false
      configurable := .present true } with
  | .ok (true, next) => .ok next
  | .ok (false, _) => .error .invalidRealmIntrinsics
  | .error (.heap fault) => .error (.heap fault)
  | .error _ => .error .invalidRealmIntrinsics

private def installFamily (machine : Machine P) (heap : Heap) (prototype : RefId)
    (family : WrapperFamily) : Except RuntimeFault (Heap × List (RefId × WrapperBuiltin)) := do
  let (valueOf, heap) ← allocateMethod machine heap
  let (toString, heap) ← allocateMethod machine heap
  let heap ← defineMethod heap prototype valueOf "valueOf"
  let heap ← defineMethod heap prototype toString "toString"
  pure (heap, [(valueOf, .valueOf family), (toString, .toString family)])

/-- Builds the represented primitive prototype hierarchy and installs checked builtin metadata. -/
def bootstrap (machine : Machine P) : Except RuntimeFault (Fixture P) := do
  let (objectPrototype, heap) ← allocateObject machine.heap
  let (booleanPrototype, heap) ← allocateWrapper heap (.boolean false) objectPrototype
  let (numberPrototype, heap) ← allocateWrapper heap (.number JSNumber.positiveZero) objectPrototype
  let (stringPrototype, heap) ← allocateWrapper heap
    (.string (JSString.ofLeanString "")) objectPrototype
  let (bigintPrototype, heap) ← allocateObject heap (some objectPrototype)
  let (symbolPrototype, heap) ← allocateObject heap (some objectPrototype)
  let intrinsics : RealmIntrinsics := {
    objectPrototype, booleanPrototype, numberPrototype, stringPrototype,
    bigintPrototype, symbolPrototype }
  let (heap, booleanBuiltins) ← installFamily machine heap booleanPrototype .boolean
  let (heap, numberBuiltins) ← installFamily machine heap numberPrototype .number
  let (heap, stringBuiltins) ← installFamily machine heap stringPrototype .string
  let (heap, bigintBuiltins) ← installFamily machine heap bigintPrototype .bigint
  let (heap, symbolBuiltins) ← installFamily machine heap symbolPrototype .symbol
  let machine ← (machine.setHeap heap).installRealmIntrinsics intrinsics
  pure ⟨machine, intrinsics, ⟨booleanBuiltins ++ numberBuiltins ++ stringBuiltins ++
    bigintBuiltins ++ symbolBuiltins⟩⟩

end TSLean.JS.RealmTestSupport
