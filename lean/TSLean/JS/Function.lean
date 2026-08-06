import TSLean.JS.ObjectAccess

namespace TSLean.JS

/-- Placement of a class method definition. -/
inductive ClassMethodPlacement where
  | instance
  | static
  deriving DecidableEq

/-- Class element descriptor kind. -/
inductive ClassElementKind where
  | method
  | getter
  | setter
  deriving DecidableEq

/-- A class element whose body is supplied later through `BodyHook`. -/
structure ClassElementDefinition where
  key : PropertyKey
  placement : ClassMethodPlacement
  kind : ClassElementKind := .method
  deriving DecidableEq

/-- ECMAScript class heritage after evaluation. -/
inductive ClassHeritage where
  | base
  | null
  | extends (constructor : RefId)
  deriving DecidableEq

/-- Stable constructor, prototype, and element-function references from one class allocation. -/
structure ClassAllocation where
  constructor : RefId
  prototype : RefId
  elements : Array RefId
  deriving DecidableEq

namespace Function

private def typeError (message : String) : Value :=
  .primitive (.string (JSString.ofLeanString ("TypeError: " ++ message)))

private def invalidEnvironment (id : EnvId) : ModelFault := .runtime (.invalidEnvironment id)

private def heapFault (fault : HeapFault) : ModelFault := .runtime (.heap fault)

private def validateEnvironment (machine : Machine P) (environment : EnvId) : Except ModelFault Unit :=
  match machine.getEnvironment environment with
  | .ok _ => .ok ()
  | .error _ => .error (invalidEnvironment environment)

private def commitAllocation (environment : EnvId)
    (allocate : Heap → Except HeapFault (RefId × Heap)) : JSM P RefId := fun machine =>
  match validateEnvironment machine environment with
  | .error fault => .fault fault machine
  | .ok () =>
      match allocate machine.heap with
      | .error fault => .fault (heapFault fault) machine
      | .ok (ref, heap) => .done (.normal ref) (machine.setHeap heap)

/-- Allocates a nonconstructible ordinary callable, such as a concise method. -/
def allocateOrdinary (environment : EnvId) (functionPrototype : Option RefId)
    (homeObject : Option RefId := none) : JSM P RefId :=
  commitAllocation environment fun heap =>
    heap.allocateFunction environment .ordinary false functionPrototype homeObject

/-- Allocates a nonconstructible arrow callable with validated lexical `this`. -/
def allocateArrow (environment : EnvId) (functionPrototype : Option RefId)
    (lexicalThis : Value) : JSM P RefId :=
  commitAllocation environment fun heap =>
    heap.allocateFunction environment .arrow false functionPrototype none .base (some lexicalThis)

/-- Allocates a constructible ordinary callable without creating an own `prototype` property,
covering bound or host constructors whose prototype is supplied dynamically. -/
def allocateBareConstructor (environment : EnvId) (functionPrototype : Option RefId) : JSM P RefId :=
  commitAllocation environment fun heap =>
    heap.allocateFunction environment .ordinary true functionPrototype

/-- Atomically allocates a constructible ordinary function and its fresh prototype object. -/
def allocateConstructor (environment : EnvId) (functionPrototype objectPrototype : Option RefId) :
    JSM P (RefId × RefId) := fun machine =>
  match validateEnvironment machine environment with
  | .error fault => .fault fault machine
  | .ok () =>
      match machine.heap.allocateConstructorPair environment functionPrototype objectPrototype with
      | .error fault => .fault (heapFault fault) machine
      | .ok (constructor, prototype, heap) =>
          .done (.normal (constructor, prototype)) (machine.setHeap heap)

private structure ClassParents where
  constructorPrototype : Option RefId
  instancePrototype : Option RefId
  constructorMode : ConstructorMode

private def classParents (hook : BodyHook P) (heritage : ClassHeritage)
    (functionPrototype objectPrototype : RefId) : JSM P ClassParents :=
  match heritage with
  | .base => pure ⟨some functionPrototype, some objectPrototype, .base⟩
  | .null => pure ⟨some functionPrototype, none, .derived⟩
  | .extends constructor => do
      let heap ← JSM.readHeap
      match heap.isConstructor constructor with
      | .error fault => JSM.fail (heapFault fault)
      | .ok false => JSM.throwJS (typeError "class heritage is not a constructor")
      | .ok true =>
          let value ← ObjectAccess.get hook constructor
            (.string (JSString.ofLeanString "prototype")) (.object constructor)
          match value with
          | .object prototype => pure ⟨some constructor, some prototype, .derived⟩
          | .primitive .null => pure ⟨some constructor, none, .derived⟩
          | .primitive _ => JSM.throwJS (typeError "class heritage prototype is not an object or null")

private def defineElement (heap : Heap) (target method : RefId)
    (definition : ClassElementDefinition) :
    Except HeapFault Heap :=
  let update : DescriptorUpdate := match definition.kind with
    | .method => {
        value := .present (.object method)
        writable := .present true
        enumerable := .present false
        configurable := .present true }
    | .getter => {
        get := .present (some method)
        enumerable := .present false
        configurable := .present true }
    | .setter => {
        set := .present (some method)
        enumerable := .present false
        configurable := .present true }
  match heap.defineOwnProperty target definition.key update with
  | .ok (true, next) => .ok next
  | .ok (false, _) => .error .cycleOrFuelExhausted
  | .error (.heap fault) => .error fault
  | .error (.invalidValueRef ref) => .error (.invalidRef ref)
  | .error _ => .error .cycleOrFuelExhausted

private def allocateElements (environment : EnvId) (functionPrototype : RefId)
    (constructor prototype : RefId) (definitions : List ClassElementDefinition)
    (heap : Heap) (elements : Array RefId := #[]) : Except HeapFault (Array RefId × Heap) := do
  match definitions with
  | [] => pure (elements, heap)
  | definition :: rest =>
      let target := match definition.placement with
        | .instance => prototype
        | .static => constructor
      let (method, withMethod) ← heap.allocateFunction environment .ordinary false
        (some functionPrototype) (some target)
      let withProperty ← defineElement withMethod target method definition
      allocateElements environment functionPrototype constructor prototype rest
        withProperty (elements.push method)

/-- After heritage evaluation succeeds, atomically allocates the constructor/prototype pair and
nonenumerable elements. Heritage accessor effects remain committed if later allocation rejects. -/
def allocateClass (hook : BodyHook P) (environment : EnvId)
    (functionPrototype objectPrototype : RefId) (heritage : ClassHeritage)
    (elements : Array ClassElementDefinition := #[]) : JSM P ClassAllocation := fun machine =>
  match validateEnvironment machine environment with
  | .error fault => .fault fault machine
  | .ok () =>
      match machine.heap.get? functionPrototype, machine.heap.get? objectPrototype with
      | .error fault, _ | _, .error fault => .fault (heapFault fault) machine
      | .ok _, .ok _ => match classParents hook heritage functionPrototype objectPrototype machine with
      | .done (.normal parents) afterHeritage =>
          match afterHeritage.heap.allocateConstructorPair environment parents.constructorPrototype
              parents.instancePrototype true parents.constructorMode with
          | .error fault => .fault (heapFault fault) afterHeritage
          | .ok (constructor, prototype, pairedHeap) =>
              match allocateElements environment functionPrototype constructor prototype
                  elements.toList pairedHeap with
              | .error fault => .fault (heapFault fault) afterHeritage
              | .ok (elementRefs, heap) =>
                  .done (.normal ⟨constructor, prototype, elementRefs⟩) (afterHeritage.setHeap heap)
      | .done (.thrown value) next => .done (.thrown value) next
      | .done (.returned _) next | .done (.break _) next | .done (.continue _) next =>
          .fault (.runtime .escapingFunctionControl) next
      | .exhausted next => .exhausted next
      | .fault fault next => .fault fault next

/-- Applies the ECMAScript constructor-result override rule without evaluating a body. -/
def constructorResult (instanceRef : RefId) : Value → Value
  | .object ref => .object ref
  | .primitive _ => .object instanceRef

end Function
end TSLean.JS
