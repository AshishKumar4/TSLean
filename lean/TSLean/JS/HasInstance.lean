import TSLean.JS.AbstractOperations

namespace TSLean.JS

namespace Instanceof

private def typeError (message : String) : Value :=
  .primitive (.string (JSString.ofLeanString ("TypeError: " ++ message)))

private def heapFault (fault : HeapFault) : ModelFault := .runtime (.heap fault)

/-- Bounded prototype reachability by reference identity. -/
def reachesPrototype (heap : Heap) (target : RefId) : Nat → RefId → Except HeapFault Bool
  | 0, _ => .error .cycleOrFuelExhausted
  | fuel + 1, ref => do
      let object ← heap.get? ref
      match object.prototype with
      | none => pure false
      | some parent =>
          if parent = target then pure true
          else reachesPrototype heap target fuel parent

/-- ECMAScript ordinary `instanceof` for represented ordinary function objects. -/
def ordinaryHasInstance (hook : BodyHook P) (constructor : RefId) (value : Value) : JSM P Bool :=
  fun machine =>
    match machine.heap.isCallable constructor with
    | .error fault => .fault (heapFault fault) machine
    | .ok false => .done (.normal false) machine
    | .ok true =>
        match value with
        | .primitive _ => .done (.normal false) machine
        | .object object =>
            match machine.heap.get? object with
            | .error fault => .fault (heapFault fault) machine
            | .ok _ =>
                match ObjectAccess.get hook constructor
                    (.string (JSString.ofLeanString "prototype")) (.object constructor) machine with
                | .done (.normal (.object prototype)) next =>
                    match reachesPrototype next.heap prototype (next.heap.size + 1) object with
                    | .ok result => .done (.normal result) next
                    | .error fault => .fault (heapFault fault) next
                | .done (.normal (.primitive _)) next =>
                    .done (.thrown (typeError "constructor prototype is not an object")) next
                | .done (.thrown thrown) next => .done (.thrown thrown) next
                | .done (.returned _) next | .done (.break _) next | .done (.continue _) next =>
                    .fault (.runtime .escapingFunctionControl) next
                | .exhausted next => .exhausted next
                | .fault fault next => .fault fault next

/-- Preservation and escaping-result validity required at the atomic ordinary-instance boundary. -/
def OrdinaryHasInstanceContract (ordinary : RefId → Value → JSM P Bool) : Prop :=
  ∀ constructor value,
    JSM.PreservesResults (fun _ _ => True) (ordinary constructor value)

/-- Production ordinary-instance dispatch satisfies its atomic boundary contract. -/
theorem ordinaryHasInstance_contract (hook : BodyHook P)
    (hookPreserves : BodyHookPreservesWellFormed hook) :
    OrdinaryHasInstanceContract (ordinaryHasInstance hook) := by
  intro constructor value
  constructor
  · intro machine valid
    unfold ordinaryHasInstance
    cases callableResult : machine.heap.isCallable constructor with
    | error fault => exact ⟨valid, machine.continuesFrom_refl⟩
    | ok isCallable =>
      clear callableResult
      cases isCallable with
      | false => simp; exact ⟨valid, machine.continuesFrom_refl⟩
      | true =>
        cases value with
        | primitive primitive => simp; exact ⟨valid, machine.continuesFrom_refl⟩
        | object object =>
            cases found : machine.heap.get? object with
            | error fault => simp [found]; exact ⟨valid, machine.continuesFrom_refl⟩
            | ok record =>
                have preserved := ObjectAccess.get_preservesWellFormed hook constructor
                  (.string (JSString.ofLeanString "prototype")) (.object constructor)
                  hookPreserves machine valid
                cases getRun : ObjectAccess.get hook constructor
                    (.string (JSString.ofLeanString "prototype")) (.object constructor) machine with
                | done completion next =>
                    rw [getRun] at preserved
                    cases completion with
                    | normal result =>
                        cases result with
                        | primitive primitive => simpa [found, getRun] using preserved
                        | object prototype =>
                            cases reached : reachesPrototype next.heap prototype
                                (next.heap.size + 1) object <;>
                              simpa [found, getRun, reached] using preserved
                    | returned returned | thrown thrown | «break» label | «continue» label =>
                        simpa [found, getRun] using preserved
                | exhausted next | fault fault next => simpa [found, getRun] using preserved
  · intro machine valid
    unfold ordinaryHasInstance
    cases callableResult : machine.heap.isCallable constructor with
    | error fault => trivial
    | ok isCallable =>
      clear callableResult
      cases isCallable with
      | false => simp [RunResult.CompletionValuesValid]
      | true =>
        cases value with
        | primitive primitive => simp [RunResult.CompletionValuesValid]
        | object object =>
            cases found : machine.heap.get? object with
            | error fault => simp [found, RunResult.CompletionValuesValid]
            | ok record =>
                have results := (ObjectAccess.get_preservesResults hook constructor
                  (.string (JSString.ofLeanString "prototype")) (.object constructor)
                  hookPreserves).2 machine valid
                cases getRun : ObjectAccess.get hook constructor
                    (.string (JSString.ofLeanString "prototype")) (.object constructor) machine with
                | done completion next =>
                    rw [getRun] at results
                    cases completion with
                    | normal result =>
                        cases result with
                        | primitive primitive =>
                            simp [found, RunResult.CompletionValuesValid, typeError,
                              Heap.valueValid]
                        | object prototype =>
                            cases reached : reachesPrototype next.heap prototype
                              (next.heap.size + 1) object <;>
                              simp [found, reached, RunResult.CompletionValuesValid]
                    | thrown thrown => simpa [found] using results
                    | returned returned | «break» label | «continue» label =>
                        simp [found, RunResult.CompletionValuesValid]
                | exhausted next | fault fault next =>
                    simp [found, RunResult.CompletionValuesValid]

/-- Built-in `Function.prototype[Symbol.hasInstance]`, excluding unrepresented bound exotica. -/
def functionPrototypeHasInstance (hook : BodyHook P) (thisValue value : Value) : JSM P Bool :=
  match thisValue with
  | .object constructor => ordinaryHasInstance hook constructor value
  | .primitive _ => pure false

/-- ECMAScript `instanceof` dispatch through generic coercion effects and an ordinary fallback. -/
def instanceofOperatorWith [Monad m] (effects : CoercionEffects m)
    (ordinary : RefId → Value → m Bool) (value constructor : Value) : m Bool :=
  match constructor with
  | .primitive _ =>
      CoercionEffects.raiseTypeError effects "right-hand side of instanceof is not an object"
  | .object constructorRef => do
      match ← AbstractOperations.getMethodWith effects constructorRef (.symbol (.wellKnown .hasInstance)) with
      | some method =>
          let result ← effects.call method constructor #[value]
          pure result.toBoolean
      | none =>
          if ← effects.isCallable constructorRef then ordinary constructorRef value
          else CoercionEffects.raiseTypeError effects "right-hand side is not callable"

/-- ECMAScript `instanceof`, including observable custom `Symbol.hasInstance` dispatch. -/
@[inline]
def instanceofOperator (hook : BodyHook P) (value constructor : Value) : JSM P Bool :=
  instanceofOperatorWith (CoercionEffects.forJSM hook) (ordinaryHasInstance hook) value constructor

end Instanceof
end TSLean.JS
