import TSLean.JS.AbstractEquality
import TSLean.JS.CoercionProgram
import TSLean.JS.HasInstance

namespace TSLean.JS.CoercionEffectsTests

private inductive Event where
  | get (ref : RefId) (key : PropertyKey) (receiver : Value)
  | call (callee : RefId) (receiver : Value) (arguments : Array Value)
  | isCallable (ref : RefId)
  | typeError (message : String)
  | throw (value : Value)
  | ordinaryHasInstance (constructor : RefId) (value : Value)
  deriving DecidableEq

private inductive ScriptError where
  | typeError (message : String)
  | thrown (value : Value)
  | exhausted
  deriving DecidableEq

private structure ScriptState where
  gets : List Value
  calls : List Value
  callables : List Bool
  events : List Event := []

private inductive ScriptResult (α : Type) where
  | ok (value : α) (state : ScriptState)
  | error (error : ScriptError) (state : ScriptState)

private def ScriptResult.events : ScriptResult α → List Event
  | .ok _ state | .error _ state => state.events

private abbrev ScriptM (α : Type) := ScriptState → ScriptResult α

private instance : Monad ScriptM where
  pure value state := .ok value state
  bind action next state :=
    match action state with
    | .ok value state => next value state
    | .error error state => .error error state

private def record (state : ScriptState) (event : Event) : ScriptState :=
  { state with events := state.events ++ [event] }

private def effects : CoercionEffects ScriptM where
  get ref key receiver state :=
    let state := record state (.get ref key receiver)
    match state.gets with
    | value :: rest => .ok value { state with gets := rest }
    | [] => .error .exhausted state
  call callee receiver arguments state :=
    let state := record state (.call callee receiver arguments)
    match state.calls with
    | value :: rest => .ok value { state with calls := rest }
    | [] => .error .exhausted state
  isCallable ref state :=
    let state := record state (.isCallable ref)
    match state.callables with
    | value :: rest => .ok value { state with callables := rest }
    | [] => .error .exhausted state
  typeError message state :=
    let state := record state (.typeError message)
    .error (.typeError message) state
  throw value state :=
    let state := record state (.throw value)
    .error (.thrown value) state

private def string (value : String) : Value :=
  .primitive (.string (JSString.ofLeanString value))

private def number (value : String) : Value :=
  .primitive (.number (JSNumber.parse (JSString.ofLeanString value)))

private def key (value : String) : PropertyKey :=
  .string (JSString.ofLeanString value)

private def exoticEvents (receiver method : RefId) (hint : String) : List Event := [
  .get receiver (.symbol (.wellKnown .toPrimitive)) (.object receiver),
  .isCallable method,
  .call method (.object receiver) #[.primitive (.string (JSString.ofLeanString hint))]]

/-- The exotic protocol reads the property, checks callability, and only then calls it. -/
theorem propertyGetBeforeCall :
    (AbstractOperations.toPrimitiveWith effects (.object ⟨1⟩) .number {
      gets := [.object ⟨2⟩], calls := [string "result"], callables := [true]
    }).events = exoticEvents ⟨1⟩ ⟨2⟩ "number" := by
  rfl

/-- A string hint tries `toString` before `valueOf`. -/
theorem stringHintMethodOrder :
    (AbstractOperations.ordinaryToPrimitiveWith effects ⟨3⟩ .string {
      gets := [.object ⟨4⟩, .object ⟨5⟩]
      calls := [.object ⟨3⟩, string "done"]
      callables := [true, true]
    }).events = [
      .get ⟨3⟩ (key "toString") (.object ⟨3⟩), .isCallable ⟨4⟩,
      .call ⟨4⟩ (.object ⟨3⟩) #[],
      .get ⟨3⟩ (key "valueOf") (.object ⟨3⟩), .isCallable ⟨5⟩,
      .call ⟨5⟩ (.object ⟨3⟩) #[]] := by
  rfl

/-- Number and default hints try `valueOf` before `toString`. -/
theorem numberHintMethodOrder :
    (AbstractOperations.ordinaryToPrimitiveWith effects ⟨3⟩ .number {
      gets := [.object ⟨4⟩, .object ⟨5⟩]
      calls := [.object ⟨3⟩, string "done"]
      callables := [true, true]
    }).events = [
      .get ⟨3⟩ (key "valueOf") (.object ⟨3⟩), .isCallable ⟨4⟩,
      .call ⟨4⟩ (.object ⟨3⟩) #[],
      .get ⟨3⟩ (key "toString") (.object ⟨3⟩), .isCallable ⟨5⟩,
      .call ⟨5⟩ (.object ⟨3⟩) #[]] := by
  rfl

/-- A default hint uses the same `valueOf`-before-`toString` order as a number hint. -/
theorem defaultHintMethodOrder :
    (AbstractOperations.ordinaryToPrimitiveWith effects ⟨3⟩ .default {
      gets := [.object ⟨4⟩, .object ⟨5⟩]
      calls := [.object ⟨3⟩, string "done"]
      callables := [true, true]
    }).events = [
      .get ⟨3⟩ (key "valueOf") (.object ⟨3⟩), .isCallable ⟨4⟩,
      .call ⟨4⟩ (.object ⟨3⟩) #[],
      .get ⟨3⟩ (key "toString") (.object ⟨3⟩), .isCallable ⟨5⟩,
      .call ⟨5⟩ (.object ⟨3⟩) #[]] := by
  rfl

/-- A primitive first-method result suppresses the second method. -/
theorem primitiveSkipsSecondMethod :
    (AbstractOperations.ordinaryToPrimitiveWith effects ⟨6⟩ .number {
      gets := [.object ⟨7⟩, .object ⟨8⟩]
      calls := [string "done", string "unused"]
      callables := [true, true]
    }).events = [
      .get ⟨6⟩ (key "valueOf") (.object ⟨6⟩), .isCallable ⟨7⟩,
      .call ⟨7⟩ (.object ⟨6⟩) #[]] := by
  rfl

/-- Failure in the first method call suppresses the second property read. -/
theorem failedCallSkipsSecondMethod :
    (AbstractOperations.ordinaryToPrimitiveWith effects ⟨9⟩ .number {
      gets := [.object ⟨10⟩, .object ⟨11⟩], calls := [], callables := [true, true]
    }).events = [
      .get ⟨9⟩ (key "valueOf") (.object ⟨9⟩), .isCallable ⟨10⟩,
      .call ⟨10⟩ (.object ⟨9⟩) #[]] := by
  rfl

/-- Addition completes all left coercion effects before beginning the right coercion. -/
theorem addCoercesLeftBeforeRight :
    (AbstractEquality.addWith effects (.object ⟨12⟩) (.object ⟨13⟩) {
      gets := [.object ⟨14⟩, .object ⟨15⟩]
      calls := [string "left", string "right"]
      callables := [true, true]
    }).events = exoticEvents ⟨12⟩ ⟨14⟩ "default" ++
      exoticEvents ⟨13⟩ ⟨15⟩ "default" := by
  rfl

/-- Relational coercion follows `leftFirst = false` by completing the right side first. -/
theorem relationalRightFirstOrder :
    (AbstractEquality.relationalComparisonWith effects (.object ⟨16⟩) (.object ⟨17⟩) false {
      gets := [.object ⟨19⟩, .object ⟨18⟩]
      calls := [number "2", number "1"]
      callables := [true, true]
    }).events = exoticEvents ⟨17⟩ ⟨19⟩ "number" ++
      exoticEvents ⟨16⟩ ⟨18⟩ "number" := by
  rfl

/-- Relational coercion follows `leftFirst = true` by completing the left side first. -/
theorem relationalLeftFirstOrder :
    (AbstractEquality.relationalComparisonWith effects (.object ⟨16⟩) (.object ⟨17⟩) true {
      gets := [.object ⟨18⟩, .object ⟨19⟩]
      calls := [number "1", number "2"]
      callables := [true, true]
    }).events = exoticEvents ⟨16⟩ ⟨18⟩ "number" ++
      exoticEvents ⟨17⟩ ⟨19⟩ "number" := by
  rfl

private def testExoticOrder : IO Unit := do
  let receiver : RefId := ⟨1⟩
  let method : RefId := ⟨2⟩
  let initial : ScriptState := {
    gets := [.object method]
    calls := [string "result"]
    callables := [true]
  }
  match AbstractOperations.toPrimitiveWith effects (.object receiver) .number initial with
  | .ok (.string result) final =>
      assert! result.equal (JSString.ofLeanString "result")
      assert! final.events = exoticEvents receiver method "number"
  | _ => assert! false

private def testOrdinaryOrder : IO Unit := do
  let receiver : RefId := ⟨3⟩
  let valueOf : RefId := ⟨4⟩
  let toString : RefId := ⟨5⟩
  let initial : ScriptState := {
    gets := [.object valueOf, .object toString]
    calls := [.object receiver, string "ordinary"]
    callables := [true, true]
  }
  match AbstractOperations.ordinaryToPrimitiveWith effects receiver .number initial with
  | .ok (.string result) final =>
      assert! result.equal (JSString.ofLeanString "ordinary")
      assert! final.events = [
        .get receiver (key "valueOf") (.object receiver),
        .isCallable valueOf,
        .call valueOf (.object receiver) #[],
        .get receiver (key "toString") (.object receiver),
        .isCallable toString,
        .call toString (.object receiver) #[]]
  | _ => assert! false

private def testErrorRetainsTrace : IO Unit := do
  let receiver : RefId := ⟨6⟩
  let method : RefId := ⟨7⟩
  let initial : ScriptState := {
    gets := [.object method]
    calls := [.object receiver]
    callables := [true]
  }
  match AbstractOperations.toPrimitiveWith effects (.object receiver) .default initial with
  | .error (.typeError message) final =>
      assert! message = "Symbol.toPrimitive returned an object"
      assert! final.events = exoticEvents receiver method "default" ++ [
        .typeError "Symbol.toPrimitive returned an object"]
  | _ => assert! false

private def testCoercionThrow : IO Unit := do
  let initial : ScriptState := { gets := [], calls := [], callables := [] }
  let thrown := CoercionFault.symbolToNumber.toThrownValue
  match AbstractOperations.toNumberWith effects
      (.primitive (.symbol (.allocated 9))) initial with
  | .error (.thrown value) final =>
      assert! value = thrown
      assert! final.events = [.throw thrown]
  | _ => assert! false
  let suppressed : ScriptM Unit := do
    let _ ← (CoercionEffects.fromCoercion effects (.error .symbolToNumber) : ScriptM JSNumber)
    let _ ← effects.get ⟨99⟩ (key "suppressed") (.object ⟨99⟩)
    pure ()
  match suppressed { initial with gets := [.primitive .undefined] } with
  | .error (.thrown value) final =>
      assert! value = thrown
      assert! final.events = [.throw thrown]
  | _ => assert! false

private def testFailureSuppressesLaterEffects : IO Unit := do
  let left : RefId := ⟨8⟩
  let right : RefId := ⟨9⟩
  let method : RefId := ⟨10⟩
  let initial : ScriptState := {
    gets := [.object method, .primitive .undefined]
    calls := []
    callables := [false]
  }
  match AbstractEquality.addWith effects (.object left) (.object right) initial with
  | .error (.typeError message) final =>
      assert! message = "property is not callable"
      assert! final.events = [
        .get left (.symbol (.wellKnown .toPrimitive)) (.object left),
        .isCallable method,
        .typeError "property is not callable"]
  | _ => assert! false

private def testLooseEqualWith : IO Unit := do
  let receiver : RefId := ⟨11⟩
  let method : RefId := ⟨12⟩
  let initial : ScriptState := {
    gets := [.object method]
    calls := [string "5"]
    callables := [true]
  }
  match AbstractEquality.looseEqualWith effects (.object receiver) (string "5") initial with
  | .ok true final => assert! final.events = exoticEvents receiver method "default"
  | _ => assert! false

private def testAddLeftBeforeRight : IO Unit := do
  let left : RefId := ⟨13⟩
  let right : RefId := ⟨14⟩
  let leftMethod : RefId := ⟨15⟩
  let rightMethod : RefId := ⟨16⟩
  let initial : ScriptState := {
    gets := [.object leftMethod, .object rightMethod]
    calls := [string "left", string "right"]
    callables := [true, true]
  }
  match AbstractEquality.addWith effects (.object left) (.object right) initial with
  | .ok result final =>
      assert! result = string "leftright"
      assert! final.events =
        exoticEvents left leftMethod "default" ++ exoticEvents right rightMethod "default"
  | _ => assert! false

private def testRelationalOrder : IO Unit := do
  let left : RefId := ⟨17⟩
  let right : RefId := ⟨18⟩
  let leftMethod : RefId := ⟨19⟩
  let rightMethod : RefId := ⟨20⟩
  let leftFirst : ScriptState := {
    gets := [.object leftMethod, .object rightMethod]
    calls := [number "1", number "2"]
    callables := [true, true]
  }
  match AbstractEquality.relationalComparisonWith effects
      (.object left) (.object right) true leftFirst with
  | .ok (some true) final =>
      assert! final.events =
        exoticEvents left leftMethod "number" ++ exoticEvents right rightMethod "number"
  | _ => assert! false
  let rightFirst : ScriptState := {
    gets := [.object rightMethod, .object leftMethod]
    calls := [number "2", number "1"]
    callables := [true, true]
  }
  match AbstractEquality.relationalComparisonWith effects
      (.object left) (.object right) false rightFirst with
  | .ok (some true) final =>
      assert! final.events =
        exoticEvents right rightMethod "number" ++ exoticEvents left leftMethod "number"
  | _ => assert! false

private def ordinaryHasInstance (result : Bool) (constructor : RefId)
    (value : Value) : ScriptM Bool := fun state =>
  .ok result (record state (.ordinaryHasInstance constructor value))

/-- Custom `@@hasInstance` dispatch performs get/check/call and suppresses ordinary fallback. -/
theorem customHasInstanceSuppressesFallback :
    (Instanceof.instanceofOperatorWith effects (ordinaryHasInstance false)
      (.object ⟨23⟩) (.object ⟨21⟩) {
        gets := [.object ⟨22⟩]
        calls := [.primitive (.boolean true)]
        callables := [true]
      }).events = [
        .get ⟨21⟩ (.symbol (.wellKnown .hasInstance)) (.object ⟨21⟩),
        .isCallable ⟨22⟩,
        .call ⟨22⟩ (.object ⟨21⟩) #[.object ⟨23⟩]] := by
  rfl

/-- Missing custom `@@hasInstance` dispatch checks callability before ordinary fallback. -/
theorem absentHasInstanceUsesOrderedFallback :
    (Instanceof.instanceofOperatorWith effects (ordinaryHasInstance true)
      (.object ⟨23⟩) (.object ⟨21⟩) {
        gets := [.primitive .undefined]
        calls := []
        callables := [true]
      }).events = [
        .get ⟨21⟩ (.symbol (.wellKnown .hasInstance)) (.object ⟨21⟩),
        .isCallable ⟨21⟩,
        .ordinaryHasInstance ⟨21⟩ (.object ⟨23⟩)] := by
  rfl

private def testInstanceofDispatch : IO Unit := do
  let constructor : RefId := ⟨21⟩
  let method : RefId := ⟨22⟩
  let value : Value := .object ⟨23⟩
  let custom : ScriptState := {
    gets := [.object method]
    calls := [.primitive (.boolean true)]
    callables := [true]
  }
  match Instanceof.instanceofOperatorWith effects (ordinaryHasInstance false)
      value (.object constructor) custom with
  | .ok true final =>
      assert! final.events = [
        .get constructor (.symbol (.wellKnown .hasInstance)) (.object constructor),
        .isCallable method,
        .call method (.object constructor) #[value]]
  | _ => assert! false
  let fallback : ScriptState := {
    gets := [.primitive .undefined]
    calls := []
    callables := [true]
  }
  match Instanceof.instanceofOperatorWith effects (ordinaryHasInstance true)
      value (.object constructor) fallback with
  | .ok true final =>
      assert! final.events = [
        .get constructor (.symbol (.wellKnown .hasInstance)) (.object constructor),
        .isCallable constructor,
        .ordinaryHasInstance constructor value]
  | _ => assert! false

private def specializationPlatform : Platform := ScriptedPlatform.make {
  times := #[], randoms := #[], fetches := #[]
}

private def specializationHook : BodyHook specializationPlatform := fun _ _ _ => pure ()

private def testSpecializationEquality : IO Unit := do
  let machine := Machine.initial specializationPlatform 1
  -- The required equivalence is extensional `JSM` behavior, not compiled C byte identity.
  let publicAction := AbstractOperations.toNumber specializationHook (.primitive (.boolean true))
  let genericAction := AbstractOperations.toNumberWith (CoercionEffects.forJSM specializationHook)
    (.primitive (.boolean true))
  have actionsEqual : publicAction = genericAction := rfl
  match actionsEqual with
  | rfl =>
      let publicResult := publicAction machine
      let genericResult := genericAction machine
      match publicResult, genericResult with
      | .done (.normal publicValue) publicMachine, .done (.normal genericValue) genericMachine =>
          assert! publicValue = genericValue
          assert! publicMachine.heap.size = genericMachine.heap.size
          assert! publicMachine.fuel = genericMachine.fuel
          assert! publicMachine.trace = genericMachine.trace
      | _, _ => assert! false

def run : IO Unit := do
  testExoticOrder
  testOrdinaryOrder
  testErrorRetainsTrace
  testCoercionThrow
  testFailureSuppressesLaterEffects
  testLooseEqualWith
  testAddLeftBeforeRight
  testRelationalOrder
  testInstanceofDispatch
  testSpecializationEquality

end TSLean.JS.CoercionEffectsTests
