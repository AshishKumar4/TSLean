import TSLean.JS.Control
import TSLean.JS.External

namespace TSLean.JS

/-- Left identity for the executable state/completion bind. -/
theorem JSM.pure_bind (value : α) (next : α → JSM P β) :
    (JSM.pure value).bind next = next value := rfl

/-- Right identity for the executable state/completion bind. -/
theorem JSM.bind_pure (action : JSM P α) :
    action.bind JSM.pure = action := by
  funext machine
  unfold JSM.bind
  cases result : action machine with
  | done completion next => cases completion <;> rfl
  | exhausted next => rfl
  | fault fault next => rfl

/-- Associativity for the executable state/completion bind. -/
theorem JSM.bind_assoc (action : JSM P α) (next : α → JSM P β)
    (last : β → JSM P γ) :
    (action.bind next).bind last =
      action.bind (fun value => (next value).bind last) := by
  funext machine
  unfold JSM.bind
  cases actionResult : action machine with
  | done completion nextMachine =>
      cases completion with
      | normal value =>
          cases nextResult : next value nextMachine with
          | done nextCompletion lastMachine => cases nextCompletion <;> rfl
          | exhausted lastMachine => rfl
          | fault fault lastMachine => rfl
      | returned value => rfl
      | thrown value => rfl
      | «break» label => rfl
      | «continue» label => rfl
  | exhausted nextMachine => rfl
  | fault fault nextMachine => rfl

/-- Bind preserves return completion without invoking its continuation. -/
theorem Completion.bind_returned (value : Value) (next : α → Completion β) :
    Completion.bind (.returned value) next = .returned value := rfl

/-- Bind preserves throw completion without invoking its continuation. -/
theorem Completion.bind_thrown (value : Value) (next : α → Completion β) :
    Completion.bind (.thrown value) next = .thrown value := rfl

/-- Bind preserves break completion without invoking its continuation. -/
theorem Completion.bind_break (label : Option JSString) (next : α → Completion β) :
    Completion.bind (.break label) next = .break label := rfl

/-- Bind preserves continue completion without invoking its continuation. -/
theorem Completion.bind_continue (label : Option JSString) (next : α → Completion β) :
    Completion.bind (.continue label) next = .continue label := rfl

/-- Catch invokes its handler for throw completion. -/
theorem Control.tryCatch_thrown (handler : Value → JSM P α) (value : Value) (machine next : Machine P)
    (action : JSM P α) (result : action machine = .done (.thrown value) next) :
    Control.tryCatch action handler machine = handler value next := by
  simp [Control.tryCatch, result]

/-- Catch preserves return completion. -/
theorem Control.tryCatch_returned (handler : Value → JSM P α) (value : Value)
    (machine next : Machine P) (action : JSM P α)
    (result : action machine = .done (.returned value) next) :
    Control.tryCatch action handler machine = .done (.returned value) next := by
  simp [Control.tryCatch, result]

/-- Normal finally completion preserves a normal prior completion. -/
theorem Completion.finally_normal_normal (value : α) :
    Completion.finallyOverride (.normal value) (.normal ()) = .normal value := rfl

/-- Normal finally completion preserves return. -/
theorem Completion.finally_normal_returned (value : Value) :
    Completion.finallyOverride (.returned value : Completion α) (.normal ()) = .returned value := rfl

/-- Normal finally completion preserves throw. -/
theorem Completion.finally_normal_thrown (value : Value) :
    Completion.finallyOverride (.thrown value : Completion α) (.normal ()) = .thrown value := rfl

/-- Normal finally completion preserves break. -/
theorem Completion.finally_normal_break (label : Option JSString) :
    Completion.finallyOverride (.break label : Completion α) (.normal ()) = .break label := rfl

/-- Normal finally completion preserves continue. -/
theorem Completion.finally_normal_continue (label : Option JSString) :
    Completion.finallyOverride (.continue label : Completion α) (.normal ()) = .continue label := rfl

/-- Any throw from finally replaces the prior completion. -/
theorem Completion.finally_throw_overrides (prior : Completion α) (value : Value) :
    Completion.finallyOverride prior (.thrown value) = .thrown value := rfl

/-- Any return from finally replaces the prior completion. -/
theorem Completion.finally_return_overrides (prior : Completion α) (value : Value) :
    Completion.finallyOverride prior (.returned value) = .returned value := rfl

/-- Fresh cell allocation returns the former arena size. -/
theorem Machine.allocateCell_fresh (machine : Machine P) (cell : Cell) :
    (machine.allocateCell cell).1.value = machine.cells.size := rfl

/-- Fresh cell allocation appends exactly one stable slot. -/
theorem Machine.allocateCell_size (machine : Machine P) (cell : Cell) :
    (machine.allocateCell cell).2.cells.size = machine.cells.size + 1 := by
  simp [Machine.allocateCell]

/-- Successful environment allocation returns the former arena size. -/
theorem Machine.allocateEnvironment_fresh (machine next : Machine P) (parent : Option EnvId)
    (id : EnvId) (allocated : machine.allocateEnvironment parent = .ok (id, next)) :
    id.value = machine.environments.size := by
  cases parent with
  | none =>
      simp [Machine.allocateEnvironment] at allocated
      exact congrArg EnvId.value allocated.1.symm
  | some parent =>
      cases found : machine.getEnvironment parent with
      | error fault => simp [Machine.allocateEnvironment, found] at allocated
      | ok record =>
          simp [Machine.allocateEnvironment, found] at allocated
          exact congrArg EnvId.value allocated.1.symm

/-- A binding in the current environment shadows every parent binding. -/
theorem Environment.resolveCell_nearest (machine : Machine P) (name : JSString)
    (environment : EnvId) (record : EnvironmentRecord) (cell : CellId) (fuel : Nat)
    (foundEnvironment : machine.getEnvironment environment = .ok record)
    (foundBinding : record.bindings[name]? = some cell) :
    Environment.resolveCell machine name (fuel + 1) environment = .ok cell := by
  simp [Environment.resolveCell, foundEnvironment, foundBinding]

/-- A successful mutable write commits exactly the target-cell replacement selected by `setCell`. -/
theorem Environment.writeCell_target (machine next : Machine P) (cell : CellId)
    (old value : Value)
    (found : machine.getCell cell = .ok ⟨.initialized old, true⟩)
    (updated : machine.setCell cell ⟨.initialized value, true⟩ = .ok next) :
    Environment.writeCell cell value machine = .done (.normal ()) next := by
  simp [Environment.writeCell, found, updated]

/-- Repeated initialization is a dedicated fault and preserves the complete machine. -/
theorem Environment.initialize_rejects_initialized (machine : Machine P) (cell : CellId)
    (old value : Value) (mutable : Bool)
    (found : machine.getCell cell = .ok ⟨.initialized old, mutable⟩) :
    Environment.initialize cell value machine =
      .fault (.runtime (.alreadyInitialized cell)) machine := by
  simp [Environment.initialize, found]

/-- Emission prepends one event to the internal reverse trace. -/
theorem Machine.emit_reverseTrace (machine : Machine P) (event : TraceEvent) :
    (machine.emit event).reverseTrace = event :: machine.reverseTrace := rfl

/-- Two emissions materialize in their original execution order. -/
theorem Machine.emit_order (machine : Machine P) (first second : TraceEvent) :
    (machine.emit first |>.emit second).trace = machine.trace ++ [first, second] := by
  simp [Machine.emit, Machine.trace]

/-- An indexed clock entry is returned exactly, with only the clock index advanced. -/
theorem ScriptedPlatform.now_indexed (state : ScriptedPlatformState)
    (result : Except PlatformFault Nat)
    (found : state.times[state.timeIndex]? = some result) :
    (ScriptedPlatform.make state).now state =
      (result, { state with timeIndex := state.timeIndex + 1 }) := by
  simp [ScriptedPlatform.make, ScriptedPlatform.stepNow, found]

/-- Missing clock script produces the clock exhaustion fault and still advances its index. -/
theorem ScriptedPlatform.now_exhausted (state : ScriptedPlatformState)
    (missing : state.times[state.timeIndex]? = none) :
    (ScriptedPlatform.make state).now state =
      (.error (.scriptExhausted (JSString.ofLeanString "now")),
        { state with timeIndex := state.timeIndex + 1 }) := by
  simp [ScriptedPlatform.make, ScriptedPlatform.stepNow, missing]

/-- An indexed random entry is returned exactly, with only the random index advanced. -/
theorem ScriptedPlatform.random_indexed (state : ScriptedPlatformState)
    (result : Except PlatformFault JSNumber)
    (found : state.randoms[state.randomIndex]? = some result) :
    (ScriptedPlatform.make state).random state =
      (result, { state with randomIndex := state.randomIndex + 1 }) := by
  simp [ScriptedPlatform.make, ScriptedPlatform.stepRandom, found]

/-- Missing random script produces the random exhaustion fault and still advances its index. -/
theorem ScriptedPlatform.random_exhausted (state : ScriptedPlatformState)
    (missing : state.randoms[state.randomIndex]? = none) :
    (ScriptedPlatform.make state).random state =
      (.error (.scriptExhausted (JSString.ofLeanString "random")),
        { state with randomIndex := state.randomIndex + 1 }) := by
  simp [ScriptedPlatform.make, ScriptedPlatform.stepRandom, missing]

/-- An indexed fetch entry is returned exactly, with only the fetch index advanced. -/
theorem ScriptedPlatform.fetch_indexed (state : ScriptedPlatformState) (request : FetchRequest)
    (result : Except PlatformFault FetchResult)
    (found : state.fetches[state.fetchIndex]? = some result) :
    (ScriptedPlatform.make state).fetch state request =
      (result, { state with fetchIndex := state.fetchIndex + 1 }) := by
  simp [ScriptedPlatform.make, ScriptedPlatform.stepFetch, found]

/-- Missing fetch script produces the fetch exhaustion fault and still advances its index. -/
theorem ScriptedPlatform.fetch_exhausted (state : ScriptedPlatformState) (request : FetchRequest)
    (missing : state.fetches[state.fetchIndex]? = none) :
    (ScriptedPlatform.make state).fetch state request =
      (.error (.scriptExhausted (JSString.ofLeanString "fetch")),
        { state with fetchIndex := state.fetchIndex + 1 }) := by
  simp [ScriptedPlatform.make, ScriptedPlatform.stepFetch, missing]

/-- Successful fuel consumption decreases fuel by exactly one. -/
theorem Machine.consumeFuel_decreases (machine next : Machine P)
    (consumed : machine.consumeFuel = some next) : next.fuel + 1 = machine.fuel := by
  cases fuel : machine.fuel with
  | zero => simp [Machine.consumeFuel, fuel] at consumed
  | succ remaining =>
      simp [Machine.consumeFuel, fuel] at consumed
      subst next
      simp

/-- Zero fuel produces meta-level exhaustion and leaves the machine unchanged. -/
theorem JSM.consumeFuel_zero (machine : Machine P) (empty : machine.fuel = 0) :
    JSM.consumeFuel machine = .exhausted machine := by
  simp [JSM.consumeFuel, Machine.consumeFuel, empty]

private def environmentPreservationWorkflow (root : EnvId) : JSM P Value := do
  let child ← Environment.allocateChild root
  let cell ← Environment.declare child (JSString.ofLeanString "value") true
  Environment.initialize cell (.primitive .undefined)
  Environment.write child (JSString.ofLeanString "value") (.primitive .null)
  Environment.withEnvironment child (Environment.read child (JSString.ofLeanString "value"))

/-- Allocation, declaration, initialization, write, resolution, read, and dynamic restoration
compose into one machine-preserving workflow with a valid returned value. -/
theorem Environment.composed_preservesResults (root : EnvId) :
    JSM.PreservesResults (fun value machine => machine.heap.valueValid value = true)
      (environmentPreservationWorkflow (P := P) root) := by
  have afterCell (child : EnvId) (cell : CellId) :
      JSM.PreservesResults (fun value (machine : Machine P) => machine.heap.valueValid value = true)
        (do
          Environment.initialize (P := P) cell (.primitive .undefined)
          Environment.write (P := P) child (JSString.ofLeanString "value") (.primitive .null)
          Environment.withEnvironment child
            (Environment.read (P := P) child (JSString.ofLeanString "value"))) := by
    have afterWrite : JSM.PreservesResults
        (fun value (machine : Machine P) => machine.heap.valueValid value = true) (do
          Environment.write (P := P) child (JSString.ofLeanString "value") (.primitive .null)
          Environment.withEnvironment child
            (Environment.read (P := P) child (JSString.ofLeanString "value"))) := by
      apply JSM.bind_preservesResults
      · exact Environment.write_primitive_preservesResults child (JSString.ofLeanString "value")
          .null
      · intro _unit machine valid unitValid
        exact ⟨(Environment.withEnvironment_preservesResults child
            (Environment.read child (JSString.ofLeanString "value"))
            (Environment.read_preservesResults child (JSString.ofLeanString "value"))).1 machine valid,
          (Environment.withEnvironment_preservesResults child
            (Environment.read child (JSString.ofLeanString "value"))
            (Environment.read_preservesResults child (JSString.ofLeanString "value"))).2 machine valid⟩
    apply JSM.bind_preservesResults
    · exact Environment.initialize_primitive_preservesResults cell .undefined
    · intro _unit machine valid unitValid
      exact ⟨afterWrite.1 machine valid, afterWrite.2 machine valid⟩
  have afterChild (child : EnvId) :
      JSM.PreservesResults (fun value (machine : Machine P) => machine.heap.valueValid value = true)
        (do
          let cell ← Environment.declare (P := P) child (JSString.ofLeanString "value") true
          Environment.initialize (P := P) cell (.primitive .undefined)
          Environment.write (P := P) child (JSString.ofLeanString "value") (.primitive .null)
          Environment.withEnvironment child
            (Environment.read (P := P) child (JSString.ofLeanString "value"))) := by
    apply JSM.bind_preservesResults
    · exact Environment.declare_preservesResults child (JSString.ofLeanString "value") true
    · intro cell machine valid cellValid
      exact ⟨(afterCell child cell).1 machine valid, (afterCell child cell).2 machine valid⟩
  unfold environmentPreservationWorkflow
  apply JSM.bind_preservesResults
  · exact Environment.allocateChild_preservesResults root
  · intro child machine valid childValid
    exact ⟨(afterChild child).1 machine valid, (afterChild child).2 machine valid⟩

private def controlPreservationWorkflow (root : EnvId) : JSM P Unit :=
  let label := JSString.ofLeanString "fixture-loop"
  Control.tryFinally
    (Environment.withEnvironment root
      (Control.whileLoop (pure true) (JSM.breakJS (some label)) (some label)))
    (JSM.emit (.emitted (JSString.ofLeanString "finally-hook")))

/-- Dynamic environment restoration, matching labeled loop control, and a concrete finally hook
compose without weakening machine validity or execution continuity. -/
theorem Control.composed_environment_loop_finally_preserves (root : EnvId) :
    JSM.PreservesWellFormed (controlPreservationWorkflow (P := P) root) := by
  let label := JSString.ofLeanString "fixture-loop"
  have conditionPreserves : JSM.PreservesResults (fun _ _ => True)
      (JSM.pure (P := P) true) :=
    JSM.pure_preservesResults (fun _ _ => True) true (by intros; trivial)
  have bodyPreserves : JSM.PreservesResults (fun _ _ => True)
      (JSM.breakJS (P := P) (α := Unit) (some label)) :=
    JSM.breakJS_preservesResults (fun _ _ => True) (some label)
  have loopPreserves := Control.whileLoop_preservesWellFormed
    (JSM.pure (P := P) true) (JSM.breakJS (P := P) (α := Unit) (some label))
    conditionPreserves bodyPreserves (some label)
  exact Control.tryFinally_preservesWellFormed
    (Environment.withEnvironment root
      (Control.whileLoop (JSM.pure true) (JSM.breakJS (some label)) (some label)))
    (JSM.emit (.emitted (JSString.ofLeanString "finally-hook")))
    (Environment.withEnvironment_preservesWellFormed root _ loopPreserves)
    (JSM.emit_preservesWellFormed _)

end TSLean.JS
