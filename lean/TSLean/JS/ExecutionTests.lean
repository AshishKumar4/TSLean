import TSLean.JS.Control
import TSLean.JS.External

namespace TSLean.JS.ExecutionTests

private def text (value : String) : JSString := JSString.ofLeanString value
private def value (number : Int) : Value := .primitive (.bigint number)

private def platform : Platform := ScriptedPlatform.make {
  times := #[.ok 10, .ok 20]
  randoms := #[.ok ⟨0x3ff0000000000000⟩]
  fetches := #[
    .ok (.resolved ⟨200, text "ok"⟩),
    .ok (.rejected (value 9))]
}

private def emptyPlatform : Platform := ScriptedPlatform.make {
  times := #[], randoms := #[], fetches := #[]
}

private def fresh (fuel : Nat := 100) : Machine platform := Machine.initial platform fuel

private def testFinallyMatrix : IO Unit := do
  let label := text "outer"
  let completions : List (Completion Unit) := [
    .normal (), .returned (value 1), .thrown (value 2), .break (some label),
    .continue (some label)]
  for prior in completions do
    for finalizer in completions do
      let expected := match finalizer with | .normal () => prior | abrupt => abrupt
      assert! Completion.finallyOverride prior finalizer = expected

  let returned : JSM platform Nat := JSM.returnJS (value 1)
  let overriding : JSM platform Unit := JSM.returnJS (value 2)
  match Control.tryFinally returned overriding (fresh) with
  | .done (.returned actual) _ => assert! actual = value 2
  | _ => assert! false

  let preserve (action : JSM platform Unit) := Control.tryFinally action (pure ()) (fresh)
  match preserve (JSM.returnJS (value 3)) with
  | .done (.returned actual) _ => assert! actual = value 3
  | _ => assert! false
  match preserve (JSM.breakJS (some label)) with
  | .done (.break (some actual)) _ => assert! actual = label
  | _ => assert! false
  match preserve (JSM.continueJS (some label)) with
  | .done (.continue (some actual)) _ => assert! actual = label
  | _ => assert! false

  let tracedTry : JSM platform Unit := do
    JSM.emit (.emitted (text "try"))
    JSM.throwJS (value 4)
  let handled (_ : Value) : JSM platform Unit := do
    JSM.emit (.emitted (text "catch"))
  let finalizer : JSM platform Unit := do
    JSM.emit (.emitted (text "finally"))
  match Control.tryCatchFinally tracedTry handled finalizer (fresh) with
  | .done (.normal ()) machine =>
      assert! machine.trace = [
        .emitted (text "try"), .emitted (text "catch"), .emitted (text "finally")]
  | _ => assert! false

  match Control.tryFinally (JSM.returnJS (value 1) : JSM platform Unit)
      (JSM.throwJS (value 8)) (fresh) with
  | .done (.thrown actual) _ => assert! actual = value 8
  | _ => assert! false

private def testControlHandlers : IO Unit := do
  let outer := text "outer"
  let other := text "other"
  match Control.handleSwitchBreak (JSM.breakJS : JSM platform Unit) (fresh) with
  | .done (.normal ()) _ => pure ()
  | _ => assert! false
  match Control.handleSwitchBreak (JSM.breakJS (some outer) : JSM platform Unit) (fresh) with
  | .done (.break (some actual)) _ => assert! actual = outer
  | _ => assert! false
  match Control.handleLabeledBreak outer (JSM.breakJS (some outer)) (fresh) with
  | .done (.normal ()) _ => pure ()
  | _ => assert! false
  match Control.handleLabeledBreak outer (JSM.breakJS (some other)) (fresh) with
  | .done (.break (some actual)) _ => assert! actual = other
  | _ => assert! false

  for completion in [
      Control.handleLoopControl (some outer) (JSM.breakJS : JSM platform Unit),
      Control.handleLoopControl (some outer) (JSM.breakJS (some outer)),
      Control.handleLoopControl (some outer) (JSM.continueJS : JSM platform Unit),
      Control.handleLoopControl (some outer) (JSM.continueJS (some outer))] do
    match completion (fresh) with
    | .done (.normal _) _ => pure ()
    | _ => assert! false
  match Control.handleLoopControl (some outer) (JSM.continueJS (some other)) (fresh) with
  | .done (.continue (some actual)) _ => assert! actual = other
  | _ => assert! false

private def mutateBeforeAbrupt (returns : Bool) : JSM platform Unit := do
    let machine ← JSM.get
    match machine.heap.allocate with
    | .error fault => JSM.fail (.runtime (.heap fault))
    | .ok (_, heap) => JSM.set (machine.setHeap heap)
    let withHeap ← JSM.get
    let cell ← Environment.declare withHeap.currentEnv (text "x") true
    Environment.initialize cell (value 1)
    Environment.writeCell cell (value 2)
    JSM.emit (.emitted (text "before abrupt"))
    if returns then JSM.returnJS (value 6) else JSM.throwJS (value 7)

private def checkCommittedMutation (machine : Machine platform) : IO Unit := do
  assert! machine.heap.size = 1
  assert! machine.trace = [.emitted (text "before abrupt")]
  match machine.getCell ⟨0⟩ with
  | .ok ⟨.initialized stored, true⟩ => assert! stored = value 2
  | _ => assert! false

private def testStateSurvivesAbrupt : IO Unit := do
  match mutateBeforeAbrupt false (fresh) with
  | .done (.thrown actual) machine =>
      assert! actual = value 7
      checkCommittedMutation machine
  | _ => assert! false
  match mutateBeforeAbrupt true (fresh) with
  | .done (.returned actual) machine =>
      assert! actual = value 6
      checkCommittedMutation machine
  | _ => assert! false

private def testEnvironments : IO Unit := do
  let setup : JSM platform (EnvId × EnvId × CellId) := do
    let machine ← JSM.get
    let outerCell ← Environment.declare machine.currentEnv (text "x") true
    Environment.initialize outerCell (value 1)
    let child ← Environment.allocateChild machine.currentEnv
    let innerCell ← Environment.declare child (text "x") true
    Environment.initialize innerCell (value 2)
    pure (machine.currentEnv, child, outerCell)
  match setup (fresh) with
  | .done (.normal (global, child, outerCell)) machine =>
      match Environment.read child (text "x") machine with
      | .done (.normal actual) _ => assert! actual = value 2
      | _ => assert! false
      match Environment.write child (text "x") (value 3) machine with
      | .done (.normal ()) written =>
          match Environment.readCell outerCell written with
          | .done (.normal actual) _ => assert! actual = value 1
          | _ => assert! false
      | _ => assert! false

      let shared : JSM platform Unit := do
        let captured ← Environment.allocateChild global
        let cell ← Environment.declare captured (text "shared") true
        Environment.initialize cell (value 5)
        let closureRead := Environment.read captured (text "shared")
        let closureWrite := Environment.write captured (text "shared") (value 6)
        closureWrite
        let observed ← closureRead
        if observed = value 6 then pure () else JSM.throwJS (value 99)
      match shared machine with
      | .done (.normal ()) _ => pure ()
      | _ => assert! false

      let inside (action : JSM platform Unit) := Environment.withEnvironment child do
        let current ← JSM.get
        assert! current.currentEnv = child
        action
      match inside (pure ()) machine with
      | .done (.normal ()) restored => assert! restored.currentEnv = global
      | _ => assert! false
      match inside (JSM.returnJS (value 7)) machine with
      | .done (.returned actual) restored =>
          assert! actual = value 7
          assert! restored.currentEnv = global
      | _ => assert! false
      match inside (JSM.throwJS (value 8)) machine with
      | .done (.thrown actual) restored =>
          assert! actual = value 8
          assert! restored.currentEnv = global
      | _ => assert! false
      match inside JSM.breakJS machine with
      | .done (.break none) restored => assert! restored.currentEnv = global
      | _ => assert! false
      match inside (JSM.continueJS (some (text "loop"))) machine with
      | .done (.continue (some actual)) restored =>
          assert! actual = text "loop"
          assert! restored.currentEnv = global
      | _ => assert! false
      let exhausted : JSM platform Unit := fun current =>
        .exhausted (current.emit (.emitted (text "exhausted")))
      match inside exhausted machine with
      | .exhausted restored =>
          assert! restored.currentEnv = global
          assert! restored.trace = [.emitted (text "exhausted")]
      | _ => assert! false
      let faulted : JSM platform Unit := fun current =>
        .fault (.runtime (.invalidCell ⟨999⟩)) (current.emit (.emitted (text "fault")))
      match inside faulted machine with
      | .fault (.runtime (.invalidCell ⟨999⟩)) restored =>
          assert! restored.currentEnv = global
          assert! restored.trace = [.emitted (text "fault")]
      | _ => assert! false
  | _ => assert! false

  let tdz : JSM platform Value := do
    let machine ← JSM.get
    let cell ← Environment.declare machine.currentEnv (text "tdz") true
    Environment.readCell cell
  match tdz (fresh) with
  | .done (.thrown _) _ => pure ()
  | _ => assert! false

  let immutable : JSM platform Unit := do
    let machine ← JSM.get
    let cell ← Environment.declare machine.currentEnv (text "constant") false
    Environment.initialize cell (value 1)
    Environment.writeCell cell (value 2)
  match immutable (fresh) with
  | .done (.thrown _) _ => pure ()
  | _ => assert! false

private def testRepeatedInitialization : IO Unit := do
  for mutable in [true, false] do
    let setup : JSM platform CellId := do
      let machine ← JSM.get
      let cell ← Environment.declare machine.currentEnv (text "binding") mutable
      Environment.initialize cell (value 1)
      pure cell
    match setup (fresh) with
    | .done (.normal cell) initialized =>
        match Environment.initialize cell (value 2) initialized with
        | .fault (.runtime (.alreadyInitialized actual)) rejected =>
            assert! actual = cell
            assert! rejected.cells = initialized.cells
            assert! rejected.currentEnv = initialized.currentEnv
            assert! rejected.heap.size = initialized.heap.size
            assert! rejected.reverseTrace = initialized.reverseTrace
            assert! rejected.fuel = initialized.fuel
            match rejected.getCell cell with
            | .ok ⟨.initialized stored, actualMutable⟩ =>
                assert! stored = value 1
                assert! actualMutable = mutable
            | _ => assert! false
        | _ => assert! false
    | _ => assert! false

private def testPlatform : IO Unit := do
  let request : FetchRequest := ⟨text "https://example.test"⟩
  let action : JSM platform Unit := do
    let first ← External.now
    let random ← External.random
    let response ← External.fetch request
    if first = 10 && random.bits = 0x3ff0000000000000 && response.status = 200 then pure ()
    else JSM.throwJS (value 100)
  match action (fresh) with
  | .done (.normal ()) machine =>
      assert! machine.trace = [
        .now 10,
        .random ⟨0x3ff0000000000000⟩,
        .fetch request (.resolved ⟨200, text "ok"⟩)]
  | _ => assert! false

  let rejected : JSM platform FetchResponse := do
    let _ ← External.fetch request
    External.fetch request
  match rejected (fresh) with
  | .done (.thrown reason) machine =>
      assert! reason = value 9
      assert! machine.trace.length = 2
  | _ => assert! false

  let untaken : JSM platform Unit := do
    if false then
      let _ ← External.now
      pure ()
    else pure ()
  match untaken (fresh) with
  | .done (.normal ()) machine => assert! machine.trace = []
  | _ => assert! false

  match External.now (Machine.initial emptyPlatform 1) with
  | .fault (.platform (.scriptExhausted _)) machine =>
      assert! machine.trace.length = 1
      assert! machine.platform.timeIndex = 1
      assert! machine.platform.randomIndex = 0
      assert! machine.platform.fetchIndex = 0
      assert! machine.platform.randoms.isEmpty
      assert! machine.platform.fetches.isEmpty
  | _ => assert! false

private def testCatchExcludesModelFaults : IO Unit := do
  let handler (_ : Value) : JSM platform Unit := JSM.emit (.emitted (text "caught"))
  let runtimeFault : JSM platform Unit := JSM.fail (.runtime (.invalidCell ⟨17⟩))
  match Control.tryCatch runtimeFault handler (fresh) with
  | .fault (.runtime (.invalidCell ⟨17⟩)) machine => assert! machine.trace = []
  | _ => assert! false

  let platformHandler (_ : Value) : JSM emptyPlatform Nat := do
    JSM.emit (.emitted (text "caught"))
    pure 0
  match Control.tryCatch External.now platformHandler (Machine.initial emptyPlatform 1) with
  | .fault (.platform (.scriptExhausted _)) machine =>
      assert! machine.platform.timeIndex = 1
      match machine.trace with
      | [.platformFault _ _] => pure ()
      | _ => assert! false
  | _ => assert! false

private def recursiveSteps (steps : Nat) : JSM platform Unit :=
  match steps with
  | 0 => pure ()
  | remaining + 1 => do
      JSM.consumeFuel
      recursiveSteps remaining

private def testFuel : IO Unit := do
  match (Control.whileLoop (pure false) (JSM.emit (.emitted (text "body")))) (fresh 0) with
  | .exhausted machine =>
      assert! machine.fuel = 0
      assert! machine.trace = []
  | _ => assert! false
  match (Control.whileLoop (pure false) (JSM.emit (.emitted (text "body")))) (fresh 1) with
  | .done (.normal ()) machine =>
      assert! machine.fuel = 0
      assert! machine.trace = []
  | _ => assert! false
  match (Control.whileLoop (pure true) (JSM.breakJS : JSM platform Unit)) (fresh 1) with
  | .done (.normal ()) machine => assert! machine.fuel = 0
  | _ => assert! false
  match (Control.whileLoop (pure true) (JSM.emit (.emitted (text "body")))) (fresh 1) with
  | .exhausted machine =>
      assert! machine.fuel = 0
      assert! machine.trace = [.emitted (text "body")]
  | _ => assert! false
  match (Control.whileLoop (pure true) (pure ())) (fresh 3) with
  | .exhausted machine => assert! machine.fuel = 0
  | _ => assert! false
  match recursiveSteps 10 (fresh 4) with
  | .exhausted machine => assert! machine.fuel = 0
  | _ => assert! false

private def run : IO Unit := do
  testFinallyMatrix
  testControlHandlers
  testStateSurvivesAbrupt
  testEnvironments
  testRepeatedInitialization
  testPlatform
  testCatchExcludesModelFaults
  testFuel

#eval run

end TSLean.JS.ExecutionTests
