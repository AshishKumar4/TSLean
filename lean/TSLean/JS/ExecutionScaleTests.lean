import TSLean.JS.Environment

namespace TSLean.JS.ExecutionScaleTests

private def platform : Platform := ScriptedPlatform.make {
  times := #[], randoms := #[], fetches := #[]
}

private def allocateCells (count : Nat) (machine : Machine platform) : Machine platform :=
  (List.range count).foldl (fun current _ =>
    (current.allocateCell ⟨.uninitialized, true⟩).2) machine

private def allocateEnvironments (count : Nat) (machine : Machine platform) : Machine platform :=
  (List.range count).foldl (fun current _ =>
    match current.allocateEnvironment (some current.currentEnv) with
    | .ok (_, next) => next
    | .error _ => current) machine

private def emitEvents (count : Nat) (machine : Machine platform) : Machine platform :=
  (List.range count).foldl (fun current index => current.emit (.now index)) machine

/-- Exercises 100k append-only cell/environment allocations and constant-time reverse emissions.
Arena append and trace emission are amortized O(1); ordered trace materialization is O(n). -/
private def run : IO Unit := do
  let count := 100000
  let cells := allocateCells count (Machine.initial platform 0)
  assert! cells.cells.size = count
  let environments := allocateEnvironments count (Machine.initial platform 0)
  assert! environments.environments.size = count + 1
  let traced := emitEvents count (Machine.initial platform 0)
  assert! traced.reverseTrace.length = count
  assert! traced.trace.length = count

#eval run

end TSLean.JS.ExecutionScaleTests
