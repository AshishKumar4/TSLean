import TSLean.JS.Control

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

private def allocateGlobals : Nat → JSM platform Unit
  | 0 => pure ()
  | count + 1 => do
      let _ ← Environment.allocateGlobal
      allocateGlobals count

private theorem allocateGlobals_preservesResults (count : Nat) :
    JSM.PreservesResults (fun _ _ => True) (allocateGlobals count) := by
  induction count with
  | zero => exact JSM.pure_preservesResults (fun _ _ => True) () (by intros; trivial)
  | succ count ih =>
      unfold allocateGlobals
      apply JSM.bind_preservesResults
      · exact Environment.allocateGlobal_preservesResults
      · intro environment machine valid environmentValid
        exact ⟨ih.1 machine valid, ih.2 machine valid⟩

/-- The preservation proof instantiates without weakening at the 100,000-allocation scale. -/
theorem allocation_preservation_scale :
    JSM.PreservesResults (fun _ _ => True) (allocateGlobals 100000) :=
  allocateGlobals_preservesResults 100000

/-- The recursive loop preservation proof instantiates at a 10,000-step fuel bound. -/
theorem loop_preservation_scale :
    JSM.PreservesResults (fun _ _ => True)
      (Control.whileLoop (JSM.pure true) (JSM.pure ()) : JSM platform Unit) :=
  Control.whileLoop_preservesResults (JSM.pure true) (JSM.pure ())
    (JSM.pure_preservesResults (fun _ _ => True) true (by intros; trivial))
    (JSM.pure_preservesResults (fun _ _ => True) () (by intros; trivial))

/-- The 10,000-step loop also satisfies the terminal fuel monotonicity bound. -/
theorem loop_fuel_scale : ∀ machine,
    ((Control.whileLoop (JSM.pure true) (JSM.pure ()) : JSM platform Unit) machine).AllMachines
      (fun final => final.fuel ≤ machine.fuel) :=
  Control.whileLoop_fuel_mono (JSM.pure true) (JSM.pure ())
    (by intro machine; exact Nat.le_refl _)
    (by intro machine; exact Nat.le_refl _)

/-- Proof witness pairing the valid 10,000-fuel start with the all-machine preservation and fuel
bounds used by the executable run below. Keeping the action theorems quantified avoids reducing
10,000 iterations while elaborating a result-indexed proposition. -/
theorem tenThousand_loop_proof_witness :
    (Machine.initial platform 10000).WellFormed ∧
    JSM.PreservesResults (fun _ _ => True)
      (Control.whileLoop (JSM.pure true) (JSM.pure ()) : JSM platform Unit) ∧
    ∀ machine,
      ((Control.whileLoop (JSM.pure true) (JSM.pure ()) : JSM platform Unit) machine).AllMachines
        (fun final => final.fuel ≤ machine.fuel) :=
  ⟨Machine.initial_wellFormed platform 10000, loop_preservation_scale, loop_fuel_scale⟩

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
  match (Control.whileLoop (pure true) (pure ())) (Machine.initial platform 10000) with
  | .exhausted machine => assert! machine.fuel = 0
  | _ => assert! false

#eval run

end TSLean.JS.ExecutionScaleTests
