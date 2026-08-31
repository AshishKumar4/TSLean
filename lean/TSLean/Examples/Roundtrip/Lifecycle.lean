namespace TSLean.Examples.Roundtrip.Lifecycle

/-- Where a job is in its life. -/
inductive Phase where
  | queued
  | running
  | done
  | failed
  deriving DecidableEq, Repr

/-- The phase one event moves the job to. A terminal phase stays put. -/
def advance (phase : Phase) (succeeded : Bool) : Phase :=
  match phase with
  | .queued => .running
  | .running => if succeeded then .done else .failed
  | .done => .done
  | .failed => .failed

/-- Whether the job has stopped. -/
def terminal (phase : Phase) : Bool :=
  match phase with
  | .queued => false
  | .running => false
  | .done => true
  | .failed => true

/-- A terminal phase never advances. -/
theorem advance_terminal (phase : Phase) (succeeded : Bool) :
    terminal phase = true → advance phase succeeded = phase := by
  cases phase <;> simp [terminal, advance]

end TSLean.Examples.Roundtrip.Lifecycle
