namespace TSLean.Examples.Roundtrip.Parity

/-- Whether a count is even or odd. -/
inductive Parity where
  | even
  | odd
  deriving DecidableEq, Repr

/-- The parity a further step reaches. -/
def step (parity : Parity) : Parity :=
  match parity with
  | .even => .odd
  | .odd => .even

/-- Two steps return to the parity they started from. -/
theorem step_step (parity : Parity) : step (step parity) = parity := by
  cases parity <;> rfl

end TSLean.Examples.Roundtrip.Parity
