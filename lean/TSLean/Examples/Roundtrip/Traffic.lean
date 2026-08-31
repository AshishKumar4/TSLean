namespace TSLean.Examples.Roundtrip.Traffic

/-- What a traffic light shows. -/
inductive Light where
  | red
  | amber
  | green
  deriving DecidableEq, Repr

/-- The next light in the cycle. -/
def next (light : Light) : Light :=
  match light with
  | .red => .green
  | .green => .amber
  | .amber => .red

/-- Whether traffic may cross. -/
def mayCross (light : Light) : Bool :=
  match light with
  | .red => false
  | .amber => false
  | .green => true

/-- Three steps return to the light they started from. -/
theorem next_cycle (light : Light) : next (next (next light)) = light := by
  cases light <;> rfl

end TSLean.Examples.Roundtrip.Traffic
