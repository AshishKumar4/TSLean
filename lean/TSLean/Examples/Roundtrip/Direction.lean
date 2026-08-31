namespace TSLean.Examples.Roundtrip.Direction

/-- One of the four compass directions. -/
inductive Direction where
  | north
  | east
  | south
  | west
  deriving DecidableEq, Repr

/-- The direction facing the other way. -/
def opposite (direction : Direction) : Direction :=
  match direction with
  | .north => .south
  | .east => .west
  | .south => .north
  | .west => .east

/-- Turning right once. -/
def clockwise (direction : Direction) : Direction :=
  match direction with
  | .north => .east
  | .east => .south
  | .south => .west
  | .west => .north

/-- Facing the other way twice faces the first way again. -/
theorem opposite_opposite (direction : Direction) : opposite (opposite direction) = direction := by
  cases direction <;> rfl

end TSLean.Examples.Roundtrip.Direction
