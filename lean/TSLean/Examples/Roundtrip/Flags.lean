namespace TSLean.Examples.Roundtrip.Flags

/-- Three independent switches. -/
structure Flags where
  alpha : Bool
  beta : Bool
  gamma : Bool
  deriving DecidableEq, Repr

/-- Every switch either side has on. -/
def Flags.union (left right : Flags) : Flags :=
  { alpha := left.alpha || right.alpha
    beta := left.beta || right.beta
    gamma := left.gamma || right.gamma }

/-- Only the switches both sides have on. -/
def Flags.meet (left right : Flags) : Flags :=
  { alpha := left.alpha && right.alpha
    beta := left.beta && right.beta
    gamma := left.gamma && right.gamma }

/-- The meet is below the union. -/
theorem meet_le_union (left right : Flags) :
    (Flags.meet left right).alpha = true → (Flags.union left right).alpha = true := by
  simp [Flags.meet, Flags.union]
  intro h
  simp [h]

end TSLean.Examples.Roundtrip.Flags
