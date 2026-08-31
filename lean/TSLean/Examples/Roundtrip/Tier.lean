namespace TSLean.Examples.Roundtrip.Tier

/-- Which tier serves a call. -/
inductive Tier where
  | direct
  | mediated
  deriving DecidableEq, Repr

/-- What the call does. -/
inductive Impact where
  | observe
  | mutate
  | administer
  deriving DecidableEq, Repr

/-- The weakest tier the impact admits under the given session condition. -/
def floorOf (impact : Impact) (ownedSession : Bool) : Tier :=
  match impact with
  | .observe => .direct
  | .mutate => if ownedSession then .direct else .mediated
  | .administer => .mediated

/-- Whether the tier serves the call without evidence. -/
def isDirect (tier : Tier) : Bool :=
  match tier with
  | .direct => true
  | .mediated => false

/-- Whether a claimed impact never lowers the derived impact's floor. -/
def honours (claimed derived : Impact) (ownedSession : Bool) : Bool :=
  let claimedTier := floorOf claimed ownedSession
  let derivedTier := floorOf derived ownedSession
  match claimedTier with
  | .mediated => true
  | .direct => isDirect derivedTier

/-- Administering is always mediated. -/
theorem floor_administer (ownedSession : Bool) : floorOf .administer ownedSession = .mediated := by
  rfl

end TSLean.Examples.Roundtrip.Tier
