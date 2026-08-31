namespace TSLean.Examples.Roundtrip.Suit

/-- A playing-card suit. -/
inductive Suit where
  | clubs
  | diamonds
  | hearts
  | spades
  deriving DecidableEq, Repr

/-- The colour a suit is printed in. -/
inductive Colour where
  | black
  | red
  deriving DecidableEq, Repr

/-- The colour of the suit. -/
def colourOf (suit : Suit) : Colour :=
  match suit with
  | .clubs => .black
  | .spades => .black
  | .diamonds => .red
  | .hearts => .red

/-- Whether two suits share a colour. -/
def sameColour (left right : Suit) : Bool :=
  let leftColour := colourOf left
  let rightColour := colourOf right
  match leftColour with
  | .black =>
    match rightColour with
    | .black => true
    | .red => false
  | .red =>
    match rightColour with
    | .black => false
    | .red => true

/-- Every suit shares its colour with itself. -/
theorem sameColour_refl (suit : Suit) : sameColour suit suit = true := by
  cases suit <;> rfl

end TSLean.Examples.Roundtrip.Suit
