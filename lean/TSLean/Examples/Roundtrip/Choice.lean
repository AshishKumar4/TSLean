namespace TSLean.Examples.Roundtrip.Choice

/-- One of three candidates. -/
inductive Candidate where
  | first
  | second
  | third
  deriving DecidableEq, Repr

/-- Which candidates are still available. -/
structure Availability where
  first : Bool
  second : Bool
  third : Bool
  deriving DecidableEq, Repr

/-- The first available candidate, if there is one. -/
def choose (availability : Availability) : Option Candidate :=
  if availability.first then some .first
  else if availability.second then some .second
  else if availability.third then some .third
  else none

end TSLean.Examples.Roundtrip.Choice
