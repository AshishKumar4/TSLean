namespace TSLean.Examples.Roundtrip.Vote

/-- How one voter voted. -/
inductive Ballot where
  | against
  | abstain
  | infavour
  deriving DecidableEq, Repr

/-- What a three-voter panel decided. -/
inductive Outcome where
  | rejected
  | tied
  | carried
  deriving DecidableEq, Repr

/-- The outcome of two ballots against each other. -/
def pair (first second : Ballot) : Outcome :=
  match first with
  | .against =>
    match second with
    | .infavour => .tied
    | .abstain => .rejected
    | .against => .rejected
  | .abstain =>
    match second with
    | .infavour => .carried
    | .abstain => .tied
    | .against => .rejected
  | .infavour =>
    match second with
    | .infavour => .carried
    | .abstain => .carried
    | .against => .tied

/-- Whether the panel carried the motion. -/
def carried (outcome : Outcome) : Bool :=
  match outcome with
  | .carried => true
  | .tied => false
  | .rejected => false

/-- Swapping the two ballots does not change the outcome. -/
theorem pair_comm (first second : Ballot) : pair first second = pair second first := by
  cases first <;> cases second <;> rfl

end TSLean.Examples.Roundtrip.Vote
