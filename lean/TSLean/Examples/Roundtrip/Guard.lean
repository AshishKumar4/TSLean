namespace TSLean.Examples.Roundtrip.Guard

/-- Why a request was refused, or that it was not. -/
inductive Verdict where
  | admit
  | refuseUnauthenticated
  | refuseUnauthorised
  deriving DecidableEq, Repr

/-- What the guard decides. Authentication is checked before authorisation. -/
def verdictOf (authenticated authorised : Bool) : Verdict :=
  if !authenticated then .refuseUnauthenticated
  else if !authorised then .refuseUnauthorised
  else .admit

/-- Whether the verdict lets the request through. -/
def admitted (verdict : Verdict) : Bool :=
  match verdict with
  | .admit => true
  | .refuseUnauthenticated => false
  | .refuseUnauthorised => false

/-- An unauthenticated request is never admitted. -/
theorem verdict_unauthenticated (authorised : Bool) :
    admitted (verdictOf false authorised) = false := by
  simp [verdictOf, admitted]

end TSLean.Examples.Roundtrip.Guard
