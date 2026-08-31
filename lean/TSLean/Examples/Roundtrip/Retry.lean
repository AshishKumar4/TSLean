namespace TSLean.Examples.Roundtrip.Retry

/-- What to do after a failed attempt. -/
inductive Recovery where
  | giveUp
  | retryNow
  | retryLater
  deriving DecidableEq, Repr

/-- What the caller observed about the failure. -/
structure Failure where
  transient : Bool
  budgetLeft : Bool
  throttled : Bool
  deriving DecidableEq, Repr

/-- What to do next. A permanent failure and an exhausted budget both stop the attempt. -/
def recover (failure : Failure) : Recovery :=
  if !failure.transient then .giveUp
  else if !failure.budgetLeft then .giveUp
  else if failure.throttled then .retryLater
  else .retryNow

/-- A permanent failure always gives up. -/
theorem recover_permanent (budgetLeft throttled : Bool) :
    recover { transient := false, budgetLeft := budgetLeft, throttled := throttled } = .giveUp := by
  simp [recover]

end TSLean.Examples.Roundtrip.Retry
