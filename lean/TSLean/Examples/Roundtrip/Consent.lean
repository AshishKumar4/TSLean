namespace TSLean.Examples.Roundtrip.Consent

/-- What a subject agreed to. -/
inductive Purpose where
  | essential
  | analytics
  | marketing
  deriving DecidableEq, Repr

/-- The record of one subject's answers. -/
structure Consent where
  analytics : Bool
  marketing : Bool
  withdrawn : Bool
  deriving DecidableEq, Repr

/-- The strongest purpose the record still permits, if any. -/
def granted (consent : Consent) : Option Purpose :=
  if consent.withdrawn then none
  else if consent.marketing then some .marketing
  else if consent.analytics then some .analytics
  else some .essential

/-- A withdrawn record permits nothing. -/
theorem granted_withdrawn (analytics marketing : Bool) :
    granted { analytics := analytics, marketing := marketing, withdrawn := true } = none := by
  simp [granted]

end TSLean.Examples.Roundtrip.Consent
