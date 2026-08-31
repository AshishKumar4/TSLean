namespace TSLean.Examples.Roundtrip.Sign

/-- The sign of a quantity. -/
inductive Sign where
  | negative
  | zero
  | positive
  deriving DecidableEq, Repr

/-- The sign of the negated quantity. -/
def negate (sign : Sign) : Sign :=
  match sign with
  | .negative => .positive
  | .zero => .zero
  | .positive => .negative

/-- Negation is its own inverse. -/
theorem negate_negate (sign : Sign) : negate (negate sign) = sign := by
  cases sign <;> rfl

end TSLean.Examples.Roundtrip.Sign
