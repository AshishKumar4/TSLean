import TSLean.Examples.Package.Capability

namespace TSLean.Examples.Package

/-- A grant, the strongest capability the policy advertises, and whether it is frozen. -/
structure Policy where
  granted : Grant
  ceiling : Capability
  frozen : Bool
  deriving DecidableEq, Repr

/-- What the policy hands out now. A frozen policy keeps only its read capability. -/
def Policy.effective (policy : Policy) : Grant :=
  if policy.frozen then { read := policy.granted.read, write := false, administer := false }
  else policy.granted

/-- Whether the policy still holds the capability it advertises as its ceiling. -/
def Policy.consistent (policy : Policy) : Bool :=
  policy.granted.allows policy.ceiling

end TSLean.Examples.Package
