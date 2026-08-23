import TSLean.Examples.Package.Policy

namespace TSLean.Examples.Package

/-- The outcome of one access check. -/
inductive Decision where
  | allow
  | deny
  deriving DecidableEq, Repr

/-- The decision one policy reaches for one requested capability. -/
def decideAccess (policy : Policy) (capability : Capability) : Decision :=
  if policy.consistent && policy.effective.allows capability then .allow else .deny

/-- The requested capability, when the policy actually hands it out. -/
def grantedCapability (policy : Policy) (capability : Capability) : Option Capability :=
  if policy.effective.allows capability then some capability else none

end TSLean.Examples.Package
