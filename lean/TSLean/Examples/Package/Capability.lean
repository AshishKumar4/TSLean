namespace TSLean.Examples.Package

/-- What a caller may do with a resource. -/
inductive Capability where
  | read
  | write
  | administer
  deriving DecidableEq, Repr

/-- The capabilities one grant carries. -/
structure Grant where
  read : Bool
  write : Bool
  administer : Bool
  deriving DecidableEq, Repr

/-- Whether this grant carries the capability. -/
def Grant.allows (grant : Grant) (capability : Capability) : Bool :=
  match capability with
  | .read => grant.read
  | .write => grant.write
  | .administer => grant.administer

end TSLean.Examples.Package
