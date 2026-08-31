namespace TSLean.Examples.Roundtrip.Access

/-- What a subject may do. -/
inductive Action where
  | read
  | write
  | erase
  deriving DecidableEq, Repr

/-- The permissions one subject holds. -/
structure Permissions where
  reader : Bool
  writer : Bool
  owner : Bool
  deriving DecidableEq, Repr

/-- Whether the permissions admit the action. -/
def Permissions.admits (permissions : Permissions) (action : Action) : Bool :=
  match action with
  | .read => permissions.reader || permissions.writer || permissions.owner
  | .write => permissions.writer || permissions.owner
  | .erase => permissions.owner

end TSLean.Examples.Roundtrip.Access
