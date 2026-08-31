namespace TSLean.Examples.Roundtrip.Tribool

/-- A truth value that may be unknown. -/
inductive Tribool where
  | no
  | unknown
  | yes
  deriving DecidableEq, Repr

/-- Kleene negation. -/
def notT (value : Tribool) : Tribool :=
  match value with
  | .no => .yes
  | .unknown => .unknown
  | .yes => .no

/-- Kleene conjunction: the weaker of the two. -/
def andT (left right : Tribool) : Tribool :=
  match left with
  | .no => .no
  | .unknown =>
    match right with
    | .no => .no
    | .unknown => .unknown
    | .yes => .unknown
  | .yes => right

/-- Negation is its own inverse. -/
theorem notT_notT (value : Tribool) : notT (notT value) = value := by
  cases value <;> rfl

end TSLean.Examples.Roundtrip.Tribool
