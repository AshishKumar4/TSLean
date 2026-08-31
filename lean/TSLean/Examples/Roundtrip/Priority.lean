namespace TSLean.Examples.Roundtrip.Priority

/-- How urgent a task is. -/
inductive Priority where
  | low
  | normal
  | high
  | urgent
  deriving DecidableEq, Repr

/-- Whether the left task runs strictly before the right one. -/
def before (left right : Priority) : Bool :=
  match left with
  | .low => false
  | .normal =>
    match right with
    | .low => true
    | .normal => false
    | .high => false
    | .urgent => false
  | .high =>
    match right with
    | .low => true
    | .normal => true
    | .high => false
    | .urgent => false
  | .urgent =>
    match right with
    | .low => true
    | .normal => true
    | .high => true
    | .urgent => false

/-- No task runs before itself. -/
theorem before_irrefl (priority : Priority) : before priority priority = false := by
  cases priority <;> rfl

end TSLean.Examples.Roundtrip.Priority
