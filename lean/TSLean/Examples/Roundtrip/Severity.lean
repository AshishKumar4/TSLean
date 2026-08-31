namespace TSLean.Examples.Roundtrip.Severity

/-- How serious a report is. -/
inductive Severity where
  | info
  | warning
  | error
  deriving DecidableEq, Repr

/-- Whether the left severity is at least the right one. -/
def atLeast (left right : Severity) : Bool :=
  match left with
  | .error => true
  | .warning =>
    match right with
    | .info => true
    | .warning => true
    | .error => false
  | .info =>
    match right with
    | .info => true
    | .warning => false
    | .error => false

/-- The more serious of two severities. -/
def worst (left right : Severity) : Severity :=
  if atLeast left right then left else right

/-- Every severity is at least itself. -/
theorem atLeast_refl (severity : Severity) : atLeast severity severity = true := by
  cases severity <;> rfl

end TSLean.Examples.Roundtrip.Severity
