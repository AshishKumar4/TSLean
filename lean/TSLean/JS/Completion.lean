import TSLean.JS.String
import TSLean.JS.Value

namespace TSLean.JS

/-- A JavaScript non-normal control transfer. Labels are exact ECMAScript strings. -/
inductive Abrupt where
  | returned (value : Value)
  | thrown (value : Value)
  | break (label : Option JSString)
  | continue (label : Option JSString)
  deriving DecidableEq

/-- A normal result or one of JavaScript's abrupt completion forms. -/
inductive Completion (α : Type) where
  | normal (value : α)
  | returned (value : Value)
  | thrown (value : Value)
  | break (label : Option JSString)
  | continue (label : Option JSString)
  deriving DecidableEq

namespace Completion

/-- Changes a normal result and preserves every abrupt completion exactly. -/
def map (f : α → β) : Completion α → Completion β
  | .normal value => .normal (f value)
  | .returned value => .returned value
  | .thrown value => .thrown value
  | .break label => .break label
  | .continue label => .continue label

/-- Sequences only normal completion; abrupt completion bypasses the continuation. -/
def bind (result : Completion α) (next : α → Completion β) : Completion β :=
  match result with
  | .normal value => next value
  | .returned value => .returned value
  | .thrown value => .thrown value
  | .break label => .break label
  | .continue label => .continue label

/-- Changes the result type of an abrupt completion. A normal result maps through `f`. -/
def cast (f : α → β) : Completion α → Completion β := map f

/-- Extracts the abrupt payload, if present. -/
def abrupt? : Completion α → Option Abrupt
  | .normal _ => none
  | .returned value => some (.returned value)
  | .thrown value => some (.thrown value)
  | .break label => some (.break label)
  | .continue label => some (.continue label)

/-- Reports whether a completion is non-normal. -/
def isAbrupt (result : Completion α) : Bool := result.abrupt?.isSome

/-- ECMAScript finally selection: normal finalization preserves the prior completion;
abrupt finalization replaces it. -/
def finallyOverride (prior : Completion α) (finalizer : Completion Unit) : Completion α :=
  match finalizer with
  | .normal () => prior
  | .returned value => .returned value
  | .thrown value => .thrown value
  | .break label => .break label
  | .continue label => .continue label

end Completion
end TSLean.JS
