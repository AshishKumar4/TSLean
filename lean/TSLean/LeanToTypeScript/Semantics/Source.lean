import TSLean.LeanToTypeScript.Semantics.Ir

/-!
# Source semantics of the admitted IR

A big-step, call-indexed semantics for `Ir.Expr`. It is total: every expression at every fuel
returns a value, a typed fault, or fuel exhaustion.

Fuel counts function entries, not evaluation steps. The lowering turns one declared call or one
anonymous application into one target entry, so the same fuel bounds both sides and the preservation
statement can quantify over one fuel rather than relate two step counts.

Evaluation order is fixed and observable. `and`, `or` and `if` are lazy in the operands the Lean
elaborator makes lazy; every other form evaluates its subexpressions left to right. The trace records
one event per entry, in order, so a lowering that reordered, dropped or duplicated a call fails the
refinement even where the returned value happens to agree.

An arrow is a value, not a host function. `Value.closure` carries its exact inline parameter list and
body plus the enclosing binders it captured. Applying one enters that stored body, records one
anonymous-application event carrying the same code identity, and spends one unit of fuel. Nothing
about an arrow is left to a Lean callback the model would have to trust.
-/

namespace TSLean.LeanToTypeScript.Semantics

namespace Source

/-- A value of the admitted fragment. -/
inductive Value where
  | boolean (value : Bool)
  /-- `Option.none`. -/
  | absent
  /-- `Option.some`. -/
  | present (value : Value)
  | record (type : String) (fields : List (String × Value))
  | variant (type name : String) (arguments : List Value)
  /-- An inline arrow's captured scope, exact parameter list and exact body. The captured scope is
  innermost-first, as every de Bruijn scope is. -/
  | closure (captured : List Value) (parameters : List Ir.Field) (body : Ir.Expr)
  deriving Repr

/-- One observable function entry. A declared function has its qualified name; an anonymous
application has the exact inline lambda code that entered. -/
inductive Event where
  | function (name : String) (arguments : List Value)
  | application (code : Ir.LambdaCode) (arguments : List Value)
  deriving Repr

/-- The ordered events one evaluation produced. -/
abbrev Trace := List Event

/-- A typed way evaluation cannot proceed. Every one of these is unreachable for a well-typed
program, and the preservation theorems prove that rather than assume it. -/
inductive Fault where
  | unboundVariable (index : Nat)
  | notABoolean
  | notARecord
  | fieldAbsent (field : String)
  | notAVariant
  | armAbsent (constructor : String)
  | undeclaredFunction (function : String)
  | arityMismatch (function : String) (expected actual : Nat)
  | notAClosure
  | closureArity (expected actual : Nat)
  deriving DecidableEq, Repr

/-- The result of evaluating one expression, carrying the trace in every case. -/
inductive Outcome where
  | value (value : Value) (trace : Trace)
  | fault (fault : Fault) (trace : Trace)
  | exhausted (trace : Trace)
  deriving Repr

/-- The result of evaluating a list of expressions left to right. -/
inductive ListOutcome where
  | values (values : List Value) (trace : Trace)
  | fault (fault : Fault) (trace : Trace)
  | exhausted (trace : Trace)
  deriving Repr

/-- The result of evaluating a named field list left to right. -/
inductive FieldsOutcome where
  | fields (fields : List (String × Value)) (trace : Trace)
  | fault (fault : Fault) (trace : Trace)
  | exhausted (trace : Trace)
  deriving Repr

/-- The value bound at a de Bruijn index, innermost binder first. -/
def lookup (scope : List Value) (index : Nat) : Option Value := scope[index]?

/-- The value stored at a declared field of a record value. -/
def fieldValue? (fields : List (String × Value)) (name : String) : Option Value :=
  (fields.find? fun entry => entry.1 == name).map Prod.snd

mutual

/--
Evaluates one expression. `scope` holds the enclosing bindings, innermost first; `trace` holds the
events already produced, in order; the result extends that trace.
-/
def eval (program : Ir.Program) (fuel : Nat) (scope : List Value) (trace : Trace) :
    Ir.Expr → Outcome
  | .varRef index =>
      match lookup scope index with
      | some value => .value value trace
      | none => .fault (.unboundVariable index) trace
  | .boolLit value => .value (.boolean value) trace
  | .letBind _ value body =>
      match eval program fuel scope trace value with
      | .value bound next => eval program fuel (bound :: scope) next body
      | .fault fault next => .fault fault next
      | .exhausted next => .exhausted next
  | .fieldGet target field =>
      match eval program fuel scope trace target with
      | .value (.record _ fields) next =>
          match fieldValue? fields field with
          | some value => .value value next
          | none => .fault (.fieldAbsent field) next
      | .value _ next => .fault .notARecord next
      | .fault fault next => .fault fault next
      | .exhausted next => .exhausted next
  | .ifThenElse condition consequent alternate =>
      match eval program fuel scope trace condition with
      | .value (.boolean true) next => eval program fuel scope next consequent
      | .value (.boolean false) next => eval program fuel scope next alternate
      | .value _ next => .fault .notABoolean next
      | .fault fault next => .fault fault next
      | .exhausted next => .exhausted next
  | .boolEquals left right =>
      match eval program fuel scope trace left with
      | .value (.boolean first) next =>
          match eval program fuel scope next right with
          | .value (.boolean second) last => .value (.boolean (first == second)) last
          | .value _ last => .fault .notABoolean last
          | .fault fault last => .fault fault last
          | .exhausted last => .exhausted last
      | .value _ next => .fault .notABoolean next
      | .fault fault next => .fault fault next
      | .exhausted next => .exhausted next
  | .boolAnd left right =>
      match eval program fuel scope trace left with
      | .value (.boolean false) next => .value (.boolean false) next
      | .value (.boolean true) next =>
          match eval program fuel scope next right with
          | .value (.boolean second) last => .value (.boolean second) last
          | .value _ last => .fault .notABoolean last
          | .fault fault last => .fault fault last
          | .exhausted last => .exhausted last
      | .value _ next => .fault .notABoolean next
      | .fault fault next => .fault fault next
      | .exhausted next => .exhausted next
  | .boolOr left right =>
      match eval program fuel scope trace left with
      | .value (.boolean true) next => .value (.boolean true) next
      | .value (.boolean false) next =>
          match eval program fuel scope next right with
          | .value (.boolean second) last => .value (.boolean second) last
          | .value _ last => .fault .notABoolean last
          | .fault fault last => .fault fault last
          | .exhausted last => .exhausted last
      | .value _ next => .fault .notABoolean next
      | .fault fault next => .fault fault next
      | .exhausted next => .exhausted next
  | .boolNot operand =>
      match eval program fuel scope trace operand with
      | .value (.boolean value) next => .value (.boolean (!value)) next
      | .value _ next => .fault .notABoolean next
      | .fault fault next => .fault fault next
      | .exhausted next => .exhausted next
  | .someValue value =>
      match eval program fuel scope trace value with
      | .value inner next => .value (.present inner) next
      | .fault fault next => .fault fault next
      | .exhausted next => .exhausted next
  | .noneValue => .value .absent trace
  | .variant type name arguments =>
      match evalList program fuel scope trace arguments with
      | .values values next => .value (.variant type name values) next
      | .fault fault next => .fault fault next
      | .exhausted next => .exhausted next
  | .record type fields =>
      match evalFields program fuel scope trace fields with
      | .fields values next => .value (.record type values) next
      | .fault fault next => .fault fault next
      | .exhausted next => .exhausted next
  | .matchOn type scrutinee cases =>
      match eval program fuel scope trace scrutinee with
      | .value (.variant valueType name arguments) next =>
          if valueType = type then evalCases program fuel scope next name arguments cases
          else .fault .notAVariant next
      | .value _ next => .fault .notAVariant next
      | .fault fault next => .fault fault next
      | .exhausted next => .exhausted next
  | .call function arguments =>
      match evalList program fuel scope trace arguments with
      | .values values next => enter program fuel next function values
      | .fault fault next => .fault fault next
      | .exhausted next => .exhausted next
  | .lambda parameters body => .value (.closure scope parameters body) trace
  | .apply callee arguments =>
      match eval program fuel scope trace callee with
      | .value (.closure captured parameters body) next =>
          match evalList program fuel scope next arguments with
          | .values values last => applyClosure program fuel last captured parameters body values
          | .fault fault last => .fault fault last
          | .exhausted last => .exhausted last
      | .value _ next => .fault .notAClosure next
      | .fault fault next => .fault fault next
      | .exhausted next => .exhausted next
termination_by expression => (fuel, sizeOf expression)

/-- Enters one declared function on already evaluated arguments. The callee's scope is the argument
list reversed, so de Bruijn index `0` is its last parameter, and entry costs one unit of fuel. -/
def enter (program : Ir.Program) (fuel : Nat) (trace : Trace) (function : String)
    (values : List Value) : Outcome :=
  match program.function? function with
  | none => .fault (.undeclaredFunction function) trace
  | some (parameters, _, _, body) =>
      if parameters.length = values.length then
        match fuel with
        | 0 => .exhausted trace
        | remaining + 1 =>
            eval program remaining values.reverse (trace ++ [.function function values]) body
      else .fault (.arityMismatch function parameters.length values.length) trace
termination_by (fuel, 0)

/--
Applies one inline closure to already evaluated arguments. The body sees the parameters at the
innermost indices in reverse order and the captured enclosing binders beneath them, exactly as
Coverage v5's emitter builds `parameters.reverse.concat(scope)`. Entry records the exact anonymous
code identity and costs one unit of fuel.
-/
def applyClosure (program : Ir.Program) (fuel : Nat) (trace : Trace) (captured : List Value)
    (parameters : List Ir.Field) (body : Ir.Expr) (values : List Value) : Outcome :=
  if parameters.length = values.length then
    match fuel with
    | 0 => .exhausted trace
    | remaining + 1 =>
        eval program remaining (values.reverse ++ captured)
          (trace ++ [.application ⟨parameters, body⟩ values]) body
  else .fault (.closureArity parameters.length values.length) trace
termination_by (fuel, 0)

/-- Evaluates a list of expressions left to right. -/
def evalList (program : Ir.Program) (fuel : Nat) (scope : List Value) (trace : Trace) :
    List Ir.Expr → ListOutcome
  | [] => .values [] trace
  | expression :: rest =>
      match eval program fuel scope trace expression with
      | .value value next =>
          match evalList program fuel scope next rest with
          | .values values last => .values (value :: values) last
          | .fault fault last => .fault fault last
          | .exhausted last => .exhausted last
      | .fault fault next => .fault fault next
      | .exhausted next => .exhausted next
termination_by expressions => (fuel, sizeOf expressions)

/-- Evaluates a named field list left to right, keeping declaration order. -/
def evalFields (program : Ir.Program) (fuel : Nat) (scope : List Value) (trace : Trace) :
    List (String × Ir.Expr) → FieldsOutcome
  | [] => .fields [] trace
  | (name, expression) :: rest =>
      match eval program fuel scope trace expression with
      | .value value next =>
          match evalFields program fuel scope next rest with
          | .fields values last => .fields ((name, value) :: values) last
          | .fault fault last => .fault fault last
          | .exhausted last => .exhausted last
      | .fault fault next => .fault fault next
      | .exhausted next => .exhausted next
termination_by fields => (fuel, sizeOf fields)

/-- Selects the arm deciding a constructor and evaluates it with the constructor's fields bound,
innermost field last. -/
def evalCases (program : Ir.Program) (fuel : Nat) (scope : List Value) (trace : Trace)
    (name : String) (arguments : List Value) : List (String × Ir.Expr) → Outcome
  | [] => .fault (.armAbsent name) trace
  | (constructor, arm) :: rest =>
      if constructor = name then eval program fuel (arguments.reverse ++ scope) trace arm
      else evalCases program fuel scope trace name arguments rest
termination_by cases => (fuel, sizeOf cases)

end

end Source

end TSLean.LeanToTypeScript.Semantics
