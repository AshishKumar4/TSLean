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

/--
A value of the admitted fragment. `Option`, `Except` and `List` values are `variant`s at their
mapped type, exactly as `constructorsOf` says, so a source list is a `nil`/`cons` chain rather than
a fourth kind of value.
-/
inductive Value where
  | boolean (value : Bool)
  | nat (value : Nat)
  | string (value : String)
  /-- An `Int`. It shares the target's bigint representation with a `Nat`, which is why `int.ofNat`
  is the identity on the image rather than a conversion. -/
  | int (value : Int)
  /-- A `Char`, which reaches the target as a string of exactly one code point. -/
  | char (value : Char)
  | record (type : Ir.Ty) (fields : List (String × Value))
  /-- A `List`, holding its elements directly. `constructorsOf` gives a list `nil`/`cons`
  constructors so a match can take one apart, but that is how it is *decided*, not how it is
  *held*: the target holds a dense array, and so does this. -/
  | array (element : Ir.Ty) (elements : List Value)
  | variant (type : Ir.Ty) (name : String) (arguments : List Value)
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
  | notANat
  | notAnInt
  | notAString
  | notAChar
  | notARecord
  | fieldAbsent (field : String)
  | notAVariant
  | armAbsent (constructor : String)
  | undeclaredFunction (function : String)
  /-- A constructor the scrutinised type does not declare. -/
  | undeclaredConstructor (name : String)
  | arityMismatch (function : String) (expected actual : Nat)
  | notAClosure
  | closureArity (expected actual : Nat)
  /-- A type the fragment cannot take apart, such as a `Nat` used as a match scrutinee. -/
  | notDestructurable
  /-- An opcode reached with operands it does not accept, and how many there were. -/
  | opcodeOperands (opcode : Ir.Opcode) (operands : Nat)
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

/-- The element type an opcode's first type argument names. -/
def elementType (typeArguments : List Ir.Ty) : Ir.Ty := (typeArguments[0]?).getD .boolean

/-- The image type an opcode's second type argument names. -/
def imageType (typeArguments : List Ir.Ty) : Ir.Ty := (typeArguments[1]?).getD .boolean

/--
The characters a `List Char` value carries, and `none` for a list carrying anything else.

`string.ofList` is the one opcode whose operand is a homogeneous list of a *primitive* it has to read
back rather than pass along, so the read is written once here instead of inside the opcode clause.
-/
def charList? : List Value → Option (List Char)
  | [] => some []
  | .char character :: rest => (charList? rest).map fun characters => character :: characters
  | _ :: _ => none

/-- Exactly a list of character values answers a character list, element for element. -/
theorem charList?_eq_some : ∀ {values : List Value} {characters : List Char},
    charList? values = some characters → values = characters.map Value.char
  | [], _, read => by simpa [charList?] using read.symm
  | .char character :: rest, characters, read => by
      simp only [charList?, Option.map_eq_some_iff] at read
      obtain ⟨tail, tailRead, characterEq⟩ := read
      rw [← characterEq, List.map_cons, charList?_eq_some tailRead]
  | .boolean _ :: _, _, read | .nat _ :: _, _, read | .int _ :: _, _, read
  | .string _ :: _, _, read | .record _ _ :: _, _, read | .array _ _ :: _, _, read
  | .variant _ _ _ :: _, _, read | .closure _ _ _ :: _, _, read => by simp [charList?] at read

/-- A character list is read back exactly. -/
theorem charList?_map : ∀ characters : List Char,
    charList? (characters.map Value.char) = some characters
  | [] => rfl
  | character :: rest => by simp [charList?, charList?_map rest]

/--
The strict, first-order opcodes, as a total function on operand lists: one clause per opcode and
accepted operand shape, and one refusal carrying the opcode and the number of operands it was
reached with. Every shape an opcode does not accept is that typed fault rather than a silent
default, so a mis-shaped operand is refused where it occurs instead of being coerced.

`bool.and` and `bool.or` are absent on purpose: ECMAScript evaluates their right operand lazily, so
they are decided in `eval`, where the unevaluated operand is still available. The six higher-order
list opcodes are absent for the same structural reason: they enter a closure, which costs fuel and
records an entry.
-/
def applyStrict (opcode : Ir.Opcode) (values : List Value) : Except Fault Value :=
  match opcode, values with
  | .boolNot, [.boolean operand] => .ok (.boolean (!operand))
  | .boolEquals, [.boolean left, .boolean right] => .ok (.boolean (left == right))
  | .natSuccessor, [.nat operand] => .ok (.nat (operand + 1))
  | .natAdd, [.nat left, .nat right] => .ok (.nat (left + right))
  | .natSubtract, [.nat left, .nat right] => .ok (.nat (left - right))
  | .natMultiply, [.nat left, .nat right] => .ok (.nat (left * right))
  | .natLess, [.nat left, .nat right] => .ok (.boolean (decide (left < right)))
  | .natLessOrEqual, [.nat left, .nat right] => .ok (.boolean (decide (left ≤ right)))
  | .natEquals, [.nat left, .nat right] => .ok (.boolean (left == right))
  | .stringAppend, [.string left, .string right] => .ok (.string (left ++ right))
  | .stringEquals, [.string left, .string right] => .ok (.boolean (left == right))
  | .listLength, [.array _ elements] => .ok (.nat elements.length)
  | .listIsEmpty, [.array _ elements] => .ok (.boolean elements.isEmpty)
  | .listReverse, [.array element elements] => .ok (.array element elements.reverse)
  | .listRest, [.array element (_ :: rest)] => .ok (.array element rest)
  | .listFirst, [.array _ (head :: _)] => .ok head
  | .listHead, [.array element []] => .ok (.variant (.option element) "none" [])
  | .listHead, [.array element (head :: _)] => .ok (.variant (.option element) "some" [head])
  | .listAppend, [.array element first, .array _ second] =>
      .ok (.array element (first ++ second))
  | .intAdd, [.int left, .int right] => .ok (.int (left + right))
  | .intSubtract, [.int left, .int right] => .ok (.int (left - right))
  | .intMultiply, [.int left, .int right] => .ok (.int (left * right))
  | .intNegate, [.int operand] => .ok (.int (-operand))
  | .intTruncatedDivide, [.int left, .int right] => .ok (.int (left.tdiv right))
  | .intTruncatedModulo, [.int left, .int right] => .ok (.int (left.tmod right))
  | .intLess, [.int left, .int right] => .ok (.boolean (decide (left < right)))
  | .intLessOrEqual, [.int left, .int right] => .ok (.boolean (decide (left ≤ right)))
  | .intEquals, [.int left, .int right] => .ok (.boolean (left == right))
  | .intOfNat, [.nat operand] => .ok (.int (Int.ofNat operand))
  | .intToNat, [.int operand] => .ok (.nat operand.toNat)
  | .charToNat, [.char operand] => .ok (.nat operand.toNat)
  | .charOfNat, [.nat operand] => .ok (.char (Char.ofNat operand))
  | .charEquals, [.char left, .char right] => .ok (.boolean (left == right))
  | .charLess, [.char left, .char right] => .ok (.boolean (decide (left < right)))
  | .stringLength, [.string operand] => .ok (.nat operand.length)
  | .stringIsEmpty, [.string operand] => .ok (.boolean operand.isEmpty)
  | .stringPush, [.string operand, .char character] => .ok (.string (operand.push character))
  | .stringSingleton, [.char character] => .ok (.string (String.singleton character))
  | .stringToList, [.string operand] =>
      .ok (.array .char (operand.toList.map Value.char))
  | .stringOfList, [.array _ elements] =>
      match charList? elements with
      | some characters => .ok (.string (String.ofList characters))
      | none => .error .notAChar
  | opcode, values => .error (.opcodeOperands opcode values.length)


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
  | .natLit value => .value (.nat value) trace
  | .stringLit value => .value (.string value) trace
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
  | .operation opcode typeArguments arguments =>
      match opcode.operator?, arguments with
      | some .logicalAnd, [left, right] =>
          match eval program fuel scope trace left with
          | .value (.boolean false) next => .value (.boolean false) next
          | .value (.boolean true) next =>
              match eval program fuel scope next right with
              | .value (.boolean value) last => .value (.boolean value) last
              | .value _ last => .fault .notABoolean last
              | .fault fault last => .fault fault last
              | .exhausted last => .exhausted last
          | .value _ next => .fault .notABoolean next
          | .fault fault next => .fault fault next
          | .exhausted next => .exhausted next
      | some .logicalOr, [left, right] =>
          match eval program fuel scope trace left with
          | .value (.boolean true) next => .value (.boolean true) next
          | .value (.boolean false) next =>
              match eval program fuel scope next right with
              | .value (.boolean value) last => .value (.boolean value) last
              | .value _ last => .fault .notABoolean last
              | .fault fault last => .fault fault last
              | .exhausted last => .exhausted last
          | .value _ next => .fault .notABoolean next
          | .fault fault next => .fault fault next
          | .exhausted next => .exhausted next
      | _, arguments =>
          match evalList program fuel scope trace arguments with
          | .values values next => applyOperation program fuel next opcode typeArguments values
          | .fault fault next => .fault fault next
          | .exhausted next => .exhausted next
  | .variant type name arguments =>
      match evalList program fuel scope trace arguments with
      | .values values next =>
          match type.element?, name, values with
          | some element, "nil", [] => .value (.array element []) next
          | some element, "cons", [head, .array _ rest] =>
              .value (.array element (head :: rest)) next
          | some _, name, _ => .fault (.undeclaredConstructor name) next
          | none, name, values => .value (.variant type name values) next
      | .fault fault next => .fault fault next
      | .exhausted next => .exhausted next
  | .record type fields =>
      match evalFields program fuel scope trace fields with
      | .fields values next => .value (.record type values) next
      | .fault fault next => .fault fault next
      | .exhausted next => .exhausted next
  | .matchOn type scrutinee cases =>
      match eval program fuel scope trace scrutinee with
      | .value (.array element elements) next =>
          if .list element = type then
            match elements with
            | [] => evalCases program fuel scope next "nil" [] cases
            | head :: rest =>
                evalCases program fuel scope next "cons" [head, .array element rest] cases
          else .fault .notAVariant next
      | .value (.variant valueType name arguments) next =>
          if valueType = type then evalCases program fuel scope next name arguments cases
          else .fault .notAVariant next
      | .value _ next => .fault .notAVariant next
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
  | .call function _ arguments =>
      match evalList program fuel scope trace arguments with
      | .values values next => enter program fuel next function values
      | .fault fault next => .fault fault next
      | .exhausted next => .exhausted next
termination_by expression => (fuel, 3, sizeOf expression)

/-- Applies one opcode to already evaluated operands, entering closures where the opcode is
higher-order. The operand positions are Coverage v5's own: `map` and `filter` take the callback
first, `any` and `all` take the subject first, and both folds take step, initial, subject. -/
def applyOperation (program : Ir.Program) (fuel : Nat) (trace : Trace) (opcode : Ir.Opcode)
    (typeArguments : List Ir.Ty) (values : List Value) : Outcome :=
  match opcode, values with
  | .listMap, [.closure captured parameters body, .array _ elements] =>
          match mapElements program fuel trace captured parameters body elements with
          | .values images last => .value (.array (imageType typeArguments) images) last
          | .fault fault last => .fault fault last
          | .exhausted last => .exhausted last
  | .listFilter, [.closure captured parameters body, .array _ elements] =>
          match filterElements program fuel trace captured parameters body elements with
          | .values kept last => .value (.array (elementType typeArguments) kept) last
          | .fault fault last => .fault fault last
          | .exhausted last => .exhausted last
  | .listAny, [.array _ elements, .closure captured parameters body] => anyElements program fuel trace captured parameters body elements
  | .listAll, [.array _ elements, .closure captured parameters body] => allElements program fuel trace captured parameters body elements
  | .listFoldLeft, [.closure captured parameters body, initial, .array _ elements] =>
          foldLeftElements program fuel trace captured parameters body initial elements
  | .listFoldRight, [.closure captured parameters body, initial, .array _ elements] =>
          foldRightElements program fuel trace captured parameters body initial elements
  | .listMap, [_, _] | .listFilter, [_, _] => .fault .notAClosure trace
  | .listAny, [_, _] | .listAll, [_, _] => .fault .notAClosure trace
  | .listFoldLeft, [_, _, _] | .listFoldRight, [_, _, _] => .fault .notAClosure trace
  | opcode, values =>
      match applyStrict opcode values with
      | .ok value => .value value trace
      | .error fault => .fault fault trace
termination_by (fuel, 2, 0)

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
termination_by (fuel, 0, 0)

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
termination_by (fuel, 0, 0)

/-- Applies a callback to every element in order, keeping the images. -/
def mapElements (program : Ir.Program) (fuel : Nat) (trace : Trace) (captured : List Value)
    (parameters : List Ir.Field) (body : Ir.Expr) : List Value → ListOutcome
  | [] => .values [] trace
  | head :: rest =>
      match applyClosure program fuel trace captured parameters body [head] with
      | .value produced next =>
          match mapElements program fuel next captured parameters body rest with
          | .values images last => .values (produced :: images) last
          | .fault fault last => .fault fault last
          | .exhausted last => .exhausted last
      | .fault fault next => .fault fault next
      | .exhausted next => .exhausted next
termination_by elements => (fuel, 1, sizeOf elements)

/-- Applies a decision to every element in order, keeping the elements it accepts. -/
def filterElements (program : Ir.Program) (fuel : Nat) (trace : Trace) (captured : List Value)
    (parameters : List Ir.Field) (body : Ir.Expr) : List Value → ListOutcome
  | [] => .values [] trace
  | head :: rest =>
      match applyClosure program fuel trace captured parameters body [head] with
      | .value (.boolean keep) next =>
          match filterElements program fuel next captured parameters body rest with
          | .values kept last => .values (if keep then head :: kept else kept) last
          | .fault fault last => .fault fault last
          | .exhausted last => .exhausted last
      | .value _ next => .fault .notABoolean next
      | .fault fault next => .fault fault next
      | .exhausted next => .exhausted next
termination_by elements => (fuel, 1, sizeOf elements)

/-- Applies a decision to every element in order, answering whether one of them holds. Every element
is entered, matching `Array.prototype.some` only where the emitted callback is total; a callback that
faults stops the run exactly as it does in the emitted program. -/
def anyElements (program : Ir.Program) (fuel : Nat) (trace : Trace) (captured : List Value)
    (parameters : List Ir.Field) (body : Ir.Expr) : List Value → Outcome
  | [] => .value (.boolean false) trace
  | head :: rest =>
      match applyClosure program fuel trace captured parameters body [head] with
      | .value (.boolean true) next => .value (.boolean true) next
      | .value (.boolean false) next =>
          anyElements program fuel next captured parameters body rest
      | .value _ next => .fault .notABoolean next
      | .fault fault next => .fault fault next
      | .exhausted next => .exhausted next
termination_by elements => (fuel, 1, sizeOf elements)

/-- Applies a decision to every element in order, answering whether all of them hold. -/
def allElements (program : Ir.Program) (fuel : Nat) (trace : Trace) (captured : List Value)
    (parameters : List Ir.Field) (body : Ir.Expr) : List Value → Outcome
  | [] => .value (.boolean true) trace
  | head :: rest =>
      match applyClosure program fuel trace captured parameters body [head] with
      | .value (.boolean false) next => .value (.boolean false) next
      | .value (.boolean true) next =>
          allElements program fuel next captured parameters body rest
      | .value _ next => .fault .notABoolean next
      | .fault fault next => .fault fault next
      | .exhausted next => .exhausted next
termination_by elements => (fuel, 1, sizeOf elements)

/-- Folds a callback over the elements from the left, accumulator first. -/
def foldLeftElements (program : Ir.Program) (fuel : Nat) (trace : Trace) (captured : List Value)
    (parameters : List Ir.Field) (body : Ir.Expr) (accumulator : Value) : List Value → Outcome
  | [] => .value accumulator trace
  | head :: rest =>
      match applyClosure program fuel trace captured parameters body [accumulator, head] with
      | .value produced next =>
          foldLeftElements program fuel next captured parameters body produced rest
      | .fault fault next => .fault fault next
      | .exhausted next => .exhausted next
termination_by elements => (fuel, 1, sizeOf elements)

/-- Folds a callback over the elements from the right, element first, matching `reduceRight`. -/
def foldRightElements (program : Ir.Program) (fuel : Nat) (trace : Trace) (captured : List Value)
    (parameters : List Ir.Field) (body : Ir.Expr) (accumulator : Value) : List Value → Outcome
  | [] => .value accumulator trace
  | head :: rest =>
      match foldRightElements program fuel trace captured parameters body accumulator rest with
      | .value produced next =>
          applyClosure program fuel next captured parameters body [head, produced]
      | .fault fault next => .fault fault next
      | .exhausted next => .exhausted next
termination_by elements => (fuel, 1, sizeOf elements)

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
termination_by expressions => (fuel, 3, sizeOf expressions)

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
termination_by fields => (fuel, 3, sizeOf fields)

/-- Selects the arm deciding a constructor and evaluates it with the constructor's fields bound,
innermost field last. -/
def evalCases (program : Ir.Program) (fuel : Nat) (scope : List Value) (trace : Trace)
    (name : String) (arguments : List Value) : List (String × Ir.Expr) → Outcome
  | [] => .fault (.armAbsent name) trace
  | (constructor, arm) :: rest =>
      if constructor = name then eval program fuel (arguments.reverse ++ scope) trace arm
      else evalCases program fuel scope trace name arguments rest
termination_by cases => (fuel, 3, sizeOf cases)

end


end Source

end TSLean.LeanToTypeScript.Semantics
