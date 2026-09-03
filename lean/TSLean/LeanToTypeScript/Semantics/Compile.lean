import TSLean.LeanToTypeScript.Semantics.Target

/-!
# The modeled lowering

`Compile` is this model of what `src/lean-to-typescript/emitter.ts` builds for each IR operation.
Every clause corresponds to one branch of that emitter, and every refusal to one of its typed
rejections, so the preservation theorems are about the lowering the compiler performs rather than
about an idealised one.

## The one boundary this model draws

`emitter.ts` gives a declared type one of two representations. A type with no dot-notation function
over it stays *structural*: a record is an object literal, an enum is a tag or a tagged object. A
type that carries dot-notation behaviour becomes a *nominal* class, with per-constructor subclasses,
static factories, frozen instances and virtual dispatch.

This model lowers the structural representation and refuses a behavioural type by name, with
`Fault.behaviouralType`. The refusal is exact and checked: `Program.behavioural` decides the same
condition `isDotNotationMethod` decides in the emitter, so a program the model admits is one whose
every declared type the emitter also represents structurally. Modelling the nominal representation
needs frozen-instance property observations that `TSLean/JS/Heap.lean` does not export, so the
boundary is recorded here rather than assumed away.

## The two arrow constraints, kept explicit

A `lambda` lowers its exact inline parameter list and body to one target arrow whose callable payload
owns the compiled body. There is no program arrow table. An `apply` becomes a call on the value a
binding holds, and a callee that is not a bound variable is refused by name with
`Fault.computedCallee`: the decoder admits no other target, so lowering one would be lowering a
program the decoder cannot produce.

## The two body positions, kept apart

`emitter.ts` has two body forms, and this model has both. A function or host-boundary declaration is
emitted by `emitReturn`, which builds *statements*: a `const` run, an `if` whose consequent returns,
and a `match` as one `if` per alternative with the payload bound by `const`s inside the branch that
decided it. `Compile.returnBody` lowers exactly that. An inline arrow is emitted by
`emitExpression`, which builds one *expression* for its concise body, and `Compile.body` lowers
that.

The one shape left outside is a payload-carrying `match` in argument position: no statement can be
emitted there, so `emitter.ts` substitutes each payload read into the arm that reads it, and this
model refuses that form by name with `Fault.substitutedMatch` rather than claiming the theorem
covers it.
-/

namespace TSLean.LeanToTypeScript.Semantics

namespace Compile

/-- A typed reason the lowering refuses an IR program. Each one mirrors a rejection in
`emitter.ts`. -/
inductive Fault where
  /-- A `let` that is not part of a function body's leading run. -/
  | nestedLet (name : String)
  /-- A declared type carrying dot-notation behaviour, which this model does not lower. -/
  | behaviouralType (type : String)
  /-- A type the program does not declare, or one that carries no constructors. -/
  | undeclaredType (type : Ir.Ty)
  /-- A constructor the named enum does not declare. -/
  | undeclaredConstructor (type : Ir.Ty) (name : String)
  /-- A constructor applied to a different number of arguments than it declares fields. -/
  | constructorArity (type : Ir.Ty) (name : String) (expected actual : Nat)
  /-- A payload-carrying `match` outside return position. No statement can be emitted there, so
  `emitter.ts` substitutes each payload read into the arm that reads it instead of naming it with a
  `const`; this model lowers the statement form, where the payload is bound, so the substituted form
  is refused by name rather than given a lowering the theorem does not cover. -/
  | substitutedMatch (type : Ir.Ty)
  /-- A `match` whose arms are not every declared constructor exactly once in declaration order, or
  whose type declares two constructors under one name. The emitted `if` chain reads each arm's
  payload field list positionally out of the declaration, so an arm out of order would name another
  constructor's fields. `ir.ts` refuses the same document. -/
  | armOrder (type : Ir.Ty)
  /-- A `match` on a `List`. Its values reach the target as a dense array, so the emitted tests are
  length comparisons and its payload reads are `subject[0]` and `subject.slice(1)` rather than a tag
  comparison and two own-property reads: a third dispatch shape this model does not carry. -/
  | listMatch (type : Ir.Ty)
  /-- A `match` on a one-constructor structure — a `pair`, or a declared `record`. `Source.eval`
  gives such a value the `record` form, whose fields are read with field reads, so a match on one is
  refused rather than given a lowering whose refinement would hold only because the source faults. -/
  | structureMatch (type : Ir.Ty)
  /-- A `match` whose scrutinee computes, which the tag chain would re-evaluate per arm. -/
  | computedScrutinee (type : Ir.Ty)
  /-- A `match` with no arms. -/
  | emptyMatch (type : Ir.Ty)
  /-- A call to a function the program does not declare. -/
  | undeclaredFunction (name : String)
  /-- Field names that cannot be an own-key sequence in declaration order: one of them spells an
  array index, or two of them are the same. -/
  | unpresentableFields (type : Ir.Ty)
  /-- A constructor field named `kind`, which the emitted tag occupies. -/
  | reservedTagField (type : Ir.Ty) (name : String)
  /-- A record expression whose fields are not the declared fields in declaration order. -/
  | fieldsMismatch (type : Ir.Ty)
  /-- An application whose callee computes. `src/lean-to-typescript/ir.ts` admits an application
  target that is a bound variable and nothing else, so an application of anything else is refused
  here rather than given a lowering the decoder cannot produce. -/
  | computedCallee
  deriving DecidableEq, Repr

/--
Field names an ECMAScript object can present as its own keys in declaration order: none of them
spells an array index, because integer-index keys are hoisted ahead of every other string key, and no
two of them are the same, because a duplicate would overwrite.
-/
def presentableKeys (names : List String) : Bool :=
  names.all (fun name => decide (Ir.ValidKey name)) && decide names.Nodup

/-- The key check accepts exactly the presentable name sequences. -/
theorem presentableKeys_iff {names : List String} :
    presentableKeys names = true ↔ (∀ name ∈ names, Ir.ValidKey name) ∧ names.Nodup := by
  unfold presentableKeys
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_iff]

/--
Lean dot notation names the receiver, so `T.f (t : T) …` is a method on `T`. This decides the same
condition as `isDotNotationMethod` in `emitter.ts`: the name is one component under the type's own
name, and the first parameter is the type itself.
-/
def isDotNotationMethod (typeName : String) : Ir.Decl → Bool
  | .function name parameters _ _ _ =>
      name.startsWith (typeName ++ ".") &&
        !(name.drop (typeName.length + 1)).contains '.' &&
        (match parameters with
          | receiver :: _ =>
              match receiver.type with
              | .named name _ => name == typeName
              | _ => false
          | [] => false)
  | _ => false

/-- A declared type carries behaviour when the program declares a dot-notation method on it. -/
def behavioural (program : Ir.Program) (typeName : String) : Bool :=
  program.declarations.any (isDotNotationMethod typeName)

/--
A scrutinee the tag chain may re-read once per arm: a binding, or a field of a readable scrutinee.
Anything that computes has to be named by a `let` first, because the chain evaluates the scrutinee
once per comparison.

`isRereadable` in `emitter.ts` decides the same transitive condition, clause for clause, so a match
that emitter lowers to a tag chain is one this model admits. It is the argument-position condition
only: in return position the emitter names the scrutinee with a `const` and evaluates it exactly
once, which is what `Compile.returnBody` lowers and what `Target.Body.branch` evaluates once, so no
re-readability is required there.
-/
def readableScrutinee : Ir.Expr → Bool
  | .varRef _ => true
  | .fieldGet subject _ => readableScrutinee subject
  | _ => false

/-- The `===` chain a tag match lowers to: one comparison per arm in order, with the final arm
unconditional because the IR has already decided every constructor exactly once. -/
def tagChain (scrutinee : Target.Expr) : List (String × Target.Expr) → Option Target.Expr
  | [] => none
  | [(_, value)] => some value
  | (tag, value) :: rest =>
      (tagChain scrutinee rest).map fun alternate =>
        .conditional (.strictEquals scrutinee (.stringLit tag)) value alternate

/--
The types a `match` takes apart. `Source.eval` decides a `variant` value by its constructor, so a
type whose values are `variant`s is one a tag dispatch can decide: the three mapped unions and a
declared `enum`. A structure's value is a `record`, whose fields are read with field reads, and a
`List`'s value is an array, whose alternatives are decided by length — neither is a tag dispatch, so
each is refused under its own name.
-/
def destructurable (program : Ir.Program) : Ir.Ty → Bool
  | .option _ | .except _ _ | .json => true
  | .named name _ =>
      match program.find? name with
      | some (.enum _ _) => true
      | _ => false
  | .boolean | .nat | .string | .parameter _ | .list _ | .function _ _ | .int | .char | .bytes
  | .array _ | .pair _ _ | .hashMap _ _ | .treeMap _ _ => false

/--
The arms decide every declared constructor exactly once, in declaration order, and no two declared
constructors share a name. `ir.ts` refuses the same document, and the emitted `if` chain reads each
arm's payload field list positionally out of the declaration, so an arm out of order would name
another constructor's fields. The distinctness is what makes the constructor a decided tag selects
the one the arm at that position declares.
-/
def decidesInOrder (constructors : List Ir.Constructor) (cases : List (String × Ir.Expr)) : Bool :=
  (cases.map Prod.fst == constructors.map Ir.Constructor.name) &&
    decide (constructors.map Ir.Constructor.name).Nodup

/--
Every alternative's payload can be read back off the value that decided it: its field names are own
keys presentable in declaration order, and none of them is the `kind` the emitted tag occupies.
`assertRepresentationNames` in `emitter.ts` refuses a declaration for the same collision.
-/
def checkPayloads (type : Ir.Ty) : List Ir.Constructor → Except Fault Unit
  | [] => pure ()
  | constructor :: rest =>
      if presentableKeys (constructor.fields.map Ir.Field.name) = false then
        throw (.unpresentableFields type)
      else if (constructor.fields.map Ir.Field.name).all (· != "kind") = false then
        throw (.reservedTagField type constructor.name)
      else checkPayloads type rest

mutual

/-- Lowers one IR expression. -/
def expr (program : Ir.Program) : Ir.Expr → Except Fault Target.Expr
  | .varRef index => pure (.binding index)
  | .boolLit value => pure (.boolLit value)
  | .letBind name _ _ => throw (.nestedLet name)
  | .fieldGet target field => do pure (.member (← expr program target) field)
  | .ifThenElse condition consequent alternate => do
      pure (.conditional (← expr program condition) (← expr program consequent)
        (← expr program alternate))
  | .natLit value => pure (.bigintLit value)
  | .stringLit value => pure (.stringLit value)
  | .operation opcode _ arguments => do
      match opcode.operator?, arguments with
      | some .logicalAnd, [left, right] =>
          pure (.logicalAnd (← expr program left) (← expr program right))
      | some .logicalOr, [left, right] =>
          pure (.logicalOr (← expr program left) (← expr program right))
      | some .logicalNot, [operand] => pure (.logicalNot (← expr program operand))
      | some .strictEquals, [left, right] =>
          if right.isTrueLiteral then expr program left
          else if left.isTrueLiteral then expr program right
          else pure (.strictEquals (← expr program left) (← expr program right))
      | _, arguments => pure (.operation opcode (← exprList program arguments))
  | .variant type name arguments => do
      match type.element? with
      | some element =>
          match name, arguments with
          | "nil", [] => pure .arrayEmpty
          | "cons", [head, tail] => pure (.arrayCons (← expr program head) (← expr program tail))
          | name, _ => throw (.undeclaredConstructor (.list element) name)
      | none =>
          match program.constructorsOf type with
          | none => throw (.undeclaredType type)
          | some constructors =>
              match Ir.constructor? constructors name with
              | none => throw (.undeclaredConstructor type name)
              | some constructor =>
                  let values ← exprList program arguments
                  if constructor.fields.length ≠ values.length then
                    throw (.constructorArity type name constructor.fields.length values.length)
                  else if presentableKeys (constructor.fields.map Ir.Field.name) = false then
                    throw (.unpresentableFields type)
                  else if (constructor.fields.map Ir.Field.name).all (· != "kind") = false then
                    throw (.reservedTagField type name)
                  else if Ir.allNullary constructors && constructor.fields.isEmpty then
                    pure (.stringLit name)
                  else
                    pure (.objectLiteral (("kind", .stringLit name) ::
                      (constructor.fields.map Ir.Field.name).zip values))
  | .record type fields => do
      match program.constructorsOf type with
      | some [constructor] =>
          if (fields.map Prod.fst) ≠ (constructor.fields.map Ir.Field.name) then
            throw (.fieldsMismatch type)
          else if presentableKeys (fields.map Prod.fst) = false then
            throw (.unpresentableFields type)
          else pure (.objectLiteral (← exprFields program fields))
      | _ => throw (.undeclaredType type)
  | .matchOn type scrutinee cases => do
      match program.constructorsOf type with
      | none => throw (.undeclaredType type)
      | some constructors =>
          if Ir.allNullary constructors = false then throw (.substitutedMatch type)
          else if readableScrutinee scrutinee = false then throw (.computedScrutinee type)
          else
            let target ← expr program scrutinee
            let arms ← exprCases program cases
            match tagChain target arms with
            | none => throw (.emptyMatch type)
            | some chain => pure chain
  | .call function _ arguments => do
      match program.function? function with
      | none => throw (.undeclaredFunction function)
      | some _ => pure (.callFunction function (← exprList program arguments))
  | .lambda parameters sourceBody => do
      pure (.arrow ⟨parameters, sourceBody⟩ (← body program sourceBody))
  | .apply callee arguments => do
      match callee with
      | .varRef index => pure (.callValue (.binding index) (← exprList program arguments))
      | .fieldGet subject field =>
          pure (.callValue (.member (← expr program subject) field) (← exprList program arguments))
      | _ => throw .computedCallee
termination_by expression => (sizeOf expression, 0)

/-- Lowers a positional argument list. -/
def exprList (program : Ir.Program) : List Ir.Expr → Except Fault (List Target.Expr)
  | [] => pure []
  | expression :: rest => do pure ((← expr program expression) :: (← exprList program rest))
termination_by expressions => (sizeOf expressions, 0)

/-- Lowers a named field list, keeping declaration order. -/
def exprFields (program : Ir.Program) :
    List (String × Ir.Expr) → Except Fault (List (String × Target.Expr))
  | [] => pure []
  | (name, expression) :: rest => do
      pure ((name, ← expr program expression) :: (← exprFields program rest))
termination_by fields => (sizeOf fields, 0)

/-- Lowers a match's arms, keeping their order. -/
def exprCases (program : Ir.Program) :
    List (String × Ir.Expr) → Except Fault (List (String × Target.Expr))
  | [] => pure []
  | (constructor, arm) :: rest => do
      pure ((constructor, ← expr program arm) :: (← exprCases program rest))
termination_by cases => (sizeOf cases, 0)

/-- Lowers an inline arrow's body, which `emitExpression` emits as one concise expression. The
measure's second component ranks a body above the expression it delegates to, so the fall-through to
`expr` on the same expression decreases even though its size does not. -/
def body (program : Ir.Program) : Ir.Expr → Except Fault Target.Body
  | .letBind name value rest => do
      pure (.constBind name (← expr program value) (← body program rest))
  | expression => do pure (.ret (← expr program expression))
termination_by expression => (sizeOf expression, 1)

/--
Lowers a function or host-boundary declaration body, which `emitReturn` emits as statements: the
leading `let` run becomes `const` statements, an `if` becomes an `if` whose consequent returns, a
`match` becomes the tag dispatch with its payload bound by `const`s inside the branch that decided
it, and the expression a branch ends in becomes its `return`.
-/
def returnBody (program : Ir.Program) : Ir.Expr → Except Fault Target.Body
  | .letBind name value rest => do
      pure (.constBind name (← expr program value) (← returnBody program rest))
  | .ifThenElse condition consequent alternate => do
      pure (.ifThen (← expr program condition) (← returnBody program consequent)
        (← returnBody program alternate))
  | .matchOn type scrutinee cases => do
      match program.constructorsOf type with
      | none => throw (.undeclaredType type)
      | some constructors =>
          if type.element?.isSome = true then throw (.listMatch type)
          else if destructurable program type = false then throw (.structureMatch type)
          else if cases.isEmpty = true then throw (.emptyMatch type)
          else if decidesInOrder constructors cases = false then throw (.armOrder type)
          else do
            checkPayloads type constructors
            pure (.branch (← expr program scrutinee)
              (if Ir.allNullary constructors = true then .tag else .tagged)
              (← returnArms program type constructors cases))
  | expression => do pure (.ret (← expr program expression))
termination_by expression => (sizeOf expression, 1)

/-- Lowers a match's arms against the constructors they decide, in declaration order. Each arm
carries the constructor's name and its payload field names, which is exactly what the emitted `if`
chain tests and names. -/
def returnArms (program : Ir.Program) (type : Ir.Ty) :
    List Ir.Constructor → List (String × Ir.Expr) →
      Except Fault (List (String × List String × Target.Body))
  | [], [] => pure []
  | constructor :: constructors, (_, arm) :: cases => do
      pure ((constructor.name, constructor.fields.map Ir.Field.name, ← returnBody program arm)
        :: (← returnArms program type constructors cases))
  | [], _ :: _ | _ :: _, [] => throw (.armOrder type)
termination_by _ cases => (sizeOf cases, 1)

end

/--
Lowers one declaration. A record or an enum has no runtime image: `emitter.ts` gives it an interface
or a type alias, and both erase.

A `foreign` declaration lowers to a function carrying its *reference* body. The emitted module does
not declare that function — it imports the substrate's implementation under the same name — so what
this model proves is that a target module whose binding at that name behaves like the compiled
reference refines the source program. That the substrate's binding does behave like it is the named
premise `Program.HostSubstrate`, and it is discharged one row per host operation rather than assumed
here.
-/
def declaration (program : Ir.Program) : Ir.Decl → Except Fault (Option Target.Function)
  | .enum _ _ | .record _ _ _ => pure none
  | .function name parameters _ _ bodyExpr =>
      do pure (some ⟨name, parameters.length, ← returnBody program bodyExpr⟩)
  | .foreign name _ parameters _ reference =>
      do pure (some ⟨name, parameters.length, ← returnBody program reference⟩)


/-- Lowers a declaration list to the functions it contributes. -/
def declarations (program : Ir.Program) : List Ir.Decl → Except Fault (List Target.Function)
  | [] => pure []
  | head :: rest => do
      match ← declaration program head with
      | none => declarations program rest
      | some emitted => pure (emitted :: (← declarations program rest))

/-- Refuses every declared type this model does not represent. -/
def checkRepresentations (program : Ir.Program) : List Ir.Decl → Except Fault Unit
  | [] => pure ()
  | .function _ _ _ _ _ :: rest | .foreign _ _ _ _ _ :: rest => checkRepresentations program rest
  | declaration :: rest =>
      if behavioural program declaration.name then throw (.behaviouralType declaration.name)
      else checkRepresentations program rest

/-- Lowers a whole IR program. Inline arrows lower within their enclosing expression; no secondary
arrow table exists. -/
def program (source : Ir.Program) : Except Fault Target.Program := do
  checkRepresentations source source.declarations
  pure ⟨← declarations source source.declarations⟩

end Compile

end TSLean.LeanToTypeScript.Semantics
