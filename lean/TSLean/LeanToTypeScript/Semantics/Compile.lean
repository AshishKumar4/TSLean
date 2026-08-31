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
  /-- A named type the program does not declare. -/
  | undeclaredType (type : String)
  /-- A constructor the named enum does not declare. -/
  | undeclaredConstructor (type name : String)
  /-- A constructor applied to a different number of arguments than it declares fields. -/
  | constructorArity (type name : String) (expected actual : Nat)
  /-- A `match` on an enum that carries a payload, which has no tag-comparison lowering. -/
  | payloadMatch (type : String)
  /-- A `match` whose scrutinee computes, which the tag chain would re-evaluate per arm. -/
  | computedScrutinee (type : String)
  /-- A `match` with no arms. -/
  | emptyMatch (type : String)
  /-- A call to a function the program does not declare. -/
  | undeclaredFunction (name : String)
  /-- Field names that cannot be an own-key sequence in declaration order: one of them spells an
  array index, or two of them are the same. -/
  | unpresentableFields (type : String)
  /-- A constructor field named `kind`, which the emitted tag occupies. -/
  | reservedTagField (type name : String)
  /-- A record expression whose fields are not the declared fields in declaration order. -/
  | fieldsMismatch (type : String)
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
          | receiver :: _ => receiver.type == .named typeName
          | [] => false)
  | _ => false

/-- A declared type carries behaviour when the program declares a dot-notation method on it. -/
def behavioural (program : Ir.Program) (typeName : String) : Bool :=
  program.declarations.any (isDotNotationMethod typeName)

/--
A scrutinee the tag chain may re-read once per arm: a binding, or a field of a readable scrutinee.
Anything that computes has to be named by a `let` first, because the chain evaluates the scrutinee
once per comparison.

The condition is transitive here, and in `emitter.ts` it is not: that emitter tests only the
outermost node, so it admits a scrutinee such as a field of a call and duplicates the call once per
arm. Soundness needs the transitive condition, so the model takes it and the shallow check is a
defect reported against the emitter rather than reproduced here.
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
  | .boolEquals left right =>
      if right.isTrueLiteral then expr program left
      else if left.isTrueLiteral then expr program right
      else do pure (.strictEquals (← expr program left) (← expr program right))
  | .boolAnd left right => do pure (.logicalAnd (← expr program left) (← expr program right))
  | .boolOr left right => do pure (.logicalOr (← expr program left) (← expr program right))
  | .boolNot operand => do pure (.logicalNot (← expr program operand))
  | .someValue value => expr program value
  | .noneValue => pure .undefinedLit
  | .variant type name arguments => do
      match program.enum? type with
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
      match program.record? type with
      | none => throw (.undeclaredType type)
      | some declared =>
          if (fields.map Prod.fst) ≠ (declared.map Ir.Field.name) then
            throw (.fieldsMismatch type)
          else if presentableKeys (fields.map Prod.fst) = false then
            throw (.unpresentableFields type)
          else pure (.objectLiteral (← exprFields program fields))
  | .matchOn type scrutinee cases => do
      match program.enum? type with
      | none => throw (.undeclaredType type)
      | some constructors =>
          if Ir.allNullary constructors = false then throw (.payloadMatch type)
          else if readableScrutinee scrutinee = false then throw (.computedScrutinee type)
          else
            let target ← expr program scrutinee
            let arms ← exprCases program cases
            match tagChain target arms with
            | none => throw (.emptyMatch type)
            | some chain => pure chain
  | .call function arguments => do
      match program.function? function with
      | none => throw (.undeclaredFunction function)
      | some _ => pure (.callFunction function (← exprList program arguments))
  | .lambda parameters sourceBody => do
      pure (.arrow ⟨parameters, sourceBody⟩ (← body program sourceBody))
  | .apply callee arguments => do
      match callee with
      | .varRef index => pure (.callValue (.binding index) (← exprList program arguments))
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

/-- Lowers a function or inline-arrow body: the leading `let` run becomes `const` statements, and
the expression it ends in becomes the `return`. The measure's second component ranks a body above
the expression it delegates to, so the fall-through to `expr` on the same expression decreases even
though its size does not. -/
def body (program : Ir.Program) : Ir.Expr → Except Fault Target.Body
  | .letBind name value rest => do
      pure (.constBind name (← expr program value) (← body program rest))
  | expression => do pure (.ret (← expr program expression))
termination_by expression => (sizeOf expression, 1)

end

/-- Lowers one declaration. A record or an enum has no runtime image: `emitter.ts` gives it an
interface or a type alias, and both erase. -/
def declaration (program : Ir.Program) : Ir.Decl → Except Fault (Option Target.Function)
  | .enum _ _ | .record _ _ => pure none
  | .function name parameters _ _ bodyExpr => do
      pure (some ⟨name, parameters.length, ← body program bodyExpr⟩)


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
  | .function _ _ _ _ _ :: rest => checkRepresentations program rest
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
