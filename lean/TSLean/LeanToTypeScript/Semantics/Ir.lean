import TSLean.JS.PropertyKey
import TSLean.JS.Value

/-!
# The admitted semantic IR, as Lean data

`TSLean/LeanToTypeScript/Export.lean` writes one JSON document per compilation and
`src/lean-to-typescript/ir.ts` decodes it. This module is that document's grammar, written as Lean
data so the compiler's source language has a semantics rather than a schema.

The grammar is closed. Every expression form carries an `Op`, every declaration form a `Family`, and
every type form a `TyKind`, and each of those three registries is a finite enumeration whose wire
spelling is fixed here. `scripts/check-semantics-registry.mjs` joins these spellings against the
decoder in `ir.ts` and the lowering in `emitter.ts`, so an operation admitted on one side and absent
on the other is a build failure rather than a silent gap.
-/

namespace TSLean.LeanToTypeScript.Semantics

open TSLean.JS

namespace Ir

/-- A type of the admitted fragment. `named` refers to a declared record or enum by its Lean name. -/
inductive Ty where
  | boolean
  | option (inner : Ty)
  | named (name : String)
  deriving DecidableEq, Repr

/-- The three type forms the fragment admits, as a closed registry. -/
inductive TyKind where
  | boolean
  | option
  | named
  deriving DecidableEq, Repr

/-- The wire spelling `Export.lean` writes and `ir.ts` decodes. -/
def TyKind.kind : TyKind → String
  | .boolean => "boolean"
  | .option => "option"
  | .named => "named"

/-- Every admitted type form. -/
def TyKind.all : List TyKind := [.boolean, .option, .named]

theorem TyKind.mem_all (kind : TyKind) : kind ∈ TyKind.all := by
  cases kind <;> simp [TyKind.all]

/-- The registry entry a type belongs to. -/
def Ty.kind : Ty → TyKind
  | .boolean => .boolean
  | .option _ => .option
  | .named _ => .named

/-- One declared field: its emitted property key and its type. -/
structure Field where
  name : String
  type : Ty
  deriving DecidableEq, Repr

/-- An expression of the admitted fragment. Variables are de Bruijn indices into the enclosing
scope, innermost binder first, exactly as `Export.lean` writes them. -/
inductive Expr where
  /-- `variable`: de Bruijn reference into the enclosing scope. -/
  | varRef (index : Nat)
  /-- `boolean`: a `Bool` literal. -/
  | boolLit (value : Bool)
  /-- `let`: a named binding whose body sees it at index `0`. -/
  | letBind (name : String) (value : Expr) (body : Expr)
  /-- `field`: a declared record or constructor field read. -/
  | fieldGet (target : Expr) (field : String)
  /-- `if`: a `Bool`-decided conditional. -/
  | ifThenElse (condition consequent alternate : Expr)
  /-- `equals`: `Bool` equality, the only equality the exporter admits. -/
  | boolEquals (left right : Expr)
  /-- `and`: `Bool.and`, lazy in its right operand. -/
  | boolAnd (left right : Expr)
  /-- `or`: `Bool.or`, lazy in its right operand. -/
  | boolOr (left right : Expr)
  /-- `not`: `Bool.not`. -/
  | boolNot (operand : Expr)
  /-- `some`: `Option.some`. -/
  | someValue (value : Expr)
  /-- `none`: `Option.none`. -/
  | noneValue
  /-- `variant`: an enum constructor applied to its declared fields. -/
  | variant (type name : String) (arguments : List Expr)
  /-- `record`: a structure constructor applied to its declared fields. -/
  | record (type : String) (fields : List (String × Expr))
  /-- `match`: a total case analysis over one enum, one arm per constructor. -/
  | matchOn (type : String) (scrutinee : Expr) (cases : List (String × Expr))
  /-- `call`: an application of a declared function to its declared parameters. -/
  | call (function : String) (arguments : List Expr)
  /-- `lambda`: an inline arrow with the exact parameter list and body Coverage v5 decodes. -/
  | lambda (parameters : List Field) (body : Expr)
  /-- `apply`: an application of an arrow value to its arguments. -/
  | apply (callee : Expr) (arguments : List Expr)
  deriving Repr

/-- The seventeen expression forms the fragment admits, as a closed registry. Every preservation
theorem is indexed by this type, so a new form cannot reach the compiler without one. -/
inductive Op where
  | varRef
  | boolLit
  | letBind
  | fieldGet
  | ifThenElse
  | boolEquals
  | boolAnd
  | boolOr
  | boolNot
  | someValue
  | noneValue
  | variant
  | record
  | matchOn
  | call
  | lambda
  | apply
  deriving DecidableEq, Repr

/-- The wire spelling `Export.lean` writes and `ir.ts` decodes. -/
def Op.kind : Op → String
  | .varRef => "variable"
  | .boolLit => "boolean"
  | .letBind => "let"
  | .fieldGet => "field"
  | .ifThenElse => "if"
  | .boolEquals => "equals"
  | .boolAnd => "and"
  | .boolOr => "or"
  | .boolNot => "not"
  | .someValue => "some"
  | .noneValue => "none"
  | .variant => "variant"
  | .record => "record"
  | .matchOn => "match"
  | .call => "call"
  | .lambda => "lambda"
  | .apply => "apply"

/-- Every admitted expression form. -/
def Op.all : List Op :=
  [.varRef, .boolLit, .letBind, .fieldGet, .ifThenElse, .boolEquals, .boolAnd, .boolOr, .boolNot,
    .someValue, .noneValue, .variant, .record, .matchOn, .call, .lambda, .apply]

theorem Op.mem_all (op : Op) : op ∈ Op.all := by
  cases op <;> simp [Op.all]

/-- Distinct operations have distinct wire spellings, so the registry join is a bijection. -/
theorem Op.kind_injective {left right : Op} (equal : left.kind = right.kind) : left = right := by
  cases left <;> cases right <;> simp_all [Op.kind]

/-- The registry entry an expression belongs to. -/
def Expr.op : Expr → Op
  | .varRef _ => .varRef
  | .boolLit _ => .boolLit
  | .letBind _ _ _ => .letBind
  | .fieldGet _ _ => .fieldGet
  | .ifThenElse _ _ _ => .ifThenElse
  | .boolEquals _ _ => .boolEquals
  | .boolAnd _ _ => .boolAnd
  | .boolOr _ _ => .boolOr
  | .boolNot _ => .boolNot
  | .someValue _ => .someValue
  | .noneValue => .noneValue
  | .variant _ _ _ => .variant
  | .record _ _ => .record
  | .matchOn _ _ _ => .matchOn
  | .call _ _ => .call
  | .lambda _ _ => .lambda
  | .apply _ _ => .apply

/-- The `true` literal, which `emitter.ts` folds out of a `Bool` equality. -/
def Expr.isTrueLiteral : Expr → Bool
  | .boolLit true => true
  | _ => false

/-- The test recognises exactly the `true` literal. -/
theorem Expr.eq_of_isTrueLiteral {expression : Expr}
    (literal : expression.isTrueLiteral = true) : expression = .boolLit true := by
  unfold Expr.isTrueLiteral at literal
  split at literal
  · rfl
  · exact absurd literal (by simp)

/-- The immediate subexpressions of one expression, in evaluation order. -/
def Expr.children : Expr → List Expr
  | .varRef _ | .boolLit _ | .noneValue => []
  | .letBind _ value body => [value, body]
  | .fieldGet target _ => [target]
  | .ifThenElse condition consequent alternate => [condition, consequent, alternate]
  | .boolEquals left right | .boolAnd left right | .boolOr left right => [left, right]
  | .boolNot operand | .someValue operand => [operand]
  | .variant _ _ arguments => arguments
  | .record _ fields => fields.map Prod.snd
  | .matchOn _ scrutinee cases => scrutinee :: cases.map Prod.snd
  | .call _ arguments => arguments
  | .lambda _ body => [body]
  | .apply callee arguments => callee :: arguments

/--
The code identity of one anonymous v5 lambda. It is a label for an application trace and the
function object's semantic provenance. It is not an index and it is never used to look up a body:
the closure itself owns its stored body.
-/
structure LambdaCode where
  parameters : List Field
  body : Expr
  deriving Repr


/-- One declared enum constructor and the fields it carries, in declaration order. -/
structure Constructor where
  name : String
  fields : List Field
  deriving DecidableEq, Repr

/-- A declaration of the admitted fragment. -/
inductive Decl where
  /-- `enum`: an inductive data type with no parameters and no indices. -/
  | enum (name : String) (constructors : List Constructor)
  /-- `record`: a structure with declared fields in declaration order. -/
  | record (name : String) (fields : List Field)
  /-- `function`: a first-order definition. `recursion` names the parameter Lean proved it
  recurses structurally on, and is absent for a non-recursive definition. -/
  | function (name : String) (parameters : List Field) (result : Ty)
      (recursion : Option Nat) (body : Expr)
  deriving Repr

/-- The three declaration families the fragment admits, as a closed registry. -/
inductive Family where
  | enum
  | record
  | function
  deriving DecidableEq, Repr

/-- The wire spelling `Export.lean` writes and `ir.ts` decodes. -/
def Family.kind : Family → String
  | .enum => "enum"
  | .record => "record"
  | .function => "function"

/-- Every admitted declaration family. -/
def Family.all : List Family := [.enum, .record, .function]

theorem Family.mem_all (family : Family) : family ∈ Family.all := by
  cases family <;> simp [Family.all]

/-- Distinct families have distinct wire spellings. -/
theorem Family.kind_injective {left right : Family} (equal : left.kind = right.kind) :
    left = right := by
  cases left <;> cases right <;> simp_all [Family.kind]

/-- The registry entry a declaration belongs to. -/
def Decl.family : Decl → Family
  | .enum _ _ => .enum
  | .record _ _ => .record
  | .function _ _ _ _ _ => .function

/-- The declared name of a declaration. -/
def Decl.name : Decl → String
  | .enum name _ | .record name _ | .function name _ _ _ _ => name

/-- One compilation unit: the declarations reachable from the exported roots. -/
structure Program where
  declarations : List Decl
  deriving Repr

/-- The declaration carrying a name, if the program declares it. -/
def Program.find? (program : Program) (name : String) : Option Decl :=
  program.declarations.find? fun declaration => declaration.name == name

/-- The record declaration carrying a name. -/
def Program.record? (program : Program) (name : String) : Option (List Field) :=
  match program.find? name with
  | some (.record _ fields) => some fields
  | _ => none

/-- The enum declaration carrying a name. -/
def Program.enum? (program : Program) (name : String) : Option (List Constructor) :=
  match program.find? name with
  | some (.enum _ constructors) => some constructors
  | _ => none

/-- The function declaration carrying a name. -/
def Program.function? (program : Program) (name : String) :
    Option (List Field × Ty × Option Nat × Expr) :=
  match program.find? name with
  | some (.function _ parameters result recursion body) => some (parameters, result, recursion, body)
  | _ => none

/--
An enum no constructor of which carries a field. `emitter.ts` represents such a type by its own tag
string and every other enum by a tagged object, so the decision is a property of the whole
declaration rather than of one constructor.
-/
def allNullary (constructors : List Constructor) : Bool :=
  constructors.all fun constructor => constructor.fields.isEmpty

/-- One declared constructor of an enum, by name. -/
def constructor? (constructors : List Constructor) (name : String) : Option Constructor :=
  constructors.find? fun constructor => constructor.name == name

/-- The type declared at a field name, if the field list declares it. -/
def fieldType? (fields : List Field) (name : String) : Option Ty :=
  (fields.find? fun field => field.name == name).map Field.type

/-!
## Emitted property keys

A field name reaches the target as an own string property key. ECMAScript hoists integer-index keys
ahead of every other string key in own-key order, so a declared field spelled as an array index
could not be read back in declaration order. `Export.lean` already refuses it — an emitted field name
is an ASCII identifier, which never spells a decimal integer — and the model decides the same
condition rather than assuming the exporter's guarantee.
-/

/-- The own property key a field name reaches the target as. -/
def propertyKey (name : String) : PropertyKey := .string (JSString.ofLeanString name)

/-- A field name presentable as an own string key in declaration order. -/
def ValidKey (name : String) : Prop :=
  PropertyKey.arrayIndex? (JSString.ofLeanString name) = none

instance (name : String) : Decidable (ValidKey name) := by
  unfold ValidKey; infer_instance

/-- Distinct field names reach the target as distinct property keys. -/
theorem propertyKey_injective {left right : String} (equal : propertyKey left = propertyKey right) :
    left = right := by
  unfold propertyKey at equal
  injection equal with stringEqual
  exact JSString.ofLeanString_injective stringEqual

/-!
## The arrow object's own keys

An emitted arrow is a heap-allocated function object. Its executable body is an internal closure
slot, not a JavaScript property and not an index into a program table. The heap object carries one
own data property per captured binder, in scope order. Those entries make the captured environment
observable to the target semantics and let an application read it back exactly.

Every key begins with `$`, so none spells an array index, and two captured names are distinct because
two decimal spellings of distinct positions are.
-/

/-- The own property carrying the binder at position `index` of the captured scope. -/
def capturedKey (index : Nat) : String := "$captured" ++ index.repr

/-- Every captured key is presentable: `arrayIndex?` reads the leading code unit, and every captured
key leads with `$`. -/
theorem capturedKey_valid (index : Nat) : ValidKey (capturedKey index) := by
  unfold ValidKey capturedKey
  rw [JSString.ofLeanString_append]
  rfl

/-- Distinct positions carry distinct captured keys, so an arrow's own keys never collide. -/
theorem capturedKey_injective {left right : Nat} (equal : capturedKey left = capturedKey right) :
    left = right := by
  have digits : Nat.toDigits 10 left = Nat.toDigits 10 right := by
    have lists := congrArg String.toList equal
    simp only [capturedKey, String.toList_append, Nat.toList_repr] at lists
    exact List.append_cancel_left lists
  calc left = Nat.ofDigitChars 10 (Nat.toDigits 10 left) 0 := Nat.ofDigitChars_ten_toDigits.symm
    _ = Nat.ofDigitChars 10 (Nat.toDigits 10 right) 0 := by rw [digits]
    _ = right := Nat.ofDigitChars_ten_toDigits

/-- The captured scope's own properties, starting at position `start`, in scope order. -/
def capturedEntries (start : Nat) : List Value → List (String × Value)
  | [] => []
  | value :: rest => (capturedKey start, value) :: capturedEntries (start + 1) rest

/-- The own-property sequence an arrow object carries: exactly its captured scope. -/
def closureEntries (captured : List Value) : List (String × Value) := capturedEntries 0 captured

/-- The captured scope contributes exactly one own property per binder. -/
theorem capturedEntries_length :
    ∀ (start : Nat) (values : List Value), (capturedEntries start values).length = values.length
  | _, [] => rfl
  | start, _ :: rest => by
      simp only [capturedEntries, List.length_cons]
      rw [capturedEntries_length (start + 1) rest]

/-- Every key the captured scope contributes names a position at or after where it starts. -/
theorem capturedEntries_key_ge :
    ∀ (start : Nat) (values : List Value) (index : Nat),
      capturedKey index ∈ (capturedEntries start values).map Prod.fst → start ≤ index
  | _, [], _, member => by simp [capturedEntries] at member
  | start, _ :: rest, index, member => by
      simp only [capturedEntries, List.map_cons, List.mem_cons] at member
      rcases member with head | tail
      · exact Nat.le_of_eq (capturedKey_injective head).symm
      · exact Nat.le_of_succ_le (capturedEntries_key_ge (start + 1) rest index tail)

/-- Every own key the captured scope contributes is presentable. -/
theorem capturedEntries_valid :
    ∀ (start : Nat) (values : List Value) (entry : String × Value),
      entry ∈ capturedEntries start values → ValidKey entry.1
  | _, [], _, member => by simp [capturedEntries] at member
  | start, _ :: rest, entry, member => by
      simp only [capturedEntries, List.mem_cons] at member
      rcases member with rfl | tail
      · exact capturedKey_valid start
      · exact capturedEntries_valid (start + 1) rest entry tail

/-- Every value the captured scope contributes is one of the captured binders. -/
theorem capturedEntries_mem :
    ∀ (start : Nat) (values : List Value) (entry : String × Value),
      entry ∈ capturedEntries start values → entry.2 ∈ values
  | _, [], _, member => by simp [capturedEntries] at member
  | start, head :: rest, entry, member => by
      simp only [capturedEntries, List.mem_cons] at member
      rcases member with rfl | tail
      · simp
      · exact List.mem_cons_of_mem head (capturedEntries_mem (start + 1) rest entry tail)

/-- The captured scope's own keys are distinct. -/
theorem capturedEntries_nodup :
    ∀ (start : Nat) (values : List Value), ((capturedEntries start values).map Prod.fst).Nodup
  | _, [] => by simp [capturedEntries]
  | start, _ :: rest => by
      simp only [capturedEntries, List.map_cons, List.nodup_cons]
      refine ⟨fun member => ?_, capturedEntries_nodup (start + 1) rest⟩
      exact absurd (capturedEntries_key_ge (start + 1) rest start member) (by omega)

/-- Every own key an arrow object carries is presentable. -/
theorem closureEntries_valid (captured : List Value) :
    ∀ entry ∈ closureEntries captured, ValidKey entry.1
  | entry, member => capturedEntries_valid 0 captured entry member

/-- An arrow object's own keys are distinct, so every captured binder survives the allocation. -/
theorem closureEntries_nodup (captured : List Value) :
    ((closureEntries captured).map Prod.fst).Nodup := capturedEntries_nodup 0 captured

/-- Reading the captured key at a position answers the binder captured at that position. -/
theorem capturedEntries_find :
    ∀ (start : Nat) (taken rest : List Value) (value : Value),
      ((capturedEntries start (taken ++ value :: rest)).find? fun entry =>
          entry.1 == capturedKey (start + taken.length))
        = some (capturedKey (start + taken.length), value)
  | start, [], rest, value => by
      simp [capturedEntries]
  | start, head :: taken, rest, value => by
      have step : start + (head :: taken).length = start + 1 + taken.length := by
        simp only [List.length_cons]
        omega
      have miss :
          ¬((capturedKey start == capturedKey (start + (head :: taken).length)) = true) := by
        simp only [beq_iff_eq]
        intro same
        have index := capturedKey_injective same
        simp only [List.length_cons] at index
        omega
      simp only [List.cons_append, capturedEntries]
      rw [List.find?_cons_of_neg (by simpa using miss), step]
      exact capturedEntries_find (start + 1) taken rest value

/-- An arrow object's captured key at a position answers the binder captured there. -/
theorem closureEntries_find_captured (taken rest : List Value) (value : Value) :
    ((closureEntries (taken ++ value :: rest)).find? fun entry =>
        entry.1 == capturedKey taken.length)
      = some (capturedKey taken.length, value) := by
  simpa [closureEntries] using capturedEntries_find 0 taken rest value

end Ir

end TSLean.LeanToTypeScript.Semantics
