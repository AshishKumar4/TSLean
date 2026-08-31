import TSLean.JS.Conversion
import TSLean.JS.Equality

/-!
# External assumptions, as typed propositions

Nothing here is an axiom. Every claim this compiler makes about a JavaScript engine is a `Prop` over
a `Runtime` parameter, so a theorem that needs one carries it as a hypothesis and a theorem that does
not cannot silently acquire one.

`Runtime` is the interface the emitted TypeScript reaches: one field per runtime opcode, holding the
result the engine produces for exactly the form `src/lean-to-typescript/emitter.ts` emits. An
`Assumption.Id` states what those fields do, cites the ECMA-262 clause that says so, and names the
differential-oracle scenario in `spec/differential/` that measures it. `Provenance.canonicalWording` is derived
from the four recorded strings by length-prefixed concatenation, so a catalog row cannot drift from
the wording it pins.

Each opcode's assumption closure is exactly the set of assumptions that constrain the `Runtime`
fields its theorem uses. Nothing is listed that the proof does not consume, and nothing the proof
consumes is left out: `Opcode.registry` would not typecheck either way.
-/

namespace TSLean.LeanToTypeScript.Semantics

open TSLean.JS

/--
The emitted image of a Lean `Option`. `emitter.ts` gives it a tagged object, so the image names the
two shapes rather than a JavaScript value: the object itself is built by the target semantics.
-/
inductive OptionImage where
  | absent
  | present (value : Value)
  deriving DecidableEq

namespace Encode

/-- A JavaScript boolean. -/
def bool (value : Bool) : Value := .primitive (.boolean value)

/-- A JavaScript bigint. -/
def bigint (value : Int) : Value := .primitive (.bigint value)

/-- A JavaScript string. -/
def jsString (value : JSString) : Value := .primitive (.string value)

/-- A Lean `Nat` reaches the target as a JavaScript bigint, which is exact at every magnitude. A
`number` would be exact only below `2 ^ 53`. -/
def nat (value : Nat) : Value := bigint value

/-- A Lean `String` reaches the target as a JavaScript string, in UTF-16 code units. -/
def string (value : String) : Value := jsString (JSString.ofLeanString value)

/-- A Lean `Option` reaches the target as the tagged image. -/
def option : Option Value → OptionImage
  | none => .absent
  | some value => .present value

end Encode

namespace Model

/-- ECMAScript `&&`: the left operand when it is falsy, otherwise the right one. -/
def boolAnd (left right : Value) : Value := if left.toBoolean then right else left

/-- ECMAScript `||`: the left operand when it is truthy, otherwise the right one. -/
def boolOr (left right : Value) : Value := if left.toBoolean then left else right

/-- ECMAScript `!`. -/
def boolNot (operand : Value) : Value := Encode.bool (!operand.toBoolean)

/-- ECMAScript `===`. -/
def strictEquals (left right : Value) : Value := Encode.bool (strictEqual left right)

end Model

/--
What a JavaScript engine returns for each primitive emitted runtime form. Generated helpers are
composed below from the primitives their bodies reach, so their assumption closures cannot hide a
comparison, branch or representation dependency.

Array forms take and return the dense element sequence rather than a heap reference. That the engine
observes and produces exactly that sequence is itself an assumption,
`Assumption.Id.arrayDenseElementSequence`.
-/
structure Runtime where
  /-- `left && right` -/
  boolAnd : Value → Value → Value
  /-- `left || right` -/
  boolOr : Value → Value → Value
  /-- `!operand` -/
  boolNot : Value → Value
  /-- `left === right` on booleans -/
  boolEquals : Value → Value → Value
  /-- `left + right` on bigints -/
  natAdd : Value → Value → Value
  /-- raw bigint difference `left - right`; the generated truncated helper is derived below. -/
  natDifference : Value → Value → Value
  /-- ECMAScript conditional selection when branches return JavaScript values. Branches are thunks
  so the model preserves the helper's one-branch evaluation. -/
  conditionalValue : Value → (Unit → Value) → (Unit → Value) → Value
  /-- ECMAScript conditional selection when branches return tagged Option images. -/
  conditionalOption : Value → (Unit → OptionImage) → (Unit → OptionImage) → OptionImage
  /-- `left * right` on bigints -/
  natMultiply : Value → Value → Value
  /-- `left < right` on bigints -/
  natLess : Value → Value → Value
  /-- `left <= right` on bigints -/
  natLessOrEqual : Value → Value → Value
  /-- `left === right` on bigints -/
  natEquals : Value → Value → Value
  /-- `operand + 1n` -/
  natSuccessor : Value → Value
  /-- `left + right` on strings -/
  stringAppend : Value → Value → Value
  /-- `left === right` on strings -/
  stringEquals : Value → Value → Value
  /-- `BigInt(value.length)` -/
  listLength : List Value → Value
  /-- `value.length === 0` -/
  listIsEmpty : List Value → Value
  /-- `[...left, ...right]` -/
  listAppend : List Value → List Value → List Value
  /-- `[...value].reverse()` -/
  listReverse : List Value → List Value
  /-- `value.map((element) => transform(element))` -/
  listMap : (Value → Value) → List Value → List Value
  /-- `value.filter((element) => keep(element))` -/
  listFilter : (Value → Value) → List Value → List Value
  /-- `value.reduce((accumulator, element) => step(accumulator, element), initial)` -/
  listFoldLeft : (Value → Value → Value) → Value → List Value → Value
  /-- `value.reduceRight((accumulator, element) => step(element, accumulator), initial)` -/
  listFoldRight : (Value → Value → Value) → Value → List Value → Value
  /-- `value.some((element) => holds(element))` -/
  listAny : (Value → Value) → List Value → Value
  /-- `value.every((element) => holds(element))` -/
  listAll : (Value → Value) → List Value → Value
  /-- The tagged image `{ kind: "none" }`. -/
  optionNone : OptionImage
  /-- The tagged image `{ kind: "some", value }`. -/
  optionSome : Value → OptionImage
  /-- `value[0]`, emitted only under a `length === 0` guard -/
  listFirst : List Value → Value
  /-- `value.slice(1)`, emitted only under a `length === 0` guard -/
  listRest : List Value → List Value

namespace Runtime

/-- The generated `Nat` helper, derived from exactly the three runtime primitives its body reaches. -/
def natSubtract (runtime : Runtime) (left right : Value) : Value :=
  runtime.conditionalValue (runtime.natLess left right)
    (fun () => Encode.nat 0)
    (fun () => runtime.natDifference left right)

/-- The generated `List.head?` helper, derived from its guard, its nonempty read, selection and
Option representation. -/
def listHead (runtime : Runtime) (values : List Value) : OptionImage :=
  runtime.conditionalOption (runtime.listIsEmpty values)
    (fun () => runtime.optionNone)
    (fun () => runtime.optionSome (runtime.listFirst values))

end Runtime

namespace Assumption

/--
Where an assumption's authority comes from. Every field is required, so a new assumption cannot be
admitted without naming its ECMA-262 clause, the reviewed wording, the differential-oracle scenario
that measures it, and what that scenario covers.
-/
structure Provenance where
  /-- The ECMA-262 clause identifiers the claim rests on. -/
  clauses : List String
  /-- The reviewed English wording of the claim. -/
  statement : String
  /-- The probe group that measures it. -/
  oracle : String
  /-- The coverage families the probe suite has to measure, as identifiers a checker can join on. -/
  coverage : List String
  deriving DecidableEq, Repr

/--
The frozen specification snapshot every clause citation resolves against.

`artifact` is the repository-relative path of the frozen page. Its digest is a property of that file,
so the checker computes it and the artefact owns it: a hash recorded here would be a claim this
library cannot verify.
-/
structure Snapshot where
  url : String
  artifact : String
  /-- The digest of the frozen file as `sha256:<hex>`, declared here and recomputed from the bytes by
  the gate. It is a declared expectation, not an assertion: a mismatch and an absent artefact are
  both refusals. -/
  digest : String
  deriving DecidableEq, Repr

/-- The one snapshot all nine assumptions cite. -/
def source : Snapshot :=
  { url := "https://tc39.es/ecma262/2025/"
    artifact := "spec/semantics/ecma262-2025.html"
    digest := "sha256:c1f9a15946c7dd94b13f56564fa6549cc6f212fd35101f8f5e38a32a0efbefe1" }

/-- A digest of the recorded provenance. Every component is length-prefixed, so two provenance
records that differ anywhere have different digests. -/
def Provenance.canonicalWording (provenance : Provenance) : String :=
  let parts := provenance.clauses ++ [provenance.statement, provenance.oracle] ++ provenance.coverage
  String.intercalate ":" (parts.map fun part => s!"{part.length}:{part}")

/-- The stable identity of one external assumption. -/
inductive Id where
  /-- `&&`, `||` and `!` on JavaScript booleans. -/
  | booleanLogicalOperators
  /-- `===` between two values of the same primitive type. -/
  | strictEqualitySameType
  /-- `+`, `-` and `*` on bigints, at every magnitude. -/
  | bigintExactArithmetic
  /-- `<` and `<=` on bigints. -/
  | bigintRelational
  /-- `? :` selects by ToBoolean, which is what clamps truncated subtraction at zero. -/
  | conditionalTruthySelection
  /-- `+` on two strings concatenates UTF-16 code units. -/
  | stringUtf16Concatenation
  /-- Array forms observe and produce the dense element sequence. -/
  | arrayDenseElementSequence
  /-- `BigInt(value.length)` is the array length as an exact integer. -/
  | bigintFromLength
  /-- The emitted `{ kind, value }` object denotes the tagged image. -/
  | optionTaggedObject
  deriving DecidableEq, Repr

/-- The stable string identity, which catalog rows key on. -/
def Id.name : Id → String
  | .booleanLogicalOperators => "boolean.logical-operators"
  | .strictEqualitySameType => "strict-equality.same-type"
  | .bigintExactArithmetic => "bigint.exact-arithmetic"
  | .bigintRelational => "bigint.relational"
  | .conditionalTruthySelection => "conditional.truthy-selection"
  | .stringUtf16Concatenation => "string.utf16-concatenation"
  | .arrayDenseElementSequence => "array.dense-element-sequence"
  | .bigintFromLength => "bigint.from-length"
  | .optionTaggedObject => "option.tagged-object"

/-- Every assumption this compiler makes. -/
def Id.all : List Id :=
  [.booleanLogicalOperators, .strictEqualitySameType, .bigintExactArithmetic, .bigintRelational,
    .conditionalTruthySelection, .stringUtf16Concatenation, .arrayDenseElementSequence,
    .bigintFromLength, .optionTaggedObject]

theorem Id.mem_all (id : Id) : id ∈ Id.all := by
  cases id <;> simp [Id.all]

/-- Distinct assumptions have distinct stable identities. -/
theorem Id.name_injective {left right : Id} (equal : left.name = right.name) : left = right := by
  cases left <;> cases right <;> simp_all [Id.name]

/-- The recorded authority for one assumption. -/
def Id.provenance : Id → Provenance
  | .booleanLogicalOperators =>
      { clauses := ["sec-binary-logical-operators", "sec-logical-not-operator"]
        statement := "The && operator returns its left operand when ToBoolean of that operand is false and its right operand otherwise. The || operator is the dual. The ! operator returns the negation of ToBoolean of its operand."
        oracle := "semantics-probes/boolean.logical-operators"
        coverage := ["operator-logical-and", "operator-logical-or", "operator-logical-not",
            "short-circuit-evaluation"] }
  | .strictEqualitySameType =>
      { clauses := ["sec-strict-equality-comparison", "sec-equality-operators"]
        statement := "The === operator applied to two values of the same primitive type compares those values and performs no conversion."
        oracle := "semantics-probes/strict-equality.same-type"
        coverage := ["strict-equality-boolean", "strict-equality-bigint", "strict-equality-string",
            "strict-equality-number"] }
  | .bigintExactArithmetic =>
      { clauses := ["sec-numeric-types-bigint-add", "sec-numeric-types-bigint-subtract",
          "sec-numeric-types-bigint-multiply"]
        statement := "The +, - and * operators applied to two bigints are exact integer addition, subtraction and multiplication at every magnitude."
        oracle := "semantics-probes/bigint.exact-arithmetic"
        coverage := ["bigint-add", "bigint-subtract", "bigint-multiply", "bigint-beyond-safe-integer"] }
  | .bigintRelational =>
      { clauses := ["sec-relational-operators", "sec-numeric-types-bigint-lessThan"]
        statement := "The < and <= operators applied to two bigints compare them as exact integers."
        oracle := "semantics-probes/bigint.relational"
        coverage := ["bigint-less-than", "bigint-less-than-or-equal"] }
  | .conditionalTruthySelection =>
      { clauses := ["sec-conditional-operator", "sec-toboolean"]
        statement := "The conditional form applies ToBoolean to its condition and evaluates exactly one branch: the consequent when true and the alternate otherwise, for both JavaScript-value and tagged-Option results."
        oracle := "semantics-probes/conditional.truthy-selection"
        coverage := ["conditional-selection", "conditional-single-branch", "conditional-option-selection"] }
  | .stringUtf16Concatenation =>
      { clauses := ["sec-addition-operator-plus", "sec-ecmascript-language-types-string-type"]
        statement := "The + operator applied to two strings concatenates their UTF-16 code units and converts nothing."
        oracle := "semantics-probes/string.utf16-concatenation"
        coverage := ["string-concatenation", "string-code-unit-length", "string-surrogate-pair"] }
  | .arrayDenseElementSequence =>
      { clauses := ["sec-array-exotic-objects", "sec-array.prototype.map", "sec-array.prototype.filter",
          "sec-array.prototype.reduce", "sec-array.prototype.reduceright",
          "sec-array.prototype.some", "sec-array.prototype.every", "sec-array.prototype.reverse",
          "sec-array.prototype.slice"]
        statement := "An array literal, a spread of an array, and length, indexing, slice, reverse, map, filter, reduce, reduceRight, some and every over it observe and produce exactly the dense element sequence, including the length === 0 comparison the emitted guards perform."
        oracle := "semantics-probes/array.dense-element-sequence"
        coverage := ["array-length", "array-spread", "array-reverse", "array-map", "array-filter",
            "array-reduce", "array-reduce-right", "array-some", "array-every", "array-index",
            "array-slice"] }
  | .bigintFromLength =>
      { clauses := ["sec-bigint-constructor-number-value"]
        statement := "The BigInt constructor applied to an array length yields that length as an exact integer."
        oracle := "semantics-probes/bigint.from-length"
        coverage := ["bigint-from-length"] }
  | .optionTaggedObject =>
      { clauses := ["sec-object-initializer", "sec-property-accessors"]
        statement := "The constructors for { kind: tag } and { kind: tag, value: payload } produce exactly the none and some tagged Option images; property reads of those images are modelled by the target heap semantics."
        oracle := "semantics-probes/option.tagged-object"
        coverage := ["object-literal-own-keys", "object-property-read", "object-absent-property"] }

/-- The recorded digest for one assumption. -/
def Id.canonicalWording (id : Id) : String := id.provenance.canonicalWording

/--
What one assumption claims about the engine, on the values the compiler actually produces.

The claims are stated on encoded operands rather than on arbitrary values, because that is the whole
domain the emitted forms are reached with, and claiming more would be claiming something the oracle
does not measure.
-/
def Id.statement (runtime : Runtime) : Id → Prop
  | .booleanLogicalOperators =>
      (∀ left right : Value, runtime.boolAnd left right = Model.boolAnd left right) ∧
      (∀ left right : Value, runtime.boolOr left right = Model.boolOr left right) ∧
      (∀ operand : Value, runtime.boolNot operand = Model.boolNot operand)
  | .strictEqualitySameType =>
      (∀ left right : Value, runtime.boolEquals left right = Model.strictEquals left right) ∧
      (∀ left right : Value, runtime.natEquals left right = Model.strictEquals left right) ∧
      (∀ left right : Value, runtime.stringEquals left right = Model.strictEquals left right)
  | .bigintExactArithmetic =>
      (∀ left right : Int, runtime.natAdd (Encode.bigint left) (Encode.bigint right)
          = Encode.bigint (left + right)) ∧
      (∀ left right : Int, runtime.natMultiply (Encode.bigint left) (Encode.bigint right)
          = Encode.bigint (left * right)) ∧
      (∀ operand : Int, runtime.natSuccessor (Encode.bigint operand)
          = Encode.bigint (operand + 1)) ∧
      (∀ left right : Int, right ≤ left →
          runtime.natDifference (Encode.bigint left) (Encode.bigint right)
            = Encode.bigint (left - right))
  | .bigintRelational =>
      (∀ left right : Int, runtime.natLess (Encode.bigint left) (Encode.bigint right)
          = Encode.bool (decide (left < right))) ∧
      (∀ left right : Int, runtime.natLessOrEqual (Encode.bigint left) (Encode.bigint right)
          = Encode.bool (decide (left ≤ right)))
  | .conditionalTruthySelection =>
      (∀ (condition : Value) (consequent alternate : Unit → Value),
          runtime.conditionalValue condition consequent alternate
            = if condition.toBoolean then consequent () else alternate ()) ∧
        ∀ (condition : Value) (consequent alternate : Unit → OptionImage),
          runtime.conditionalOption condition consequent alternate
            = if condition.toBoolean then consequent () else alternate ()
  | .stringUtf16Concatenation =>
      ∀ left right : JSString, runtime.stringAppend (Encode.jsString left) (Encode.jsString right)
        = Encode.jsString (JSString.append left right)
  | .arrayDenseElementSequence =>
      (∀ values : List Value, runtime.listIsEmpty values = Encode.bool values.isEmpty) ∧
      (∀ left right : List Value, runtime.listAppend left right = left ++ right) ∧
      (∀ values : List Value, runtime.listReverse values = values.reverse) ∧
      (∀ (transform : Value → Value) (values : List Value),
          runtime.listMap transform values = values.map transform) ∧
      (∀ (keep : Value → Value) (values : List Value),
          runtime.listFilter keep values = values.filter fun value => (keep value).toBoolean) ∧
      (∀ (step : Value → Value → Value) (initial : Value) (values : List Value),
          runtime.listFoldLeft step initial values = values.foldl step initial) ∧
      (∀ (step : Value → Value → Value) (initial : Value) (values : List Value),
          runtime.listFoldRight step initial values = values.foldr step initial) ∧
      (∀ (holds : Value → Value) (values : List Value),
          runtime.listAny holds values
            = Encode.bool (values.any fun value => (holds value).toBoolean)) ∧
      (∀ (holds : Value → Value) (values : List Value),
          runtime.listAll holds values
            = Encode.bool (values.all fun value => (holds value).toBoolean)) ∧
      (∀ (head : Value) (tail : List Value), runtime.listFirst (head :: tail) = head) ∧
      (∀ (head : Value) (tail : List Value), runtime.listRest (head :: tail) = tail)
  | .bigintFromLength =>
      ∀ values : List Value, runtime.listLength values = Encode.nat values.length
  | .optionTaggedObject =>
      runtime.optionNone = .absent ∧
        ∀ value : Value, runtime.optionSome value = .present value

/-- An ordered assumption closure. The order is the order the emitted form depends on them. -/
def Holds (runtime : Runtime) : List Id → Prop
  | [] => True
  | id :: rest => id.statement runtime ∧ Holds runtime rest

/-- A closure holds for every assumption it lists. -/
theorem Holds.mem {runtime : Runtime} {ids : List Id} (holds : Holds runtime ids)
    {id : Id} (member : id ∈ ids) : id.statement runtime := by
  induction ids with
  | nil => exact absurd member (by simp)
  | cons head rest step =>
      rcases List.mem_cons.mp member with rfl | tail
      · exact holds.1
      · exact step holds.2 tail

/-- An empty closure claims nothing. -/
theorem Holds.nil (runtime : Runtime) : Holds runtime [] := trivial

end Assumption

end TSLean.LeanToTypeScript.Semantics
