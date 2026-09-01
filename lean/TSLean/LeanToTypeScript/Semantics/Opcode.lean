import TSLean.Refinement.Primitive
import TSLean.Refinement.String
import TSLean.LeanToTypeScript.Semantics.Assumption
import TSLean.LeanToTypeScript.Semantics.Ir

/-!
# The runtime opcode registry, and its preservation theorems

One row per runtime opcode the exporter spends. `Opcode.kind` is the wire spelling
`src/lean-to-typescript/ir.ts` decodes, `Opcode.requires` is the ordered assumption closure the row's
theorem consumes, and `Opcode.Preserves` is the theorem's statement: the source operation on the left,
the runtime form on the right.

`registry` is a total function on `Opcode`. Adding a constructor without a theorem does not compile, so
an opcode cannot reach the compiler unproved, and the closure cannot be widened or narrowed without
the proof failing.
-/

namespace TSLean.LeanToTypeScript.Semantics

open TSLean.JS

open Ir (Opcode)

namespace Ir.Opcode


/-- The TypeScript form `emitter.ts` emits for the opcode. Recorded so a catalog row can be checked
against the emitter without reading the proof. -/
def emittedForm : Opcode → String
  | .boolAnd => "left && right"
  | .boolOr => "left || right"
  | .boolNot => "!operand"
  | .boolEquals => "left === right"
  | .natAdd => "left + right"
  | .natSubtract => "left < right ? 0n : left - right"
  | .natMultiply => "left * right"
  | .natLess => "left < right"
  | .natLessOrEqual => "left <= right"
  | .natEquals => "left === right"
  | .natSuccessor => "operand + 1n"
  | .stringAppend => "left + right"
  | .stringEquals => "left === right"
  | .listLength => "BigInt(value.length)"
  | .listIsEmpty => "value.length === 0"
  | .listAppend => "[...left, ...right]"
  | .listReverse => "[...value].reverse()"
  | .listMap => "value.map((element) => transform(element))"
  | .listFilter => "value.filter((element) => keep(element))"
  | .listFoldLeft => "value.reduce((accumulator, element) => step(accumulator, element), initial)"
  | .listFoldRight =>
      "value.reduceRight((accumulator, element) => step(element, accumulator), initial)"
  | .listAny => "value.some((element) => holds(element))"
  | .listAll => "value.every((element) => holds(element))"
  | .listHead => "value.length === 0 ? { kind: \"none\" } : { kind: \"some\", value: value[0] }"
  | .listFirst => "value[0]"
  | .listRest => "value.slice(1)"

/-- The theorem that discharges the opcode, by name inside this namespace. `registry` pairs each
opcode with that theorem, so a name recorded here and a clause naming a different theorem is a
mismatch the gate reports. -/
def theoremName : Opcode → String
  | .boolAnd => "boolAndModelsAnd"
  | .boolOr => "boolOrModelsOr"
  | .boolNot => "boolNotModelsNot"
  | .boolEquals => "boolEqualsModelsBEq"
  | .natAdd => "natAddModelsAdd"
  | .natSubtract => "natSubtractModelsSub"
  | .natMultiply => "natMultiplyModelsMul"
  | .natLess => "natLessModelsLt"
  | .natLessOrEqual => "natLessOrEqualModelsLe"
  | .natEquals => "natEqualsModelsBEq"
  | .natSuccessor => "natSuccessorModelsSucc"
  | .stringAppend => "stringAppendModelsAppend"
  | .stringEquals => "stringEqualsModelsBEq"
  | .listLength => "listLengthModelsLength"
  | .listIsEmpty => "listIsEmptyModelsIsEmpty"
  | .listAppend => "listAppendModelsAppend"
  | .listReverse => "listReverseModelsReverse"
  | .listMap => "listMapModelsMap"
  | .listFilter => "listFilterModelsFilter"
  | .listFoldLeft => "listFoldLeftModelsFoldl"
  | .listFoldRight => "listFoldRightModelsFoldr"
  | .listAny => "listAnyModelsAny"
  | .listAll => "listAllModelsAll"
  | .listHead => "listHeadModelsHead"
  | .listFirst => "listFirstModelsHead"
  | .listRest => "listRestModelsTail"

/-- The fully named model constant the opcode's theorem constrains. Most are primitive Runtime
fields; generated helpers such as natSubtract and listHead are derived Runtime definitions. -/
def modelField : Opcode → String
  | .boolAnd => "boolAnd"
  | .boolOr => "boolOr"
  | .boolNot => "boolNot"
  | .boolEquals => "boolEquals"
  | .natAdd => "natAdd"
  | .natSubtract => "natSubtract"
  | .natMultiply => "natMultiply"
  | .natLess => "natLess"
  | .natLessOrEqual => "natLessOrEqual"
  | .natEquals => "natEquals"
  | .natSuccessor => "natSuccessor"
  | .stringAppend => "stringAppend"
  | .stringEquals => "stringEquals"
  | .listLength => "listLength"
  | .listIsEmpty => "listIsEmpty"
  | .listAppend => "listAppend"
  | .listReverse => "listReverse"
  | .listMap => "listMap"
  | .listFilter => "listFilter"
  | .listFoldLeft => "listFoldLeft"
  | .listFoldRight => "listFoldRight"
  | .listAny => "listAny"
  | .listAll => "listAll"
  | .listHead => "listHead"
  | .listFirst => "listFirst"
  | .listRest => "listRest"

/-- The operator, method or generated-helper role the emitted form is built from, distinct from the
exact TypeScript `emittedForm` records. -/
def runtimeSymbol : Opcode → String
  | .boolAnd => "&&"
  | .boolOr => "||"
  | .boolNot => "!"
  | .boolEquals => "==="
  | .natAdd => "+"
  | .natSubtract => "helper:nat-truncated-subtraction"
  | .natMultiply => "*"
  | .natLess => "<"
  | .natLessOrEqual => "<="
  | .natEquals => "==="
  | .natSuccessor => "+"
  | .stringAppend => "+"
  | .stringEquals => "==="
  | .listLength => "BigInt"
  | .listIsEmpty => "length"
  | .listAppend => "spread"
  | .listReverse => "reverse"
  | .listMap => "map"
  | .listFilter => "filter"
  | .listFoldLeft => "reduce"
  | .listFoldRight => "reduceRight"
  | .listAny => "some"
  | .listAll => "every"
  | .listHead => "helper:list-head-option"
  | .listFirst => "index"
  | .listRest => "slice"

/-- The closed semantic components a generated helper reaches, in evaluation order. These are not
runtime symbols and not assumption ids: Coverage binds helper bytes separately, while these names
let the registry certify the helper's semantic composition. Ordinary one-form opcodes have none. -/
def components : Opcode → List String
  | .natSubtract => ["inline:nat.less", "conditional:select", "primitive:bigint.subtract"]
  | .listHead => ["inline:list.isEmpty", "inline:list.first", "conditional:select",
      "representation:option.tagged-option"]
  | _ => []

/-- The ordered assumption closure the opcode's theorem consumes. -/
def requires : Opcode → List Assumption.Id
  | .boolAnd | .boolOr | .boolNot => [.booleanLogicalOperators]
  | .boolEquals | .natEquals | .stringEquals => [.strictEqualitySameType]
  | .natAdd | .natMultiply | .natSuccessor => [.bigintExactArithmetic]
  | .natSubtract => [.bigintRelational, .conditionalTruthySelection, .bigintExactArithmetic]
  | .natLess | .natLessOrEqual => [.bigintRelational]
  | .stringAppend => [.stringUtf16Concatenation]
  | .listLength => [.bigintFromLength]
  | .listHead => [.arrayDenseElementSequence, .conditionalTruthySelection, .optionTaggedObject]
  | .listIsEmpty | .listAppend | .listReverse | .listMap | .listFilter | .listFoldLeft
  | .listFoldRight | .listAny | .listAll | .listFirst | .listRest =>
      [.arrayDenseElementSequence]

/--
What the opcode's theorem states. The left side is the source operation, encoded; the right side is
the runtime form applied to encoded operands.

A list opcode is polymorphic in its element type, so its statement takes the element encoder and, for
a higher-order opcode, the correspondence between the emitted callback and the Lean function it
stands for. That correspondence is a hypothesis rather than an assumption: it is discharged by the
caller's own preservation, not by the engine.
-/
def Preserves (runtime : Runtime) : Opcode → Prop
  | .boolAnd => ∀ left right : Bool,
      Encode.bool (left && right) = runtime.boolAnd (Encode.bool left) (Encode.bool right)
  | .boolOr => ∀ left right : Bool,
      Encode.bool (left || right) = runtime.boolOr (Encode.bool left) (Encode.bool right)
  | .boolNot => ∀ operand : Bool,
      Encode.bool (!operand) = runtime.boolNot (Encode.bool operand)
  | .boolEquals => ∀ left right : Bool,
      Encode.bool (left == right) = runtime.boolEquals (Encode.bool left) (Encode.bool right)
  | .natAdd => ∀ left right : Nat,
      Encode.nat (left + right) = runtime.natAdd (Encode.nat left) (Encode.nat right)
  | .natSubtract => ∀ left right : Nat,
      Encode.nat (left - right) = runtime.natSubtract (Encode.nat left) (Encode.nat right)
  | .natMultiply => ∀ left right : Nat,
      Encode.nat (left * right) = runtime.natMultiply (Encode.nat left) (Encode.nat right)
  | .natLess => ∀ left right : Nat,
      Encode.bool (decide (left < right)) = runtime.natLess (Encode.nat left) (Encode.nat right)
  | .natLessOrEqual => ∀ left right : Nat,
      Encode.bool (decide (left ≤ right))
        = runtime.natLessOrEqual (Encode.nat left) (Encode.nat right)
  | .natEquals => ∀ left right : Nat,
      Encode.bool (left == right) = runtime.natEquals (Encode.nat left) (Encode.nat right)
  | .natSuccessor => ∀ operand : Nat,
      Encode.nat (operand + 1) = runtime.natSuccessor (Encode.nat operand)
  | .stringAppend => ∀ left right : String,
      Encode.string (left ++ right)
        = runtime.stringAppend (Encode.string left) (Encode.string right)
  | .stringEquals => ∀ left right : String,
      Encode.bool (left == right)
        = runtime.stringEquals (Encode.string left) (Encode.string right)
  | .listLength => ∀ {α : Type} (encode : α → Value) (values : List α),
      Encode.nat values.length = runtime.listLength (values.map encode)
  | .listIsEmpty => ∀ {α : Type} (encode : α → Value) (values : List α),
      Encode.bool values.isEmpty = runtime.listIsEmpty (values.map encode)
  | .listAppend => ∀ {α : Type} (encode : α → Value) (left right : List α),
      (left ++ right).map encode = runtime.listAppend (left.map encode) (right.map encode)
  | .listReverse => ∀ {α : Type} (encode : α → Value) (values : List α),
      values.reverse.map encode = runtime.listReverse (values.map encode)
  | .listMap => ∀ {α β : Type} (source : α → Value) (image : β → Value)
      (transform : Value → Value) (function : α → β),
      (∀ value, transform (source value) = image (function value)) →
      ∀ values : List α,
        (values.map function).map image = runtime.listMap transform (values.map source)
  | .listFilter => ∀ {α : Type} (encode : α → Value) (keep : Value → Value) (decision : α → Bool),
      (∀ value, (keep (encode value)).toBoolean = decision value) →
      ∀ values : List α,
        (values.filter decision).map encode = runtime.listFilter keep (values.map encode)
  | .listFoldLeft => ∀ {α β : Type} (element : α → Value) (state : β → Value)
      (step : Value → Value → Value) (function : β → α → β),
      (∀ accumulator value,
        step (state accumulator) (element value) = state (function accumulator value)) →
      ∀ (initial : β) (values : List α),
        state (values.foldl function initial)
          = runtime.listFoldLeft step (state initial) (values.map element)
  | .listFoldRight => ∀ {α β : Type} (element : α → Value) (state : β → Value)
      (step : Value → Value → Value) (function : α → β → β),
      (∀ value accumulator,
        step (element value) (state accumulator) = state (function value accumulator)) →
      ∀ (initial : β) (values : List α),
        state (values.foldr function initial)
          = runtime.listFoldRight step (state initial) (values.map element)
  | .listAny => ∀ {α : Type} (encode : α → Value) (holds : Value → Value) (decision : α → Bool),
      (∀ value, (holds (encode value)).toBoolean = decision value) →
      ∀ values : List α,
        Encode.bool (values.any decision) = runtime.listAny holds (values.map encode)
  | .listAll => ∀ {α : Type} (encode : α → Value) (holds : Value → Value) (decision : α → Bool),
      (∀ value, (holds (encode value)).toBoolean = decision value) →
      ∀ values : List α,
        Encode.bool (values.all decision) = runtime.listAll holds (values.map encode)
  | .listHead => ∀ {α : Type} (encode : α → Value) (values : List α),
      Encode.option (values.head?.map encode) = runtime.listHead (values.map encode)
  | .listFirst => ∀ {α : Type} (encode : α → Value) (head : α) (tail : List α),
      encode head = runtime.listFirst ((head :: tail).map encode)
  | .listRest => ∀ {α : Type} (encode : α → Value) (head : α) (tail : List α),
      tail.map encode = runtime.listRest ((head :: tail).map encode)

/-- The obligation one opcode carries: its ordered assumption closure entails its statement. -/
def Obligation (runtime : Runtime) (code : Opcode) : Prop :=
  Assumption.Holds runtime code.requires → code.Preserves runtime

end Ir.Opcode

namespace Opcode

/-! ## The theorems -/

/-- `&&` on two JavaScript booleans denotes `Bool.and`, including its laziness in the right
operand: ECMAScript returns the left operand unevaluated-further when it is falsy, and `Bool.and`
returns `false` there. -/
theorem boolAndModelsAnd (runtime : Runtime)
    (holds : Assumption.Holds runtime Opcode.boolAnd.requires) :
    Opcode.boolAnd.Preserves runtime := by
  intro left right
  rw [holds.1.1 (Encode.bool left) (Encode.bool right)]
  cases left <;> simp [Encode.bool, Model.boolAnd, Value.toBoolean, Primitive.toBoolean]

/-- `||` on two JavaScript booleans denotes `Bool.or`. -/
theorem boolOrModelsOr (runtime : Runtime)
    (holds : Assumption.Holds runtime Opcode.boolOr.requires) :
    Opcode.boolOr.Preserves runtime := by
  intro left right
  rw [holds.1.2.1 (Encode.bool left) (Encode.bool right)]
  cases left <;> simp [Encode.bool, Model.boolOr, Value.toBoolean, Primitive.toBoolean]

/-- `!` on a JavaScript boolean denotes `Bool.not`. -/
theorem boolNotModelsNot (runtime : Runtime)
    (holds : Assumption.Holds runtime Opcode.boolNot.requires) :
    Opcode.boolNot.Preserves runtime := by
  intro operand
  rw [holds.1.2.2 (Encode.bool operand)]
  cases operand <;> simp [Encode.bool, Model.boolNot, Value.toBoolean, Primitive.toBoolean]

/-- `===` on two JavaScript booleans denotes Lean `Bool` equality. -/
theorem boolEqualsModelsBEq (runtime : Runtime)
    (holds : Assumption.Holds runtime Opcode.boolEquals.requires) :
    Opcode.boolEquals.Preserves runtime := by
  intro left right
  rw [holds.1.1 (Encode.bool left) (Encode.bool right)]
  unfold Model.strictEquals Encode.bool
  rw [TSLean.Refinement.Bool.strictEqual_commutes left right]

/-- The embedding of `Nat` into the integers is injective, so bigint identity decides `Nat`
identity. -/
private theorem beq_ofNat (left right : Nat) :
    (((left : Int)) == ((right : Int))) = (left == right) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  exact ⟨Int.ofNat.inj, congrArg Int.ofNat⟩

/-- `+` on two bigints denotes `Nat.add`, because the embedding of `Nat` in the integers is
additive. -/
theorem natAddModelsAdd (runtime : Runtime)
    (holds : Assumption.Holds runtime Opcode.natAdd.requires) :
    Opcode.natAdd.Preserves runtime := by
  intro left right
  unfold Encode.nat
  rw [holds.1.1 (left : Int) (right : Int)]
  congr 1
  all_goals omega

/-- The truncated-subtraction helper denotes `Nat.sub`. Above the diagonal the bigint difference is
the answer; below it the conditional yields zero, which is exactly where `Nat.sub` truncates. -/
theorem natSubtractModelsSub (runtime : Runtime)
    (holds : Assumption.Holds runtime Opcode.natSubtract.requires) :
    Opcode.natSubtract.Preserves runtime := by
  intro left right
  rcases holds with ⟨relational, conditional, arithmetic⟩
  have difference : ∀ left right : Int, right ≤ left →
      runtime.natDifference (Encode.bigint left) (Encode.bigint right)
        = Encode.bigint (left - right) := arithmetic.1.2.2.2
  by_cases below : right ≤ left
  · have notLess : ¬((left : Int) < (right : Int)) := by omega
    have condition :
        (runtime.natLess (Encode.bigint (left : Int)) (Encode.bigint (right : Int))).toBoolean
          = false := by
      rw [relational.1 (left : Int) (right : Int)]
      simp [Encode.bool, Value.toBoolean, Primitive.toBoolean, notLess]
    have notCondition :
        ¬((runtime.natLess (Encode.bigint (left : Int)) (Encode.bigint (right : Int))).toBoolean
          = true) := by
      rw [condition]
      simp
    unfold Encode.nat Runtime.natSubtract
    rw [conditional.1 _ _ _, if_neg notCondition,
      difference (left : Int) (right : Int) (by omega)]
    rw [show ((left - right : Nat) : Int) = (left : Int) - (right : Int) by omega]
  · have less : (left : Int) < (right : Int) := by omega
    have condition :
        (runtime.natLess (Encode.bigint (left : Int)) (Encode.bigint (right : Int))).toBoolean
          = true := by
      rw [relational.1 (left : Int) (right : Int)]
      simp [Encode.bool, Value.toBoolean, Primitive.toBoolean, less]
    unfold Encode.nat Runtime.natSubtract
    rw [conditional.1 _ _ _, if_pos condition]
    have truncated : left - right = 0 := by omega
    simp [Encode.nat, truncated]

/-- `*` on two bigints denotes `Nat.mul`. -/
theorem natMultiplyModelsMul (runtime : Runtime)
    (holds : Assumption.Holds runtime Opcode.natMultiply.requires) :
    Opcode.natMultiply.Preserves runtime := by
  intro left right
  unfold Encode.nat
  rw [holds.1.2.1 (left : Int) (right : Int)]
  congr 1
  all_goals exact Int.ofNat_mul left right

/-- `<` on two bigints denotes `Nat.lt`. -/
theorem natLessModelsLt (runtime : Runtime)
    (holds : Assumption.Holds runtime Opcode.natLess.requires) :
    Opcode.natLess.Preserves runtime := by
  intro left right
  unfold Encode.nat
  rw [holds.1.1 (left : Int) (right : Int)]
  congr 1
  all_goals exact decide_eq_decide.mpr Int.ofNat_lt.symm

/-- `<=` on two bigints denotes `Nat.le`. -/
theorem natLessOrEqualModelsLe (runtime : Runtime)
    (holds : Assumption.Holds runtime Opcode.natLessOrEqual.requires) :
    Opcode.natLessOrEqual.Preserves runtime := by
  intro left right
  unfold Encode.nat
  rw [holds.1.2 (left : Int) (right : Int)]
  congr 1
  all_goals exact decide_eq_decide.mpr Int.ofNat_le.symm

/-- `===` on two bigints denotes `Nat` equality, because the embedding is injective. -/
theorem natEqualsModelsBEq (runtime : Runtime)
    (holds : Assumption.Holds runtime Opcode.natEquals.requires) :
    Opcode.natEquals.Preserves runtime := by
  intro left right
  rw [holds.1.2.1 (Encode.nat left) (Encode.nat right)]
  unfold Model.strictEquals Encode.nat Encode.bigint
  rw [TSLean.Refinement.BigInt.strictEqual_commutes (left : Int) (right : Int),
    beq_ofNat left right]

/-- `operand + 1n` denotes `Nat.succ`. -/
theorem natSuccessorModelsSucc (runtime : Runtime)
    (holds : Assumption.Holds runtime Opcode.natSuccessor.requires) :
    Opcode.natSuccessor.Preserves runtime := by
  intro operand
  unfold Encode.nat
  rw [holds.1.2.2.1 (operand : Int)]
  congr 1
  all_goals omega

/-- `+` on two strings denotes `String.append`, at the level of UTF-16 code units. -/
theorem stringAppendModelsAppend (runtime : Runtime)
    (holds : Assumption.Holds runtime Opcode.stringAppend.requires) :
    Opcode.stringAppend.Preserves runtime := by
  intro left right
  unfold Encode.string
  rw [holds.1 (JSString.ofLeanString left) (JSString.ofLeanString right),
    JSString.ofLeanString_append]

/-- `===` on two strings denotes Lean `String` equality, because the UTF-16 encoding is
injective. -/
theorem stringEqualsModelsBEq (runtime : Runtime)
    (holds : Assumption.Holds runtime Opcode.stringEquals.requires) :
    Opcode.stringEquals.Preserves runtime := by
  intro left right
  rw [holds.1.2.2 (Encode.string left) (Encode.string right)]
  unfold Model.strictEquals Encode.string Encode.jsString
  rw [TSLean.Refinement.String.strictEqual_commutes left right]

/-- `BigInt(value.length)` denotes `List.length`, because encoding the elements does not change how
many there are. -/
theorem listLengthModelsLength (runtime : Runtime)
    (holds : Assumption.Holds runtime Opcode.listLength.requires) :
    Opcode.listLength.Preserves runtime := by
  intro α encode values
  rw [holds.1 (values.map encode), List.length_map]

/-- `value.length === 0` denotes `List.isEmpty`. -/
theorem listIsEmptyModelsIsEmpty (runtime : Runtime)
    (holds : Assumption.Holds runtime Opcode.listIsEmpty.requires) :
    Opcode.listIsEmpty.Preserves runtime := by
  intro α encode values
  rw [holds.1.1 (values.map encode)]
  cases values <;> simp

/-- `[...left, ...right]` denotes `List.append`. -/
theorem listAppendModelsAppend (runtime : Runtime)
    (holds : Assumption.Holds runtime Opcode.listAppend.requires) :
    Opcode.listAppend.Preserves runtime := by
  intro α encode left right
  rw [holds.1.2.1 (left.map encode) (right.map encode), List.map_append]

/-- `[...value].reverse()` denotes `List.reverse`. -/
theorem listReverseModelsReverse (runtime : Runtime)
    (holds : Assumption.Holds runtime Opcode.listReverse.requires) :
    Opcode.listReverse.Preserves runtime := by
  intro α encode values
  rw [holds.1.2.2.1 (values.map encode), List.map_reverse]

/-- `value.map(callback)` denotes `List.map`, given that the callback denotes the function. -/
theorem listMapModelsMap (runtime : Runtime)
    (holds : Assumption.Holds runtime Opcode.listMap.requires) :
    Opcode.listMap.Preserves runtime := by
  intro α β source image transform function callback values
  rw [holds.1.2.2.2.1 transform (values.map source), List.map_map, List.map_map]
  exact List.map_congr_left fun value _ => (callback value).symm

/-- `value.filter(callback)` denotes `List.filter`, given that the callback's truthiness denotes the
decision. -/
theorem listFilterModelsFilter (runtime : Runtime)
    (holds : Assumption.Holds runtime Opcode.listFilter.requires) :
    Opcode.listFilter.Preserves runtime := by
  intro α encode keep decision callback values
  rw [holds.1.2.2.2.2.1 keep (values.map encode)]
  induction values with
  | nil => rfl
  | cons head tail step =>
      by_cases decided : decision head
      · simp [decided, callback head, step]
      · simp [decided, callback head, step]

/-- `value.reduce(callback, initial)` denotes `List.foldl`, given that the callback denotes the
step. -/
theorem listFoldLeftModelsFoldl (runtime : Runtime)
    (holds : Assumption.Holds runtime Opcode.listFoldLeft.requires) :
    Opcode.listFoldLeft.Preserves runtime := by
  intro α β element state step function callback initial values
  rw [holds.1.2.2.2.2.2.1 step (state initial) (values.map element)]
  induction values generalizing initial with
  | nil => rfl
  | cons head tail inductive_step =>
      simp only [List.map_cons, List.foldl_cons, callback initial head]
      exact inductive_step (function initial head)

/-- `value.reduceRight(callback, initial)` denotes `List.foldr`, given that the callback denotes the
step. The emitted callback takes the accumulator first and applies the step to the element first,
which is exactly the argument order `List.foldr` uses. -/
theorem listFoldRightModelsFoldr (runtime : Runtime)
    (holds : Assumption.Holds runtime Opcode.listFoldRight.requires) :
    Opcode.listFoldRight.Preserves runtime := by
  intro α β element state step function callback initial values
  rw [holds.1.2.2.2.2.2.2.1 step (state initial) (values.map element)]
  induction values with
  | nil => rfl
  | cons head tail inductive_step =>
      simp only [List.map_cons, List.foldr_cons, ← inductive_step]
      exact (callback head (tail.foldr function initial)).symm

/-- `value.some(callback)` denotes `List.any`. -/
theorem listAnyModelsAny (runtime : Runtime)
    (holds : Assumption.Holds runtime Opcode.listAny.requires) :
    Opcode.listAny.Preserves runtime := by
  intro α encode holdsCallback decision callback values
  rw [holds.1.2.2.2.2.2.2.2.1 holdsCallback (values.map encode)]
  induction values with
  | nil => rfl
  | cons head tail step =>
      simp only [List.map_cons, List.any_cons, callback head]
      simp only [Encode.bool] at step ⊢
      injection step with primitiveEqual
      injection primitiveEqual with booleanEqual
      rw [booleanEqual]

/-- `value.every(callback)` denotes `List.all`. -/
theorem listAllModelsAll (runtime : Runtime)
    (holds : Assumption.Holds runtime Opcode.listAll.requires) :
    Opcode.listAll.Preserves runtime := by
  intro α encode holdsCallback decision callback values
  rw [holds.1.2.2.2.2.2.2.2.2.1 holdsCallback (values.map encode)]
  induction values with
  | nil => rfl
  | cons head tail step =>
      simp only [List.map_cons, List.all_cons, callback head]
      simp only [Encode.bool] at step ⊢
      injection step with primitiveEqual
      injection primitiveEqual with booleanEqual
      rw [booleanEqual]

/-- The head helper denotes `List.head?`. -/
theorem listHeadModelsHead (runtime : Runtime)
    (holds : Assumption.Holds runtime Opcode.listHead.requires) :
    Opcode.listHead.Preserves runtime := by
  intro α encode values
  rcases holds with ⟨array, conditional, option⟩
  have optionNone : runtime.optionNone = OptionImage.absent := option.1.1
  have optionSome : ∀ value : Value, runtime.optionSome value = OptionImage.present value :=
    option.1.2
  cases values with
  | nil =>
      have empty : (runtime.listIsEmpty ([] : List Value)).toBoolean = true := by
        rw [array.1 []]
        simp [Encode.bool, Value.toBoolean, Primitive.toBoolean]
      unfold Runtime.listHead
      simp only [List.map_nil]
      rw [conditional.2 _ _ _, if_pos empty]
      exact optionNone.symm
  | cons head tail =>
      have nonEmpty :
          (runtime.listIsEmpty (encode head :: List.map encode tail)).toBoolean = false := by
        rw [array.1 (encode head :: List.map encode tail)]
        simp [Encode.bool, Value.toBoolean, Primitive.toBoolean]
      have notEmpty :
          ¬((runtime.listIsEmpty (encode head :: List.map encode tail)).toBoolean = true) := by
        rw [nonEmpty]
        simp
      unfold Runtime.listHead
      simp only [List.map_cons]
      rw [conditional.2 _ _ _, if_neg notEmpty,
        array.2.2.2.2.2.2.2.2.2.1 (encode head) (List.map encode tail)]
      exact (optionSome (encode head)).symm

/-- `value[0]` under a nonempty guard denotes the head of a cons. -/
theorem listFirstModelsHead (runtime : Runtime)
    (holds : Assumption.Holds runtime Opcode.listFirst.requires) :
    Opcode.listFirst.Preserves runtime := by
  intro α encode head tail
  rw [List.map_cons, holds.1.2.2.2.2.2.2.2.2.2.1 (encode head) (List.map encode tail)]

/-- `value.slice(1)` under a nonempty guard denotes the tail of a cons. -/
theorem listRestModelsTail (runtime : Runtime)
    (holds : Assumption.Holds runtime Opcode.listRest.requires) :
    Opcode.listRest.Preserves runtime := by
  intro α encode head tail
  rw [List.map_cons, holds.1.2.2.2.2.2.2.2.2.2.2 (encode head) (List.map encode tail)]

/--
The closure over the opcode registry. It is a total function on `Opcode`, so an opcode with no theorem
is a build failure rather than an unproved row, and a theorem whose assumption closure differs from
the row's `requires` does not typecheck here.
-/
theorem registry (runtime : Runtime) : (code : Opcode) → code.Obligation runtime
  | .boolAnd => boolAndModelsAnd runtime
  | .boolOr => boolOrModelsOr runtime
  | .boolNot => boolNotModelsNot runtime
  | .boolEquals => boolEqualsModelsBEq runtime
  | .natAdd => natAddModelsAdd runtime
  | .natSubtract => natSubtractModelsSub runtime
  | .natMultiply => natMultiplyModelsMul runtime
  | .natLess => natLessModelsLt runtime
  | .natLessOrEqual => natLessOrEqualModelsLe runtime
  | .natEquals => natEqualsModelsBEq runtime
  | .natSuccessor => natSuccessorModelsSucc runtime
  | .stringAppend => stringAppendModelsAppend runtime
  | .stringEquals => stringEqualsModelsBEq runtime
  | .listLength => listLengthModelsLength runtime
  | .listIsEmpty => listIsEmptyModelsIsEmpty runtime
  | .listAppend => listAppendModelsAppend runtime
  | .listReverse => listReverseModelsReverse runtime
  | .listMap => listMapModelsMap runtime
  | .listFilter => listFilterModelsFilter runtime
  | .listFoldLeft => listFoldLeftModelsFoldl runtime
  | .listFoldRight => listFoldRightModelsFoldr runtime
  | .listAny => listAnyModelsAny runtime
  | .listAll => listAllModelsAll runtime
  | .listHead => listHeadModelsHead runtime
  | .listFirst => listFirstModelsHead runtime
  | .listRest => listRestModelsTail runtime

/-- Every admitted opcode is discharged from its own recorded assumption closure. -/
theorem registry_total (runtime : Runtime) (code : Opcode)
    (holds : Assumption.Holds runtime code.requires) : code.Preserves runtime :=
  registry runtime code holds

end Opcode

end TSLean.LeanToTypeScript.Semantics
