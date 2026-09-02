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


/-- The TypeScript form `emitter.ts` emits for the opcode, byte for byte over the operand names the
row is written in. `inlineOperationForms` in `emitter.ts` prints what that emitter builds for every
inline opcode and the semantics gate compares the two strings exactly, so a form recorded here that
the emitter does not print is a refusal rather than prose. -/
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
  | .listMap => "value.map(element => transform(element))"
  | .listFilter => "value.filter(element => keep(element))"
  | .listFoldLeft => "value.reduce((accumulator, element) => step(accumulator, element), initial)"
  | .listFoldRight =>
      "value.reduceRight((accumulator, element) => step(element, accumulator), initial)"
  | .listAny => "value.some(element => holds(element))"
  | .listAll => "value.every(element => holds(element))"
  | .listHead => "value.length === 0 ? { kind: \"none\" } : { kind: \"some\", value: value[0] }"
  | .listFirst => "value[0]"
  | .listRest => "value.slice(1)"
  | .intAdd => "left + right"
  | .intSubtract => "left - right"
  | .intMultiply => "left * right"
  | .intNegate => "-operand"
  | .intTruncatedDivide => "right === 0n ? 0n : left / right"
  | .intTruncatedModulo => "right === 0n ? left : left % right"
  | .intLess => "left < right"
  | .intLessOrEqual => "left <= right"
  | .intEquals => "left === right"
  | .intOfNat => "operand"
  | .intToNat => "operand < 0n ? 0n : operand"
  | .charToNat => "BigInt(operand.codePointAt(0) ?? 0)"
  | .charOfNat =>
      "operand >= 0n && operand <= 1114111n && !(operand >= 55296n && operand <= 57343n) ? String.fromCodePoint(Number(operand)) : \"\\0\""
  | .charEquals => "left === right"
  | .charLess => "(left.codePointAt(0) ?? 0) < (right.codePointAt(0) ?? 0)"
  | .stringLength => "BigInt([...value].length)"
  | .stringIsEmpty => "value.length === 0"
  | .stringPush => "value + character"
  | .stringSingleton => "character"
  | .stringToList => "[...value]"
  | .stringOfList => "value.join(\"\")"
  | .arraySize => "BigInt(value.length)"
  | .arrayIsEmpty => "value.length === 0"
  | .arrayPush => "[...value, element]"
  | .arrayAppend => "[...left, ...right]"
  | .arrayReverse => "[...value].reverse()"
  | .arrayToList => "value"
  | .arrayOfList => "value"

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
  | .intAdd => "intAddModelsAdd"
  | .intSubtract => "intSubtractModelsSub"
  | .intMultiply => "intMultiplyModelsMul"
  | .intNegate => "intNegateModelsNeg"
  | .intTruncatedDivide => "intTruncatedDivideModelsTdiv"
  | .intTruncatedModulo => "intTruncatedModuloModelsTmod"
  | .intLess => "intLessModelsLt"
  | .intLessOrEqual => "intLessOrEqualModelsLe"
  | .intEquals => "intEqualsModelsBEq"
  | .intOfNat => "intOfNatModelsOfNat"
  | .intToNat => "intToNatModelsToNat"
  | .charToNat => "charToNatModelsToNat"
  | .charOfNat => "charOfNatModelsOfNat"
  | .charEquals => "charEqualsModelsBEq"
  | .charLess => "charLessModelsLt"
  | .stringLength => "stringLengthModelsLength"
  | .stringIsEmpty => "stringIsEmptyModelsIsEmpty"
  | .stringPush => "stringPushModelsPush"
  | .stringSingleton => "stringSingletonModelsSingleton"
  | .stringToList => "stringToListModelsToList"
  | .stringOfList => "stringOfListModelsOfList"
  | .arraySize => "arraySizeModelsSize"
  | .arrayIsEmpty => "arrayIsEmptyModelsIsEmpty"
  | .arrayPush => "arrayPushModelsPush"
  | .arrayAppend => "arrayAppendModelsAppend"
  | .arrayReverse => "arrayReverseModelsReverse"
  | .arrayToList => "arrayToListModelsToList"
  | .arrayOfList => "arrayOfListModelsOfList"

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
  | .intAdd => "natAdd"
  | .intSubtract => "natDifference"
  | .intMultiply => "natMultiply"
  | .intNegate => "intNegate"
  | .intTruncatedDivide => "intTruncatedDivide"
  | .intTruncatedModulo => "intTruncatedModulo"
  | .intLess => "natLess"
  | .intLessOrEqual => "natLessOrEqual"
  | .intEquals => "natEquals"
  | .intOfNat => "intOfNat"
  | .intToNat => "intToNat"
  | .charToNat => "charToNat"
  | .charOfNat => "charOfNat"
  | .charEquals => "stringEquals"
  | .charLess => "charLess"
  | .stringLength => "stringLength"
  | .stringIsEmpty => "stringIsEmpty"
  | .stringPush => "stringPush"
  | .stringSingleton => "stringSingleton"
  | .stringToList => "stringToList"
  | .stringOfList => "stringOfList"
  | .arraySize => "listLength"
  | .arrayIsEmpty => "listIsEmpty"
  | .arrayPush => "listPush"
  | .arrayAppend => "listAppend"
  | .arrayReverse => "listReverse"
  | .arrayToList => "arrayToList"
  | .arrayOfList => "arrayOfList"

/--
The emitted role the opcode's form is built from, tagged by how it reaches the target.

`inline:<opcode>` is a form the emitter writes at the use site, and names the opcode it is the form
of; `helper:<role>` is a generated helper the emitter declares once and calls, and names the role
that helper fills. The tag is what lets a catalog row be joined against the emitted bytes without
reading the proof: a `helper:` row has a helper to bind and `components` to certify, and an
`inline:` row has neither. `LeanRuntimeSymbol` in `src/lean-to-typescript/ir.ts` is the same two
spellings, so the two sides join on this field exactly.

It is distinct from `emittedForm`, which records the exact TypeScript, and from `modelField`, which
names the `Runtime` constant.
-/
def runtimeSymbol : Opcode → String
  | .natSubtract => "helper:nat-truncated-subtraction"
  | .listHead => "helper:list-head-option"
  | .intTruncatedDivide => "helper:int-truncated-division"
  | .intTruncatedModulo => "helper:int-truncated-modulo"
  | .intToNat => "helper:int-to-nat-clamp"
  | .charOfNat => "helper:char-of-nat"
  | .charLess => "helper:char-less-code-point"
  | code => "inline:" ++ code.kind

/-- The tag every runtime symbol carries: `inline:` for a form written at the use site, `helper:`
for a generated helper the emitter declares. -/
def runtimeSymbolTag : Opcode → String
  | code => if (code.runtimeSymbol).startsWith "helper:" then "helper:" else "inline:"

/-- The closed semantic components a generated helper reaches, in evaluation order. These are not
runtime symbols and not assumption ids: Coverage binds helper bytes separately, while these names
let the registry certify the helper's semantic composition. Ordinary one-form opcodes have none. -/
def components : Opcode → List String
  | .natSubtract => ["inline:nat.less", "conditional:select", "primitive:bigint.subtract"]
  | .listHead => ["inline:list.isEmpty", "inline:list.first", "conditional:select",
      "representation:option.tagged-option"]
  | .intTruncatedDivide => ["inline:int.equals", "conditional:select", "primitive:bigint.divide"]
  | .intTruncatedModulo => ["inline:int.equals", "conditional:select",
      "primitive:bigint.remainder"]
  | .intToNat => ["inline:int.less", "conditional:select",
      "representation:nat.nonnegative-bigint"]
  | .charOfNat => ["inline:int.lessOrEqual", "inline:int.less", "conditional:select",
      "primitive:string.fromCodePoint", "representation:char.scalar-value"]
  | .charLess => ["inline:char.toNat", "inline:int.less"]
  | .intOfNat => ["representation:bigint.shared-nat-int"]
  | .stringLength => ["inline:string.toList", "inline:list.length"]
  | .stringPush => ["inline:string.append", "representation:char.one-code-point-string"]
  | .stringSingleton => ["representation:char.one-code-point-string"]
  | .arrayToList | .arrayOfList => ["representation:array.shared-dense-image"]
  | _ => []

/--
Whether the row's model constant is a derived `Runtime` definition rather than a primitive field.

A derived constant is composed out of other rows, so the registry records that composition in
`components`; a primitive field is one engine operation and composes nothing. This is orthogonal to
`runtimeSymbolTag`, which records how the *bytes* reach the target: `string.length` composes two
rows and still reaches the target as one inline expression, while `char.ofNat` composes rows and
reaches it as a declared helper.
-/
def derived : Opcode → Bool
  | .natSubtract | .listHead | .intTruncatedDivide | .intTruncatedModulo | .intToNat | .intOfNat
  | .charOfNat | .charLess | .stringLength | .stringPush | .stringSingleton
  | .arrayToList | .arrayOfList => true
  | .boolAnd | .boolOr | .boolNot | .boolEquals | .natAdd | .natMultiply | .natLess
  | .natLessOrEqual | .natEquals | .natSuccessor | .stringAppend | .stringEquals | .listLength
  | .listIsEmpty | .listAppend | .listReverse | .listMap | .listFilter | .listFoldLeft
  | .listFoldRight | .listAny | .listAll | .listFirst | .listRest | .intAdd | .intSubtract
  | .intMultiply | .intNegate | .intLess | .intLessOrEqual | .intEquals | .charToNat | .charEquals
  | .stringIsEmpty | .stringToList | .stringOfList | .arraySize | .arrayIsEmpty
  | .arrayPush | .arrayAppend | .arrayReverse => false

/-- Exactly the opcodes whose model constant is derived record the semantic components it composes;
a primitive field has none, because there is nothing to certify. -/
theorem components_iff_derived (code : Opcode) :
    code.components ≠ [] ↔ code.derived = true := by
  cases code <;> simp [components, derived]

/-- Every generated helper has a derived model constant: a helper exists exactly because the form is
a composition the emitter declares once rather than one operator. -/
theorem derived_of_helper (code : Opcode) (helper : code.runtimeSymbolTag = "helper:") :
    code.derived = true := by
  cases code <;> first | rfl | simp [runtimeSymbolTag, runtimeSymbol] at helper

/-- An inline runtime symbol names the opcode it is the emitted form of, so the join between this
registry and `LEAN_RUNTIME_OPCODES` in `ir.ts` is a bijection rather than a lookup. -/
theorem runtimeSymbol_inline (code : Opcode) (inline : code.runtimeSymbolTag = "inline:") :
    code.runtimeSymbol = "inline:" ++ code.kind := by
  cases code <;> first | rfl | simp [runtimeSymbolTag, runtimeSymbol] at inline


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
  | .intAdd => [.bigintExactArithmetic]
  | .intSubtract => [.bigintExactArithmetic]
  | .intMultiply => [.bigintExactArithmetic]
  | .intNegate => [.bigintNegation]
  | .intTruncatedDivide =>
      [.strictEqualitySameType, .conditionalTruthySelection, .bigintTruncatedDivision]
  | .intTruncatedModulo =>
      [.strictEqualitySameType, .conditionalTruthySelection, .bigintTruncatedDivision]
  | .intLess => [.bigintRelational]
  | .intLessOrEqual => [.bigintRelational]
  | .intEquals => [.strictEqualitySameType]
  | .intOfNat => []
  | .intToNat => [.bigintRelational, .conditionalTruthySelection]
  | .charToNat => [.stringCodePointAt]
  | .charOfNat =>
      [.bigintRelational, .booleanLogicalOperators, .conditionalTruthySelection, .stringFromCodePoint]
  | .charEquals => [.strictEqualitySameType]
  | .charLess => [.stringCodePointAt, .bigintRelational]
  | .stringLength => [.stringCodePointIteration, .bigintFromLength]
  | .stringIsEmpty => [.stringEmptyCodeUnitLength]
  | .stringPush => [.stringUtf16Concatenation]
  | .stringSingleton => []
  | .stringToList => [.stringCodePointIteration]
  | .stringOfList => [.arrayJoinEmptySeparator]
  | .arraySize => [.bigintFromLength]
  | .arrayIsEmpty | .arrayPush | .arrayAppend | .arrayReverse => [.arrayDenseElementSequence]
  | .arrayToList | .arrayOfList => []

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
  | .intAdd => ∀ left right : Int,
      Encode.int (left + right) = runtime.natAdd (Encode.int left) (Encode.int right)
  | .intSubtract => ∀ left right : Int,
      Encode.int (left - right) = runtime.natDifference (Encode.int left) (Encode.int right)
  | .intMultiply => ∀ left right : Int,
      Encode.int (left * right) = runtime.natMultiply (Encode.int left) (Encode.int right)
  | .intNegate => ∀ operand : Int,
      Encode.int (-operand) = runtime.intNegate (Encode.int operand)
  | .intTruncatedDivide => ∀ left right : Int,
      Encode.int (left.tdiv right)
        = runtime.intTruncatedDivide (Encode.int left) (Encode.int right)
  | .intTruncatedModulo => ∀ left right : Int,
      Encode.int (left.tmod right)
        = runtime.intTruncatedModulo (Encode.int left) (Encode.int right)
  | .intLess => ∀ left right : Int,
      Encode.bool (decide (left < right)) = runtime.natLess (Encode.int left) (Encode.int right)
  | .intLessOrEqual => ∀ left right : Int,
      Encode.bool (decide (left ≤ right))
        = runtime.natLessOrEqual (Encode.int left) (Encode.int right)
  | .intEquals => ∀ left right : Int,
      Encode.bool (left == right) = runtime.natEquals (Encode.int left) (Encode.int right)
  | .intOfNat => ∀ operand : Nat,
      Encode.int (Int.ofNat operand) = runtime.intOfNat (Encode.nat operand)
  | .intToNat => ∀ operand : Int,
      Encode.nat operand.toNat = runtime.intToNat (Encode.int operand)
  | .charToNat => ∀ character : Char,
      Encode.nat character.toNat = runtime.charToNat (Encode.char character)
  | .charOfNat => ∀ code : Nat,
      Encode.char (Char.ofNat code) = runtime.charOfNat (Encode.nat code)
  | .charEquals => ∀ left right : Char,
      Encode.bool (left == right) = runtime.stringEquals (Encode.char left) (Encode.char right)
  | .charLess => ∀ left right : Char,
      Encode.bool (decide (left < right)) = runtime.charLess (Encode.char left) (Encode.char right)
  | .stringLength => ∀ value : String,
      Encode.nat value.length = runtime.stringLength (Encode.string value)
  | .stringIsEmpty => ∀ value : String,
      Encode.bool value.isEmpty = runtime.stringIsEmpty (Encode.string value)
  | .stringPush => ∀ (value : String) (character : Char),
      Encode.string (value.push character)
        = runtime.stringPush (Encode.string value) (Encode.char character)
  | .stringSingleton => ∀ character : Char,
      Encode.string (String.singleton character)
        = runtime.stringSingleton (Encode.char character)
  | .stringToList => ∀ value : String,
      value.toList.map Encode.char = runtime.stringToList (Encode.string value)
  | .stringOfList => ∀ characters : List Char,
      Encode.string (String.ofList characters)
        = runtime.stringOfList (characters.map Encode.char)
  | .arraySize => ∀ {α : Type} (encode : α → Value) (values : List α),
      Encode.nat values.length = runtime.listLength (values.map encode)
  | .arrayIsEmpty => ∀ {α : Type} (encode : α → Value) (values : List α),
      Encode.bool values.isEmpty = runtime.listIsEmpty (values.map encode)
  | .arrayPush => ∀ {α : Type} (encode : α → Value) (values : List α) (element : α),
      (values ++ [element]).map encode
        = runtime.listPush (values.map encode) (encode element)
  | .arrayAppend => ∀ {α : Type} (encode : α → Value) (left right : List α),
      (left ++ right).map encode = runtime.listAppend (left.map encode) (right.map encode)
  | .arrayReverse => ∀ {α : Type} (encode : α → Value) (values : List α),
      values.reverse.map encode = runtime.listReverse (values.map encode)
  | .arrayToList => ∀ image : Value, image = runtime.arrayToList image
  | .arrayOfList => ∀ image : Value, image = runtime.arrayOfList image

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
  have difference : ∀ left right : Int,
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
    rw [conditional.1 _ _ _, if_neg notCondition, difference (left : Int) (right : Int)]
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
  rw [List.map_cons, holds.1.2.2.2.2.2.2.2.2.2.2.1 (encode head) (List.map encode tail)]


/-! ### `Int`

A `Nat` and an `Int` share the bigint representation, so the three arithmetic rows name the same
engine operations the `nat.*` rows name and are discharged from the same recorded assumption. The
`Nat` rows carry the extra work: `nat.subtract` truncates, so it needs a guard, while `int.subtract`
is the raw difference.
-/

/-- `+` on two bigints denotes `Int.add` directly: the assumption is already stated at integer
operands, which is what makes the shared representation pay off. -/
theorem intAddModelsAdd (runtime : Runtime)
    (holds : Assumption.Holds runtime Opcode.intAdd.requires) :
    Opcode.intAdd.Preserves runtime := by
  intro left right
  unfold Encode.int
  rw [holds.1.1 left right]

/-- `-` on two bigints denotes `Int.sub`, including where the difference is negative, which is
exactly where the `Nat` row has to truncate instead. -/
theorem intSubtractModelsSub (runtime : Runtime)
    (holds : Assumption.Holds runtime Opcode.intSubtract.requires) :
    Opcode.intSubtract.Preserves runtime := by
  intro left right
  unfold Encode.int
  rw [holds.1.2.2.2 left right]

/-- `*` on two bigints denotes `Int.mul`. -/
theorem intMultiplyModelsMul (runtime : Runtime)
    (holds : Assumption.Holds runtime Opcode.intMultiply.requires) :
    Opcode.intMultiply.Preserves runtime := by
  intro left right
  unfold Encode.int
  rw [holds.1.2.1 left right]

/-- Unary `-` on a bigint denotes `Int.neg`. -/
theorem intNegateModelsNeg (runtime : Runtime)
    (holds : Assumption.Holds runtime Opcode.intNegate.requires) :
    Opcode.intNegate.Preserves runtime := by
  intro operand
  rw [holds.1 operand]

/-- The zero-guarded quotient helper denotes `Int.tdiv`. BigInt division throws on a zero divisor,
and `Int.tdiv` answers zero there, so the guard is what makes the two agree rather than a
convenience. -/
theorem intTruncatedDivideModelsTdiv (runtime : Runtime)
    (holds : Assumption.Holds runtime Opcode.intTruncatedDivide.requires) :
    Opcode.intTruncatedDivide.Preserves runtime := by
  intro left right
  rcases holds with ⟨equality, conditional, division, _⟩
  have condition : (runtime.natEquals (Encode.int right) (Encode.int 0)).toBoolean
      = decide (right = 0) := by
    rw [equality.2.1 (Encode.int right) (Encode.int 0)]
    unfold Model.strictEquals Encode.int Encode.bigint
    rw [TSLean.Refinement.BigInt.strictEqual_commutes right 0]
    by_cases zero : right = 0 <;>
      simp [Encode.bool, Value.toBoolean, Primitive.toBoolean, zero]
  unfold Runtime.intTruncatedDivide
  rw [conditional.1 _ _ _]
  by_cases zero : right = 0
  · rw [if_pos (by rw [condition]; simp [zero]), zero, Int.tdiv_zero]
  · rw [if_neg (by rw [condition]; simp [zero]), division.1 left right zero]

/-- The zero-guarded remainder helper denotes `Int.tmod`, which answers the dividend at a zero
divisor, which is exactly what the guard selects. -/
theorem intTruncatedModuloModelsTmod (runtime : Runtime)
    (holds : Assumption.Holds runtime Opcode.intTruncatedModulo.requires) :
    Opcode.intTruncatedModulo.Preserves runtime := by
  intro left right
  rcases holds with ⟨equality, conditional, division, _⟩
  have condition : (runtime.natEquals (Encode.int right) (Encode.int 0)).toBoolean
      = decide (right = 0) := by
    rw [equality.2.1 (Encode.int right) (Encode.int 0)]
    unfold Model.strictEquals Encode.int Encode.bigint
    rw [TSLean.Refinement.BigInt.strictEqual_commutes right 0]
    by_cases zero : right = 0 <;>
      simp [Encode.bool, Value.toBoolean, Primitive.toBoolean, zero]
  unfold Runtime.intTruncatedModulo
  rw [conditional.1 _ _ _]
  by_cases zero : right = 0
  · rw [if_pos (by rw [condition]; simp [zero]), zero, Int.tmod_zero]
  · rw [if_neg (by rw [condition]; simp [zero]), division.2 left right zero]

/-- `<` on two bigints denotes `Int.lt`. -/
theorem intLessModelsLt (runtime : Runtime)
    (holds : Assumption.Holds runtime Opcode.intLess.requires) :
    Opcode.intLess.Preserves runtime := by
  intro left right
  unfold Encode.int
  rw [holds.1.1 left right]

/-- `<=` on two bigints denotes `Int.le`. -/
theorem intLessOrEqualModelsLe (runtime : Runtime)
    (holds : Assumption.Holds runtime Opcode.intLessOrEqual.requires) :
    Opcode.intLessOrEqual.Preserves runtime := by
  intro left right
  unfold Encode.int
  rw [holds.1.2 left right]

/-- `===` on two bigints denotes `Int` equality. -/
theorem intEqualsModelsBEq (runtime : Runtime)
    (holds : Assumption.Holds runtime Opcode.intEquals.requires) :
    Opcode.intEquals.Preserves runtime := by
  intro left right
  rw [holds.1.2.1 (Encode.int left) (Encode.int right)]
  unfold Model.strictEquals Encode.int Encode.bigint
  rw [TSLean.Refinement.BigInt.strictEqual_commutes left right]

/-- `Int.ofNat` reaches the target as the operand itself. The widening is invisible because a `Nat`
and an `Int` are the same bigint, which is a representation fact and not an engine claim: this row
names no assumption at all. -/
theorem intOfNatModelsOfNat (runtime : Runtime)
    (_holds : Assumption.Holds runtime Opcode.intOfNat.requires) :
    Opcode.intOfNat.Preserves runtime := by
  intro operand
  rfl

/-- The clamping helper denotes `Int.toNat`: below zero the conditional yields zero, which is where
`Int.toNat` clamps, and at or above zero the operand already is its own image. -/
theorem intToNatModelsToNat (runtime : Runtime)
    (holds : Assumption.Holds runtime Opcode.intToNat.requires) :
    Opcode.intToNat.Preserves runtime := by
  intro operand
  rcases holds with ⟨relational, conditional, _⟩
  have condition : (runtime.natLess (Encode.int operand) (Encode.int 0)).toBoolean
      = decide (operand < 0) := by
    unfold Encode.int
    rw [relational.1 operand 0]
    simp [Encode.bool, Value.toBoolean, Primitive.toBoolean]
  unfold Runtime.intToNat
  rw [conditional.1 _ _ _]
  by_cases negative : operand < 0
  · rw [if_pos (by rw [condition]; simp [negative])]
    have clamped : operand.toNat = 0 := by omega
    rw [clamped]
  · rw [if_neg (by rw [condition]; simp [negative])]
    unfold Encode.nat Encode.int Encode.bigint
    rw [Int.toNat_of_nonneg (by omega)]

/-! ### `Char`

A `Char` reaches the target as a string of exactly one code point. That is why `string.singleton` is
the identity on the image, and why `char.less` compares code points rather than the `<` the engine
would apply to the two strings: code-unit order disagrees with scalar order for an astral character
against U+E000..U+FFFF.
-/

/-- `BigInt(operand.codePointAt(0))` denotes `Char.toNat`. -/
theorem charToNatModelsToNat (runtime : Runtime)
    (holds : Assumption.Holds runtime Opcode.charToNat.requires) :
    Opcode.charToNat.Preserves runtime := by
  intro character
  rw [holds.1 character]

/-- `===` on two one-code-point strings denotes `Char` equality, because the singleton map is
injective and the UTF-16 encoding of a Lean string is. -/
theorem charEqualsModelsBEq (runtime : Runtime)
    (holds : Assumption.Holds runtime Opcode.charEquals.requires) :
    Opcode.charEquals.Preserves runtime := by
  intro left right
  rw [holds.1.2.2 (Encode.char left) (Encode.char right)]
  unfold Model.strictEquals Encode.char Encode.string Encode.jsString
  rw [TSLean.Refinement.String.strictEqual_commutes (String.singleton left)
    (String.singleton right)]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  refine ⟨fun equal => by rw [equal], fun equal => ?_⟩
  have lists := congrArg String.toList equal
  simpa using lists

/-- The code-point comparison helper denotes `Char.lt`, which is the order on scalar values. -/
theorem charLessModelsLt (runtime : Runtime)
    (holds : Assumption.Holds runtime Opcode.charLess.requires) :
    Opcode.charLess.Preserves runtime := by
  intro left right
  rcases holds with ⟨codePoint, relational, _⟩
  unfold Runtime.charLess
  rw [codePoint left, codePoint right]
  unfold Encode.nat
  rw [relational.1 (left.toNat : Int) (right.toNat : Int)]
  congr 1
  apply decide_eq_decide.mpr
  rw [Char.lt_def, UInt32.lt_iff_toNat_lt, Int.ofNat_lt]
  rfl

/-- A code that is a Unicode scalar value is the scalar value of the character it names: `Char.ofNat`
stores the code itself in that branch. -/
private theorem toNat_ofNat_of_valid {code : Nat} (valid : Nat.isValidChar code) :
    (Char.ofNat code).toNat = code := by
  simp [Char.ofNat, Char.toNat, dif_pos valid, Char.ofNatAux]

/-- A code that is not a scalar value names the null character, which is what the emitted guard's
alternate branch answers. -/
private theorem ofNat_of_invalid {code : Nat} (invalid : ¬ Nat.isValidChar code) :
    Char.ofNat code = Char.ofNat 0 := by
  apply Char.ext
  simp [Char.ofNat, dif_neg invalid, Char.ofNatAux]

/-- The scalar-value guard helper denotes `Char.ofNat`, including its answer for a code that is not
a scalar value: Lean gives the null character there, and the guard's alternate branch is exactly
that character's image. -/
theorem charOfNatModelsOfNat (runtime : Runtime)
    (holds : Assumption.Holds runtime Opcode.charOfNat.requires) :
    Opcode.charOfNat.Preserves runtime := by
  intro code
  rcases holds with ⟨relational, logical, conditional, fromCodePoint, _⟩
  have upper : runtime.natLessOrEqual (Encode.nat code) (Encode.int 1114111)
      = Encode.bool (decide ((code : Int) ≤ 1114111)) := by
    unfold Encode.nat Encode.int
    exact relational.2 (code : Int) 1114111
  have below : runtime.natLess (Encode.nat code) (Encode.int 55296)
      = Encode.bool (decide ((code : Int) < 55296)) := by
    unfold Encode.nat Encode.int
    exact relational.1 (code : Int) 55296
  have above : runtime.natLess (Encode.int 57343) (Encode.nat code)
      = Encode.bool (decide ((57343 : Int) < (code : Int))) := by
    unfold Encode.nat Encode.int
    exact relational.1 57343 (code : Int)
  have condition :
      (runtime.boolAnd (runtime.natLessOrEqual (Encode.nat code) (Encode.int 1114111))
          (runtime.boolOr (runtime.natLess (Encode.nat code) (Encode.int 55296))
            (runtime.natLess (Encode.int 57343) (Encode.nat code)))).toBoolean
        = decide (Nat.isValidChar code) := by
    rw [logical.1 _ _, logical.2.1 _ _, upper, below, above]
    unfold Model.boolAnd Model.boolOr Encode.bool Value.toBoolean Primitive.toBoolean
    by_cases upperBound : ((code : Int) ≤ 1114111)
    · by_cases lower : ((code : Int) < 55296)
      · have valid : Nat.isValidChar code := by
          unfold Nat.isValidChar
          omega
        simp [upperBound, lower, valid]
      · by_cases higher : ((57343 : Int) < (code : Int))
        · have valid : Nat.isValidChar code := by
            unfold Nat.isValidChar
            omega
          simp [upperBound, lower, higher, valid]
        · have invalid : ¬ Nat.isValidChar code := by
            unfold Nat.isValidChar
            omega
          simp [upperBound, lower, higher, invalid]
    · have invalid : ¬ Nat.isValidChar code := by
        unfold Nat.isValidChar
        omega
      simp [upperBound, invalid]
  unfold Runtime.charOfNat
  rw [conditional.1 _ _ _]
  by_cases valid : Nat.isValidChar code
  · rw [if_pos (by rw [condition]; simp [valid])]
    have image := fromCodePoint (Char.ofNat code)
    rw [toNat_ofNat_of_valid valid] at image
    rw [image]
  · rw [if_neg (by rw [condition]; simp [valid]), ofNat_of_invalid valid]

/-! ### `String`

`String.length` counts code points, so its helper spreads the string; `value.length` counts UTF-16
code units and disagrees outside the BMP. `string.toList` and `string.ofList` are the proved bridge
to `List Char`, which is what makes the rest of `String` expressible in Lean rather than in a widened
opcode set.
-/

/-- The spread-and-length helper denotes `String.length`, which counts code points. -/
theorem stringLengthModelsLength (runtime : Runtime)
    (holds : Assumption.Holds runtime Opcode.stringLength.requires) :
    Opcode.stringLength.Preserves runtime := by
  intro value
  rcases holds with ⟨iteration, fromLength, _⟩
  unfold Runtime.stringLength
  rw [iteration value, fromLength (value.toList.map Encode.char), List.length_map]
  rfl

/-- `value.length === 0` denotes `String.isEmpty`. -/
theorem stringIsEmptyModelsIsEmpty (runtime : Runtime)
    (holds : Assumption.Holds runtime Opcode.stringIsEmpty.requires) :
    Opcode.stringIsEmpty.Preserves runtime := by
  intro value
  rw [holds.1 value]

/-- `value + character` denotes `String.push`, which is concatenation with a one-code-point
string. -/
theorem stringPushModelsPush (runtime : Runtime)
    (holds : Assumption.Holds runtime Opcode.stringPush.requires) :
    Opcode.stringPush.Preserves runtime := by
  intro value character
  unfold Runtime.stringPush Encode.char Encode.string
  rw [holds.1 (JSString.ofLeanString value) (JSString.ofLeanString (String.singleton character)),
    ← JSString.ofLeanString_append]
  rfl

/-- `String.singleton` reaches the target as the operand itself, because a `Char`'s image already is
that one-code-point string. -/
theorem stringSingletonModelsSingleton (runtime : Runtime)
    (_holds : Assumption.Holds runtime Opcode.stringSingleton.requires) :
    Opcode.stringSingleton.Preserves runtime := by
  intro character
  rfl

/-- `[...value]` denotes `String.toList`, code point for code point. -/
theorem stringToListModelsToList (runtime : Runtime)
    (holds : Assumption.Holds runtime Opcode.stringToList.requires) :
    Opcode.stringToList.Preserves runtime := by
  intro value
  rw [holds.1 value]

/-- `value.join("")` denotes `String.ofList`. -/
theorem stringOfListModelsOfList (runtime : Runtime)
    (holds : Assumption.Holds runtime Opcode.stringOfList.requires) :
    Opcode.stringOfList.Preserves runtime := by
  intro characters
  rw [holds.1 characters]

/-! ### `Array`

An `Array` and a `List` share the dense-array image, so five of these rows name the engine
operations the `list.*` rows name and two are identities. That sharing is the point: it is what makes
`list.map`, `list.filter` and the folds reachable from an `Array` through `array.toList` without a
second higher-order family and a second set of callback proofs.
-/

/-- `BigInt(value.length)` denotes `Array.size`. -/
theorem arraySizeModelsSize (runtime : Runtime)
    (holds : Assumption.Holds runtime Opcode.arraySize.requires) :
    Opcode.arraySize.Preserves runtime := by
  intro α encode values
  rw [holds.1 (values.map encode), List.length_map]

/-- `value.length === 0` denotes `Array.isEmpty`. -/
theorem arrayIsEmptyModelsIsEmpty (runtime : Runtime)
    (holds : Assumption.Holds runtime Opcode.arrayIsEmpty.requires) :
    Opcode.arrayIsEmpty.Preserves runtime := by
  intro α encode values
  rw [holds.1.1 (values.map encode)]
  cases values <;> simp

/-- `[...value, element]` denotes `Array.push`. -/
theorem arrayPushModelsPush (runtime : Runtime)
    (holds : Assumption.Holds runtime Opcode.arrayPush.requires) :
    Opcode.arrayPush.Preserves runtime := by
  intro α encode values element
  rw [holds.1.2.2.2.2.2.2.2.2.2.2.2 (values.map encode) (encode element),
    List.map_append]
  rfl

/-- `[...left, ...right]` denotes `Array.append`. -/
theorem arrayAppendModelsAppend (runtime : Runtime)
    (holds : Assumption.Holds runtime Opcode.arrayAppend.requires) :
    Opcode.arrayAppend.Preserves runtime := by
  intro α encode left right
  rw [holds.1.2.1 (left.map encode) (right.map encode), List.map_append]

/-- `[...value].reverse()` denotes `Array.reverse`. -/
theorem arrayReverseModelsReverse (runtime : Runtime)
    (holds : Assumption.Holds runtime Opcode.arrayReverse.requires) :
    Opcode.arrayReverse.Preserves runtime := by
  intro α encode values
  rw [holds.1.2.2.1 (values.map encode), List.map_reverse]

/-- `Array.toList` reaches the target as the operand itself, because the two share the dense-array
image. This row claims nothing about the engine, and saying it did would be false. -/
theorem arrayToListModelsToList (runtime : Runtime)
    (_holds : Assumption.Holds runtime Opcode.arrayToList.requires) :
    Opcode.arrayToList.Preserves runtime := by
  intro image
  rfl

/-- `List.toArray` reaches the target as the operand itself, at the same identity. -/
theorem arrayOfListModelsOfList (runtime : Runtime)
    (_holds : Assumption.Holds runtime Opcode.arrayOfList.requires) :
    Opcode.arrayOfList.Preserves runtime := by
  intro image
  rfl

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
  | .intAdd => intAddModelsAdd runtime
  | .intSubtract => intSubtractModelsSub runtime
  | .intMultiply => intMultiplyModelsMul runtime
  | .intNegate => intNegateModelsNeg runtime
  | .intTruncatedDivide => intTruncatedDivideModelsTdiv runtime
  | .intTruncatedModulo => intTruncatedModuloModelsTmod runtime
  | .intLess => intLessModelsLt runtime
  | .intLessOrEqual => intLessOrEqualModelsLe runtime
  | .intEquals => intEqualsModelsBEq runtime
  | .intOfNat => intOfNatModelsOfNat runtime
  | .intToNat => intToNatModelsToNat runtime
  | .charToNat => charToNatModelsToNat runtime
  | .charOfNat => charOfNatModelsOfNat runtime
  | .charEquals => charEqualsModelsBEq runtime
  | .charLess => charLessModelsLt runtime
  | .stringLength => stringLengthModelsLength runtime
  | .stringIsEmpty => stringIsEmptyModelsIsEmpty runtime
  | .stringPush => stringPushModelsPush runtime
  | .stringSingleton => stringSingletonModelsSingleton runtime
  | .stringToList => stringToListModelsToList runtime
  | .stringOfList => stringOfListModelsOfList runtime
  | .arraySize => arraySizeModelsSize runtime
  | .arrayIsEmpty => arrayIsEmptyModelsIsEmpty runtime
  | .arrayPush => arrayPushModelsPush runtime
  | .arrayAppend => arrayAppendModelsAppend runtime
  | .arrayReverse => arrayReverseModelsReverse runtime
  | .arrayToList => arrayToListModelsToList runtime
  | .arrayOfList => arrayOfListModelsOfList runtime

/-- Every admitted opcode is discharged from its own recorded assumption closure. -/
theorem registry_total (runtime : Runtime) (code : Opcode)
    (holds : Assumption.Holds runtime code.requires) : code.Preserves runtime :=
  registry runtime code holds

end Opcode

end TSLean.LeanToTypeScript.Semantics
