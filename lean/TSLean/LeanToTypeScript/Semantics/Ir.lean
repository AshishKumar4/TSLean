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

/--
A type of the admitted fragment, in Coverage v5's nine forms. `parameter` is a de Bruijn index into
the enclosing declaration's type parameters; `named` refers to a declared record or enum and carries
the arguments that instantiate it. `option`, `except` and `list` are mapped Lean types: they are not
declarations, but they carry constructors all the same, which is what lets one `variant` form and
one `match` form decide them with exactly the machinery a user inductive uses.
-/
inductive Ty where
  | boolean
  | nat
  | string
  | parameter (index : Nat)
  | named (name : String) (arguments : List Ty)
  | option (value : Ty)
  | except (error value : Ty)
  | list (element : Ty)
  | function (parameters : List Ty) (result : Ty)
  /-- `Int`, which reaches the target as a bigint exactly as a `Nat` does: the two share one
  representation, which is what makes `int.ofNat` the identity rather than a conversion. -/
  | int
  /-- `Char`, which reaches the target as a string of exactly one code point. -/
  | char
  /-- `ByteArray`, which reaches the target as a `Uint8Array`. -/
  | bytes
  /-- The TSLean-owned `JsonValue`, a mapped Lean inductive carrying the six constructors its
  discriminated-union image carries. -/
  | json
  /-- `Array α`, which shares the dense-array image with `list`. The two are distinct type forms
  because their Lean operations are distinct, not because their values are. -/
  | array (element : Ty)
  /-- `α × β`, which reaches the target as an object with own keys `fst` then `snd`. It is a mapped
  Lean structure, so it carries one constructor and is decided by field reads. -/
  | pair (first second : Ty)
  /-- `Std.HashMap κ ν`, which reaches the target as a `Map` whose entry sequence is kept sorted by
  key, so iteration is deterministic. -/
  | hashMap (key value : Ty)
  /-- `Std.TreeMap κ ν`, with the same sorted image. -/
  | treeMap (key value : Ty)
  deriving Repr

mutual

/-- Structural equality on types. The type nests through `List Ty`, which the `DecidableEq` deriving
handler does not reach, so the decision is written out rather than assumed. -/
def Ty.decEq : (left right : Ty) → Decidable (left = right)
  | .boolean, .boolean => isTrue rfl
  | .nat, .nat => isTrue rfl
  | .string, .string => isTrue rfl
  | .int, .int => isTrue rfl
  | .char, .char => isTrue rfl
  | .bytes, .bytes => isTrue rfl
  | .json, .json => isTrue rfl
  | .parameter left, .parameter right =>
      if index : left = right then isTrue (by rw [index]) else isFalse (by simp [index])
  | .named leftName leftArguments, .named rightName rightArguments =>
      if names : leftName = rightName then
        match Ty.decEqList leftArguments rightArguments with
        | isTrue arguments => isTrue (by rw [names, arguments])
        | isFalse arguments => isFalse (by simp [arguments])
      else isFalse (by simp [names])
  | .option left, .option right =>
      match Ty.decEq left right with
      | isTrue value => isTrue (by rw [value])
      | isFalse value => isFalse (by simp [value])
  | .list left, .list right =>
      match Ty.decEq left right with
      | isTrue element => isTrue (by rw [element])
      | isFalse element => isFalse (by simp [element])
  | .array left, .array right =>
      match Ty.decEq left right with
      | isTrue element => isTrue (by rw [element])
      | isFalse element => isFalse (by simp [element])
  | .except leftError leftValue, .except rightError rightValue =>
      match Ty.decEq leftError rightError, Ty.decEq leftValue rightValue with
      | isTrue error, isTrue value => isTrue (by rw [error, value])
      | isFalse error, _ => isFalse (by simp [error])
      | _, isFalse value => isFalse (by simp [value])
  | .pair leftFirst leftSecond, .pair rightFirst rightSecond =>
      match Ty.decEq leftFirst rightFirst, Ty.decEq leftSecond rightSecond with
      | isTrue first, isTrue second => isTrue (by rw [first, second])
      | isFalse first, _ => isFalse (by simp [first])
      | _, isFalse second => isFalse (by simp [second])
  | .hashMap leftKey leftValue, .hashMap rightKey rightValue =>
      match Ty.decEq leftKey rightKey, Ty.decEq leftValue rightValue with
      | isTrue key, isTrue value => isTrue (by rw [key, value])
      | isFalse key, _ => isFalse (by simp [key])
      | _, isFalse value => isFalse (by simp [value])
  | .treeMap leftKey leftValue, .treeMap rightKey rightValue =>
      match Ty.decEq leftKey rightKey, Ty.decEq leftValue rightValue with
      | isTrue key, isTrue value => isTrue (by rw [key, value])
      | isFalse key, _ => isFalse (by simp [key])
      | _, isFalse value => isFalse (by simp [value])
  | .function leftParameters leftResult, .function rightParameters rightResult =>
      match Ty.decEqList leftParameters rightParameters, Ty.decEq leftResult rightResult with
      | isTrue parameters, isTrue result => isTrue (by rw [parameters, result])
      | isFalse parameters, _ => isFalse (by simp [parameters])
      | _, isFalse result => isFalse (by simp [result])
  | .boolean, .nat | .boolean, .string | .boolean, .parameter _ | .boolean, .named _ _
  | .boolean, .option _ | .boolean, .except _ _ | .boolean, .list _ | .boolean, .function _ _
  | .boolean, .int | .boolean, .char | .boolean, .bytes | .boolean, .json | .boolean, .array _
  | .boolean, .pair _ _ | .boolean, .hashMap _ _ | .boolean, .treeMap _ _
  | .nat, .boolean | .nat, .string | .nat, .parameter _ | .nat, .named _ _ | .nat, .option _
  | .nat, .except _ _ | .nat, .list _ | .nat, .function _ _ | .nat, .int | .nat, .char
  | .nat, .bytes | .nat, .json | .nat, .array _ | .nat, .pair _ _ | .nat, .hashMap _ _
  | .nat, .treeMap _ _
  | .string, .boolean | .string, .nat | .string, .parameter _ | .string, .named _ _
  | .string, .option _ | .string, .except _ _ | .string, .list _ | .string, .function _ _
  | .string, .int | .string, .char | .string, .bytes | .string, .json | .string, .array _
  | .string, .pair _ _ | .string, .hashMap _ _ | .string, .treeMap _ _
  | .parameter _, .boolean | .parameter _, .nat | .parameter _, .string | .parameter _, .named _ _
  | .parameter _, .option _ | .parameter _, .except _ _ | .parameter _, .list _
  | .parameter _, .function _ _ | .parameter _, .int | .parameter _, .char | .parameter _, .bytes
  | .parameter _, .json | .parameter _, .array _ | .parameter _, .pair _ _
  | .parameter _, .hashMap _ _ | .parameter _, .treeMap _ _
  | .named _ _, .boolean | .named _ _, .nat | .named _ _, .string | .named _ _, .parameter _
  | .named _ _, .option _ | .named _ _, .except _ _ | .named _ _, .list _
  | .named _ _, .function _ _ | .named _ _, .int | .named _ _, .char | .named _ _, .bytes
  | .named _ _, .json | .named _ _, .array _ | .named _ _, .pair _ _ | .named _ _, .hashMap _ _
  | .named _ _, .treeMap _ _
  | .option _, .boolean | .option _, .nat | .option _, .string | .option _, .parameter _
  | .option _, .named _ _ | .option _, .except _ _ | .option _, .list _ | .option _, .function _ _
  | .option _, .int | .option _, .char | .option _, .bytes | .option _, .json
  | .option _, .array _ | .option _, .pair _ _ | .option _, .hashMap _ _ | .option _, .treeMap _ _
  | .except _ _, .boolean | .except _ _, .nat | .except _ _, .string | .except _ _, .parameter _
  | .except _ _, .named _ _ | .except _ _, .option _ | .except _ _, .list _
  | .except _ _, .function _ _ | .except _ _, .int | .except _ _, .char | .except _ _, .bytes
  | .except _ _, .json | .except _ _, .array _ | .except _ _, .pair _ _
  | .except _ _, .hashMap _ _ | .except _ _, .treeMap _ _
  | .list _, .boolean | .list _, .nat | .list _, .string | .list _, .parameter _
  | .list _, .named _ _ | .list _, .option _ | .list _, .except _ _ | .list _, .function _ _
  | .list _, .int | .list _, .char | .list _, .bytes | .list _, .json | .list _, .array _
  | .list _, .pair _ _ | .list _, .hashMap _ _ | .list _, .treeMap _ _
  | .function _ _, .boolean | .function _ _, .nat | .function _ _, .string
  | .function _ _, .parameter _ | .function _ _, .named _ _ | .function _ _, .option _
  | .function _ _, .except _ _ | .function _ _, .list _ | .function _ _, .int
  | .function _ _, .char | .function _ _, .bytes | .function _ _, .json | .function _ _, .array _
  | .function _ _, .pair _ _ | .function _ _, .hashMap _ _ | .function _ _, .treeMap _ _
  | .int, .boolean | .int, .nat | .int, .string | .int, .parameter _ | .int, .named _ _
  | .int, .option _ | .int, .except _ _ | .int, .list _ | .int, .function _ _ | .int, .char
  | .int, .bytes | .int, .json | .int, .array _ | .int, .pair _ _ | .int, .hashMap _ _
  | .int, .treeMap _ _
  | .char, .boolean | .char, .nat | .char, .string | .char, .parameter _ | .char, .named _ _
  | .char, .option _ | .char, .except _ _ | .char, .list _ | .char, .function _ _ | .char, .int
  | .char, .bytes | .char, .json | .char, .array _ | .char, .pair _ _ | .char, .hashMap _ _
  | .char, .treeMap _ _
  | .bytes, .boolean | .bytes, .nat | .bytes, .string | .bytes, .parameter _ | .bytes, .named _ _
  | .bytes, .option _ | .bytes, .except _ _ | .bytes, .list _ | .bytes, .function _ _
  | .bytes, .int | .bytes, .char | .bytes, .json | .bytes, .array _ | .bytes, .pair _ _
  | .bytes, .hashMap _ _ | .bytes, .treeMap _ _
  | .json, .boolean | .json, .nat | .json, .string | .json, .parameter _ | .json, .named _ _
  | .json, .option _ | .json, .except _ _ | .json, .list _ | .json, .function _ _ | .json, .int
  | .json, .char | .json, .bytes | .json, .array _ | .json, .pair _ _ | .json, .hashMap _ _
  | .json, .treeMap _ _
  | .array _, .boolean | .array _, .nat | .array _, .string | .array _, .parameter _
  | .array _, .named _ _ | .array _, .option _ | .array _, .except _ _ | .array _, .list _
  | .array _, .function _ _ | .array _, .int | .array _, .char | .array _, .bytes
  | .array _, .json | .array _, .pair _ _ | .array _, .hashMap _ _ | .array _, .treeMap _ _
  | .pair _ _, .boolean | .pair _ _, .nat | .pair _ _, .string | .pair _ _, .parameter _
  | .pair _ _, .named _ _ | .pair _ _, .option _ | .pair _ _, .except _ _ | .pair _ _, .list _
  | .pair _ _, .function _ _ | .pair _ _, .int | .pair _ _, .char | .pair _ _, .bytes
  | .pair _ _, .json | .pair _ _, .array _ | .pair _ _, .hashMap _ _ | .pair _ _, .treeMap _ _
  | .hashMap _ _, .boolean | .hashMap _ _, .nat | .hashMap _ _, .string
  | .hashMap _ _, .parameter _ | .hashMap _ _, .named _ _ | .hashMap _ _, .option _
  | .hashMap _ _, .except _ _ | .hashMap _ _, .list _ | .hashMap _ _, .function _ _
  | .hashMap _ _, .int | .hashMap _ _, .char | .hashMap _ _, .bytes | .hashMap _ _, .json
  | .hashMap _ _, .array _ | .hashMap _ _, .pair _ _ | .hashMap _ _, .treeMap _ _
  | .treeMap _ _, .boolean | .treeMap _ _, .nat | .treeMap _ _, .string
  | .treeMap _ _, .parameter _ | .treeMap _ _, .named _ _ | .treeMap _ _, .option _
  | .treeMap _ _, .except _ _ | .treeMap _ _, .list _ | .treeMap _ _, .function _ _
  | .treeMap _ _, .int | .treeMap _ _, .char | .treeMap _ _, .bytes | .treeMap _ _, .json
  | .treeMap _ _, .array _ | .treeMap _ _, .pair _ _ | .treeMap _ _, .hashMap _ _ => isFalse nofun

/-- Structural equality on a type-argument list, in step with `Ty.decEq`. -/
def Ty.decEqList : (left right : List Ty) → Decidable (left = right)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse nofun
  | _ :: _, [] => isFalse nofun
  | leftHead :: leftRest, rightHead :: rightRest =>
      match Ty.decEq leftHead rightHead, Ty.decEqList leftRest rightRest with
      | isTrue head, isTrue rest => isTrue (by rw [head, rest])
      | isFalse head, _ => isFalse (by simp [head])
      | _, isFalse rest => isFalse (by simp [rest])

end

instance : DecidableEq Ty := Ty.decEq

/-- The nine type forms the fragment admits, as a closed registry. -/
inductive TyKind where
  | boolean
  | nat
  | string
  | parameter
  | named
  | option
  | except
  | list
  | function
  | int
  | char
  | bytes
  | json
  | array
  | pair
  | hashMap
  | treeMap
  deriving DecidableEq, Repr

/-- The wire spelling `Export.lean` writes and `ir.ts` decodes. -/
def TyKind.kind : TyKind → String
  | .boolean => "boolean"
  | .nat => "nat"
  | .string => "string"
  | .parameter => "parameter"
  | .named => "named"
  | .option => "option"
  | .except => "except"
  | .list => "list"
  | .function => "function"
  | .int => "int"
  | .char => "char"
  | .bytes => "bytes"
  | .json => "json"
  | .array => "array"
  | .pair => "pair"
  | .hashMap => "hashMap"
  | .treeMap => "treeMap"

/-- Every admitted type form. -/
def TyKind.all : List TyKind :=
  [.boolean, .nat, .string, .parameter, .named, .option, .except, .list, .function, .int, .char,
    .bytes, .json, .array, .pair, .hashMap, .treeMap]

theorem TyKind.mem_all (kind : TyKind) : kind ∈ TyKind.all := by
  cases kind <;> simp [TyKind.all]

/-- Distinct type forms have distinct wire spellings, so the registry join is a bijection. -/
theorem TyKind.kind_injective {left right : TyKind} (equal : left.kind = right.kind) :
    left = right := by
  cases left <;> cases right <;> simp_all [TyKind.kind]

/-- The registry entry a type belongs to. -/
def Ty.kind : Ty → TyKind
  | .boolean => .boolean
  | .nat => .nat
  | .string => .string
  | .parameter _ => .parameter
  | .named _ _ => .named
  | .option _ => .option
  | .except _ _ => .except
  | .list _ => .list
  | .function _ _ => .function
  | .int => .int
  | .char => .char
  | .bytes => .bytes
  | .json => .json
  | .array _ => .array
  | .pair _ _ => .pair
  | .hashMap _ _ => .hashMap
  | .treeMap _ _ => .treeMap

/--
The element type a `List` holds, and `none` for every other form.

A `List` is the one admitted type whose values reach the target as a dense array rather than as a
tag or a tagged object, so the lowering and the source semantics both decide that representation
here. Deciding it through one accessor rather than through a syntactic case in each of them is what
keeps the two from drifting.
-/
def Ty.element? : Ty → Option Ty
  | .list element => some element
  | .boolean | .nat | .string | .parameter _ | .named _ _ | .option _ | .except _ _
  | .function _ _ | .int | .char | .bytes | .json | .array _ | .pair _ _ | .hashMap _ _
  | .treeMap _ _ => none

/-- Exactly the `list` form holds an element type. -/
theorem Ty.eq_list_of_element? {type element : Ty} (held : type.element? = some element) :
    type = .list element := by
  cases type <;> simp_all [Ty.element?]

/-! ## The runtime opcode registry

The closed set of runtime opcodes the `operation` expression form carries. The registry lives
here, in the syntax layer, because the IR names it; `Opcode.lean` layers the emitted forms, the
assumption closures and the preservation laws on top of exactly this set, so there is one
registry rather than a syntax copy beside a semantic copy.
-/

/-- Every runtime opcode the exporter admits. -/
inductive Opcode where
  | boolAnd
  | boolOr
  | boolNot
  | boolEquals
  | natAdd
  | natSubtract
  | natMultiply
  | natLess
  | natLessOrEqual
  | natEquals
  | natSuccessor
  | stringAppend
  | stringEquals
  | listLength
  | listIsEmpty
  | listAppend
  | listReverse
  | listMap
  | listFilter
  | listFoldLeft
  | listFoldRight
  | listAny
  | listAll
  | listHead
  | listFirst
  | listRest
  | intAdd
  | intSubtract
  | intMultiply
  | intNegate
  | intTruncatedDivide
  | intTruncatedModulo
  | intLess
  | intLessOrEqual
  | intEquals
  | intOfNat
  | intToNat
  | charToNat
  | charOfNat
  | charEquals
  | charLess
  | stringLength
  | stringIsEmpty
  | stringPush
  | stringSingleton
  | stringToList
  | stringOfList
  | arraySize
  | arrayIsEmpty
  | arrayPush
  | arrayAppend
  | arrayReverse
  | arrayToList
  | arrayOfList
  deriving DecidableEq, Repr

/-- The wire spelling the IR carries. -/
def Opcode.kind : Opcode → String
  | .boolAnd => "bool.and"
  | .boolOr => "bool.or"
  | .boolNot => "bool.not"
  | .boolEquals => "bool.equals"
  | .natAdd => "nat.add"
  | .natSubtract => "nat.subtract"
  | .natMultiply => "nat.multiply"
  | .natLess => "nat.less"
  | .natLessOrEqual => "nat.lessOrEqual"
  | .natEquals => "nat.equals"
  | .natSuccessor => "nat.successor"
  | .stringAppend => "string.append"
  | .stringEquals => "string.equals"
  | .listLength => "list.length"
  | .listIsEmpty => "list.isEmpty"
  | .listAppend => "list.append"
  | .listReverse => "list.reverse"
  | .listMap => "list.map"
  | .listFilter => "list.filter"
  | .listFoldLeft => "list.foldLeft"
  | .listFoldRight => "list.foldRight"
  | .listAny => "list.any"
  | .listAll => "list.all"
  | .listHead => "list.head"
  | .listFirst => "list.first"
  | .listRest => "list.rest"
  | .intAdd => "int.add"
  | .intSubtract => "int.subtract"
  | .intMultiply => "int.multiply"
  | .intNegate => "int.negate"
  | .intTruncatedDivide => "int.tdiv"
  | .intTruncatedModulo => "int.tmod"
  | .intLess => "int.less"
  | .intLessOrEqual => "int.lessOrEqual"
  | .intEquals => "int.equals"
  | .intOfNat => "int.ofNat"
  | .intToNat => "int.toNat"
  | .charToNat => "char.toNat"
  | .charOfNat => "char.ofNat"
  | .charEquals => "char.equals"
  | .charLess => "char.less"
  | .stringLength => "string.length"
  | .stringIsEmpty => "string.isEmpty"
  | .stringPush => "string.push"
  | .stringSingleton => "string.singleton"
  | .stringToList => "string.toList"
  | .stringOfList => "string.ofList"
  | .arraySize => "array.size"
  | .arrayIsEmpty => "array.isEmpty"
  | .arrayPush => "array.push"
  | .arrayAppend => "array.append"
  | .arrayReverse => "array.reverse"
  | .arrayToList => "array.toList"
  | .arrayOfList => "array.ofList"


/-- Every admitted opcode. -/
def Opcode.all : List Opcode :=
  [ .boolAnd, .boolOr, .boolNot, .boolEquals, .natAdd, .natSubtract, .natMultiply, .natLess,
    .natLessOrEqual, .natEquals, .natSuccessor, .stringAppend, .stringEquals, .listLength,
    .listIsEmpty, .listAppend, .listReverse, .listMap, .listFilter, .listFoldLeft, .listFoldRight,
    .listAny, .listAll, .listHead, .listFirst, .listRest, .intAdd, .intSubtract, .intMultiply,
    .intNegate, .intTruncatedDivide, .intTruncatedModulo, .intLess, .intLessOrEqual, .intEquals,
    .intOfNat, .intToNat, .charToNat, .charOfNat, .charEquals, .charLess, .stringLength,
    .stringIsEmpty, .stringPush, .stringSingleton, .stringToList, .stringOfList, .arraySize,
    .arrayIsEmpty, .arrayPush, .arrayAppend, .arrayReverse, .arrayToList, .arrayOfList]

theorem Opcode.mem_all (code : Opcode) : code ∈ Opcode.all := by
  cases code <;> simp [Opcode.all]

/-- Distinct opcodes have distinct wire spellings, so the registry join is a bijection. -/
theorem Opcode.kind_injective {left right : Opcode} (equal : left.kind = right.kind) : left = right := by
  cases left <;> cases right <;> simp_all [Opcode.kind]

/-!
### The four opcodes the target spells as operators

`emitter.ts` writes `left && right`, `left || right`, `!operand` and `left === right` rather than a
call to a runtime operation. That is one meaning per operator, and it is not the operation form's:
`&&` and `||` evaluate their right operand only when it decides the answer, so routing them through
an operation call would evaluate it eagerly and make the two sides disagree about whether its calls
happen. `Target.runOperation` therefore refuses all four as operation calls.

`operator?` is the one place that decision lives. The lowering and the source semantics both consult
it, so an opcode cannot be lazy on one side and strict on the other.
-/

/-- An emitted operator, as opposed to a call to a runtime operation. -/
inductive OperatorForm where
  /-- `left && right`, lazy in its right operand. -/
  | logicalAnd
  /-- `left || right`, lazy in its right operand. -/
  | logicalOr
  /-- `!operand`. -/
  | logicalNot
  /-- `left === right`. -/
  | strictEquals
  deriving DecidableEq, Repr

/-- The number of operands the operator form takes. An opcode reached with any other number of
operands has no operator form and lowers to the operation form, which the target refuses. -/
def OperatorForm.operands : OperatorForm → Nat
  | .logicalAnd | .logicalOr | .strictEquals => 2
  | .logicalNot => 1

/-- The operator the target spells the opcode as, and `none` for an opcode it calls. -/
def Opcode.operator? : Opcode → Option OperatorForm
  | .boolAnd => some .logicalAnd
  | .boolOr => some .logicalOr
  | .boolNot => some .logicalNot
  | .boolEquals => some .strictEquals
  | .natAdd | .natSubtract | .natMultiply | .natLess | .natLessOrEqual | .natEquals
  | .natSuccessor | .stringAppend | .stringEquals | .listLength | .listIsEmpty | .listAppend
  | .listReverse | .listMap | .listFilter | .listFoldLeft | .listFoldRight | .listAny | .listAll
  | .listHead | .listFirst | .listRest | .intAdd | .intSubtract | .intMultiply | .intNegate
  | .intTruncatedDivide | .intTruncatedModulo | .intLess | .intLessOrEqual | .intEquals
  | .intOfNat | .intToNat | .charToNat | .charOfNat | .charEquals | .charLess | .stringLength
  | .stringIsEmpty | .stringPush | .stringSingleton | .stringToList | .stringOfList
  | .arraySize | .arrayIsEmpty | .arrayPush | .arrayAppend | .arrayReverse
  | .arrayToList | .arrayOfList => none

/-- Exactly `bool.and` is spelled `&&`. -/
theorem Opcode.eq_boolAnd_of_operator? {code : Opcode}
    (spelled : code.operator? = some .logicalAnd) : code = .boolAnd := by
  cases code <;> simp_all [Opcode.operator?]

/-- Exactly `bool.or` is spelled `||`. -/
theorem Opcode.eq_boolOr_of_operator? {code : Opcode}
    (spelled : code.operator? = some .logicalOr) : code = .boolOr := by
  cases code <;> simp_all [Opcode.operator?]

/-- Exactly `bool.not` is spelled `!`. -/
theorem Opcode.eq_boolNot_of_operator? {code : Opcode}
    (spelled : code.operator? = some .logicalNot) : code = .boolNot := by
  cases code <;> simp_all [Opcode.operator?]

/-- Exactly `bool.equals` is spelled `===`. -/
theorem Opcode.eq_boolEquals_of_operator? {code : Opcode}
    (spelled : code.operator? = some .strictEquals) : code = .boolEquals := by
  cases code <;> simp_all [Opcode.operator?]

/--
Whether the opcode carries a callback operand the emitted form enters once per element.

The six higher-order list opcodes do: `value.map((element) => transform(element))` enters a real
function object, which costs fuel and records an entry. Every other opcode is first-order and
denotes one engine operation at no fuel and no trace cost. The two kinds are proved differently, so
the registry names the distinction rather than leaving it to be read off a proof.
-/
def Opcode.callback : Opcode → Bool
  | .listMap | .listFilter | .listFoldLeft | .listFoldRight | .listAny | .listAll => true
  | .boolAnd | .boolOr | .boolNot | .boolEquals | .natAdd | .natSubtract | .natMultiply | .natLess
  | .natLessOrEqual | .natEquals | .natSuccessor | .stringAppend | .stringEquals | .listLength
  | .listIsEmpty | .listAppend | .listReverse | .listHead | .listFirst | .listRest | .intAdd
  | .intSubtract | .intMultiply | .intNegate | .intTruncatedDivide | .intTruncatedModulo
  | .intLess | .intLessOrEqual | .intEquals | .intOfNat | .intToNat | .charToNat | .charOfNat
  | .charEquals | .charLess | .stringLength | .stringIsEmpty | .stringPush | .stringSingleton
  | .stringToList | .stringOfList | .arraySize | .arrayIsEmpty | .arrayPush
  | .arrayAppend | .arrayReverse | .arrayToList | .arrayOfList => false


/-! ## The host-effect registry

A `HostEffect` reaches the target as a call to a substrate function the emitted module imports. The
call itself is an ordinary `call` to a declared name — effects are store passing, so a host call is a
function of its payload and the store and nothing else — and this registry is what fixes the
*identity* of the host operation the name stands for.

The spellings are shared with `AgentCore.Substrate.Opcode.wire`, which is a separate Lean library in
a separate repository; the two are joined by `spec/semantics/registry.json` and the substrate
contract gate rather than by an import, so neither library depends on the other's build.
-/

/-- The closed set of host operations the substrate seam exposes. -/
inductive HostOp where
  | storeGet
  | storePut
  | storeDelete
  | storeList
  | storeTxn
  | alarmSet
  | alarmGet
  | alarmDelete
  | contentPut
  | contentGet
  | contentHead
  | contentRange
  | queueSend
  | queueAck
  | queueRetry
  | isolateLoad
  | isolateCall
  | rpcCall
  | rpcDispose
  deriving DecidableEq, Repr

/-- The wire spelling the IR carries, and the name the emitted module imports. -/
def HostOp.wire : HostOp → String
  | .storeGet => "host.store.get"
  | .storePut => "host.store.put"
  | .storeDelete => "host.store.delete"
  | .storeList => "host.store.list"
  | .storeTxn => "host.store.txn"
  | .alarmSet => "host.alarm.set"
  | .alarmGet => "host.alarm.get"
  | .alarmDelete => "host.alarm.delete"
  | .contentPut => "host.content.put"
  | .contentGet => "host.content.get"
  | .contentHead => "host.content.head"
  | .contentRange => "host.content.range"
  | .queueSend => "host.queue.send"
  | .queueAck => "host.queue.ack"
  | .queueRetry => "host.queue.retry"
  | .isolateLoad => "host.isolate.load"
  | .isolateCall => "host.isolate.call"
  | .rpcCall => "host.rpc.call"
  | .rpcDispose => "host.rpc.dispose"

/-- Every admitted host operation. -/
def HostOp.all : List HostOp :=
  [ .storeGet, .storePut, .storeDelete, .storeList, .storeTxn, .alarmSet, .alarmGet, .alarmDelete,
    .contentPut, .contentGet, .contentHead, .contentRange, .queueSend, .queueAck, .queueRetry,
    .isolateLoad, .isolateCall, .rpcCall, .rpcDispose]

theorem HostOp.mem_all (host : HostOp) : host ∈ HostOp.all := by
  cases host <;> simp [HostOp.all]

/-- Distinct host operations have distinct wire spellings, so the join against the substrate
contract is a bijection. -/
theorem HostOp.wire_injective {left right : HostOp} (equal : left.wire = right.wire) :
    left = right := by
  cases left <;> cases right <;> simp_all [HostOp.wire]

/-! ## The recursion discipline

Which discipline Lean proved for a definition. The source semantics ignores it: `enter` resolves a
callee by name against the whole program, so mutual and well-founded recursion already terminate
under the fuel machine model and need no new machinery. The field is what lets the emitter choose a
legal emission order — a mutual group has to be emitted as hoisted `function` declarations, because a
`const` arrow is not initialised when its sibling refers to it — and what lets the gate check that it
did.
-/

/-- The recursion discipline Lean proved for a definition. -/
inductive Recursion where
  /-- Not recursive. -/
  | nonrecursive
  /-- Structurally recursive on the parameter at this index. -/
  | structural (parameter : Nat)
  /-- Well founded on a measure Lean discharged; the exporter read the equational form. -/
  | wellFounded
  /-- One member of a mutual block, which lists every member in Lean's declaration order. -/
  | mutualGroup (group : List String)
  deriving DecidableEq, Repr

/-- The wire spelling `Export.lean` writes and `ir.ts` decodes. -/
def Recursion.kind : Recursion → String
  | .nonrecursive => "none"
  | .structural _ => "structural"
  | .wellFounded => "wellFounded"
  | .mutualGroup _ => "mutual"

/-- Every admitted recursion discipline, at a witness for each payload. -/
def Recursion.allKinds : List String := ["none", "structural", "wellFounded", "mutual"]

/-- The four disciplines spell the four wire kinds. -/
theorem Recursion.kind_mem (recursion : Recursion) : recursion.kind ∈ Recursion.allKinds := by
  cases recursion <;> simp [Recursion.kind, Recursion.allKinds]

/-- The members of the mutual block a definition belongs to, and none for every other
discipline. -/
def Recursion.group : Recursion → List String
  | .mutualGroup group => group
  | .nonrecursive | .structural _ | .wellFounded => []

/-- One declared field: its emitted property key and its type. -/
structure Field where
  name : String
  type : Ty
  deriving DecidableEq, Repr

/-- An expression of the admitted fragment, in Coverage v5's fourteen forms. Variables are de Bruijn
indices into the enclosing scope, innermost binder first, exactly as `Export.lean` writes them.

There is no separate `some`, `none`, `and`, `or`, `not` or `equals` form. `Option`, `Except` and
`List` values are built by `variant` at their mapped type, and the boolean operators are `operation`
rows, so one construction form and one opcode registry cover what v4 spread across six. -/
inductive Expr where
  /-- `variable`: de Bruijn reference into the enclosing scope. -/
  | varRef (index : Nat)
  /-- `boolean`: a `Bool` literal. -/
  | boolLit (value : Bool)
  /-- `nat`: a `Nat` literal. The wire carries decimal digits so an arbitrary-precision value
  survives the IR; the model carries the `Nat` those digits denote. -/
  | natLit (value : Nat)
  /-- `string`: a `String` literal. -/
  | stringLit (value : String)
  /-- `let`: a named binding whose body sees it at index `0`. -/
  | letBind (name : String) (value : Expr) (body : Expr)
  /-- `field`: a declared record or constructor field read. -/
  | fieldGet (target : Expr) (field : String)
  /-- `if`: a `Bool`-decided conditional. -/
  | ifThenElse (condition consequent alternate : Expr)
  /-- `operation`: one runtime opcode applied to its type and value arguments. -/
  | operation (opcode : Opcode) (typeArguments : List Ty) (arguments : List Expr)
  /-- `variant`: a constructor of the scrutinised type applied to its declared fields. The type is
  a `Ty`, not a name, because `Option`, `Except` and `List` carry constructors without being
  declarations. -/
  | variant (type : Ty) (name : String) (arguments : List Expr)
  /-- `record`: a structure constructor applied to its declared fields. -/
  | record (type : Ty) (fields : List (String × Expr))
  /-- `match`: a total case analysis over one type, one arm per constructor. -/
  | matchOn (type : Ty) (scrutinee : Expr) (cases : List (String × Expr))
  /-- `lambda`: an inline arrow with the exact parameter list and body Coverage v5 decodes. -/
  | lambda (parameters : List Field) (body : Expr)
  /-- `apply`: an application of an arrow value to its arguments. -/
  | apply (callee : Expr) (arguments : List Expr)
  /-- `call`: an application of a declared function to its declared parameters. -/
  | call (function : String) (typeArguments : List Ty) (arguments : List Expr)
  deriving Repr

/-- The fourteen expression forms the fragment admits, as a closed registry. Every preservation
theorem is indexed by this type, so a new form cannot reach the compiler without one. -/
inductive Op where
  | varRef
  | boolLit
  | natLit
  | stringLit
  | letBind
  | fieldGet
  | ifThenElse
  | operation
  | variant
  | record
  | matchOn
  | lambda
  | apply
  | call
  deriving DecidableEq, Repr

/-- The wire spelling `Export.lean` writes and `ir.ts` decodes. -/
def Op.kind : Op → String
  | .varRef => "variable"
  | .boolLit => "boolean"
  | .natLit => "nat"
  | .stringLit => "string"
  | .letBind => "let"
  | .fieldGet => "field"
  | .ifThenElse => "if"
  | .operation => "operation"
  | .variant => "variant"
  | .record => "record"
  | .matchOn => "match"
  | .lambda => "lambda"
  | .apply => "apply"
  | .call => "call"

/-- Every admitted expression form. -/
def Op.all : List Op :=
  [.varRef, .boolLit, .natLit, .stringLit, .letBind, .fieldGet, .ifThenElse, .operation, .variant,
    .record, .matchOn, .lambda, .apply, .call]

theorem Op.mem_all (op : Op) : op ∈ Op.all := by
  cases op <;> simp [Op.all]

/-- Distinct operations have distinct wire spellings, so the registry join is a bijection. -/
theorem Op.kind_injective {left right : Op} (equal : left.kind = right.kind) : left = right := by
  cases left <;> cases right <;> simp_all [Op.kind]

/-- The registry entry an expression belongs to. -/
def Expr.op : Expr → Op
  | .varRef _ => .varRef
  | .boolLit _ => .boolLit
  | .natLit _ => .natLit
  | .stringLit _ => .stringLit
  | .letBind _ _ _ => .letBind
  | .fieldGet _ _ => .fieldGet
  | .ifThenElse _ _ _ => .ifThenElse
  | .operation _ _ _ => .operation
  | .variant _ _ _ => .variant
  | .record _ _ => .record
  | .matchOn _ _ _ => .matchOn
  | .lambda _ _ => .lambda
  | .apply _ _ => .apply
  | .call _ _ _ => .call

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
  | .varRef _ | .boolLit _ | .natLit _ | .stringLit _ => []
  | .letBind _ value body => [value, body]
  | .fieldGet target _ => [target]
  | .ifThenElse condition consequent alternate => [condition, consequent, alternate]
  | .operation _ _ arguments => arguments
  | .variant _ _ arguments => arguments
  | .record _ fields => fields.map Prod.snd
  | .matchOn _ scrutinee cases => scrutinee :: cases.map Prod.snd
  | .lambda _ body => [body]
  | .apply callee arguments => callee :: arguments
  | .call _ _ arguments => arguments

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
  /-- `record`: a structure with declared fields in declaration order. `constructor` names the Lean
  constructor a match on the structure decides. -/
  | record (name : String) (constructor : String) (fields : List Field)
  /-- `function`: a first-order definition. `recursion` records the discipline Lean proved, which
  the emitter needs to choose a legal emission order for a mutual block. -/
  | function (name : String) (parameters : List Field) (result : Ty)
      (recursion : Recursion) (body : Expr)
  /--
  `foreign`: a host-effect boundary.

  The emitted module imports the substrate's implementation of `host` under this name. `reference`
  is the exported reference implementation of that operation, in IR, and is what the model runs on
  both sides. The gap between the two — that the substrate's implementation computes what the
  reference computes — is the named premise `Program.HostSubstrate`, discharged by one substrate
  conformance row per host operation. It is a hypothesis, never an axiom, and nothing in this
  library proves it.
  -/
  | foreign (name : String) (host : HostOp) (parameters : List Field) (result : Ty)
      (reference : Expr)
  deriving Repr

/-- The three declaration families the fragment admits, as a closed registry. -/
inductive Family where
  | enum
  | record
  | function
  | foreign
  deriving DecidableEq, Repr

/-- The wire spelling `Export.lean` writes and `ir.ts` decodes. -/
def Family.kind : Family → String
  | .enum => "enum"
  | .record => "record"
  | .function => "function"
  | .foreign => "foreign"

/-- Every admitted declaration family. -/
def Family.all : List Family := [.enum, .record, .function, .foreign]

theorem Family.mem_all (family : Family) : family ∈ Family.all := by
  cases family <;> simp [Family.all]

/-- Distinct families have distinct wire spellings. -/
theorem Family.kind_injective {left right : Family} (equal : left.kind = right.kind) :
    left = right := by
  cases left <;> cases right <;> simp_all [Family.kind]

/-- The registry entry a declaration belongs to. -/
def Decl.family : Decl → Family
  | .enum _ _ => .enum
  | .record _ _ _ => .record
  | .function _ _ _ _ _ => .function
  | .foreign _ _ _ _ _ => .foreign

/-- The declared name of a declaration. -/
def Decl.name : Decl → String
  | .enum name _ | .record name _ _ | .function name _ _ _ _ | .foreign name _ _ _ _ => name

/-- The host operation a declaration is the boundary for, and `none` for every other family. -/
def Decl.host? : Decl → Option HostOp
  | .foreign _ host _ _ _ => some host
  | .enum _ _ | .record _ _ _ | .function _ _ _ _ _ => none

/-- Exactly a `foreign` declaration names a host operation. -/
theorem Decl.host?_isSome_iff (declaration : Decl) :
    declaration.host?.isSome = true ↔ declaration.family = .foreign := by
  cases declaration <;> simp [Decl.host?, Decl.family]

/-- One compilation unit: the declarations reachable from the exported roots. -/
structure Program where
  declarations : List Decl
  deriving Repr

/-- The declaration carrying a name, if the program declares it. -/
def Program.find? (program : Program) (name : String) : Option Decl :=
  program.declarations.find? fun declaration => declaration.name == name

mutual

/-- Substitutes a type's own arguments for the `parameter` indices a declaration left open. An index
the argument list does not reach stays open, which the compiler then refuses rather than guesses. -/
def Ty.substitute (arguments : List Ty) : Ty → Ty
  | .boolean => .boolean
  | .nat => .nat
  | .string => .string
  | .int => .int
  | .char => .char
  | .bytes => .bytes
  | .json => .json
  | .parameter index => (arguments[index]?).getD (.parameter index)
  | .named name inner => .named name (Ty.substituteList arguments inner)
  | .option value => .option (Ty.substitute arguments value)
  | .except error value => .except (Ty.substitute arguments error) (Ty.substitute arguments value)
  | .list element => .list (Ty.substitute arguments element)
  | .array element => .array (Ty.substitute arguments element)
  | .pair first second =>
      .pair (Ty.substitute arguments first) (Ty.substitute arguments second)
  | .hashMap key value =>
      .hashMap (Ty.substitute arguments key) (Ty.substitute arguments value)
  | .treeMap key value =>
      .treeMap (Ty.substitute arguments key) (Ty.substitute arguments value)
  | .function parameters result =>
      .function (Ty.substituteList arguments parameters) (Ty.substitute arguments result)

def Ty.substituteList (arguments : List Ty) : List Ty → List Ty
  | [] => []
  | head :: rest => Ty.substitute arguments head :: Ty.substituteList arguments rest

end

/-- One constructor's fields, instantiated at the scrutinised type's own arguments. -/
def substituteFields (arguments : List Ty) (fields : List Field) : List Field :=
  fields.map fun field => { field with type := field.type.substitute arguments }

/-- The function declaration carrying a name. -/
def Program.function? (program : Program) (name : String) :
    Option (List Field × Ty × Recursion × Expr) :=
  match program.find? name with
  | some (.function _ parameters result recursion body) =>
      some (parameters, result, recursion, body)
  | some (.foreign _ _ parameters result reference) =>
      some (parameters, result, .nonrecursive, reference)
  | _ => none

/-- The host operations a program declares boundaries for, in declaration order. -/
def Program.hosts (program : Program) : List HostOp :=
  program.declarations.filterMap Decl.host?

/--
The constructors of a type, instantiated at that type's own arguments, mirroring `constructorsOf`
in `ir.ts`. A mapped Lean type carries the constructor set its TypeScript representation carries,
which is why `option`, `except` and `list` are decided by exactly the machinery a user inductive
uses rather than by three special forms.

`none` means the type is not destructurable. `nat` is deliberately among those: Lean compiles a `0`
pattern to an `OfNat` literal rather than to `Nat.zero`, so a `Nat` is decided with the comparison
opcodes instead of taken apart.
-/
def Program.constructorsOf (program : Program) : Ty → Option (List Constructor)
  | .option value => some [⟨"none", []⟩, ⟨"some", [⟨"value", value⟩]⟩]
  | .except error value => some [⟨"error", [⟨"error", error⟩]⟩, ⟨"ok", [⟨"value", value⟩]⟩]
  | .list element =>
      some [⟨"nil", []⟩, ⟨"cons", [⟨"head", element⟩, ⟨"tail", .list element⟩]⟩]
  | .pair first second => some [⟨"mk", [⟨"fst", first⟩, ⟨"snd", second⟩]⟩]
  | .json =>
      some [⟨"null", []⟩, ⟨"bool", [⟨"value", .boolean⟩]⟩, ⟨"int", [⟨"value", .int⟩]⟩,
        ⟨"string", [⟨"value", .string⟩]⟩, ⟨"array", [⟨"value", .list .json⟩]⟩,
        ⟨"object", [⟨"value", .list (.pair .string .json)⟩]⟩]
  | .named name arguments =>
      match program.find? name with
      | some (.enum _ constructors) =>
          some (constructors.map fun declared =>
            ⟨declared.name, substituteFields arguments declared.fields⟩)
      | some (.record _ constructor fields) =>
          some [⟨constructor, substituteFields arguments fields⟩]
      | _ => none
  | .boolean | .nat | .string | .parameter _ | .function _ _ | .int | .char | .bytes
  | .array _ | .hashMap _ _ | .treeMap _ _ => none

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
