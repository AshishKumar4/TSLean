import TSLean.LeanToTypeScript.Semantics.Opcode
import TSLean.LeanToTypeScript.Semantics.Program

/-!
# Registry closure tests

Executable checks over the three closed registries and the assumption plane. `#guard` fails the
build when its expression does not reduce to `true`, so these are elaboration-time tests rather than
a separate runner. Nothing here uses `native_decide`, so nothing here adds an axiom.
-/

namespace TSLean.LeanToTypeScript.Semantics

namespace Tests

open Ir Assumption

/-! ## The IR expression registry -/

-- Fourteen expression operations, and every one of them enumerated.
#guard Op.all.length = 14

-- The enumeration has no repeats.
#guard Op.all.Nodup

-- Every enumerated operation spells a distinct wire kind.
#guard (Op.all.map Op.kind).Nodup

-- The wire spellings are exactly the ones `src/lean-to-typescript/ir.ts` decodes.
#guard Op.all.map Op.kind =
  ["variable", "boolean", "nat", "string", "let", "field", "if", "operation", "variant", "record",
    "match", "lambda", "apply", "call"]

-- Three declaration families, spelled as the decoder spells them.
#guard Family.all.map Family.kind = ["enum", "record", "function"]

-- Nine type forms, and every one of them enumerated.
#guard TyKind.all.length = 9

-- The enumeration has no repeats, and spells the kinds the decoder decodes.
#guard TyKind.all.Nodup
#guard TyKind.all.map TyKind.kind =
  ["boolean", "nat", "string", "parameter", "named", "option", "except", "list", "function"]

-- Every expression form reports the registry entry it belongs to.
#guard [Expr.op (.varRef 0), Expr.op (.boolLit true), Expr.op (.natLit 0),
    Expr.op (.stringLit ""), Expr.op (.letBind "x" (.natLit 0) (.natLit 0)),
    Expr.op (.fieldGet (.varRef 0) "f"),
    Expr.op (.ifThenElse (.boolLit true) (.natLit 0) (.natLit 1)),
    Expr.op (.operation .natAdd [] []), Expr.op (.variant .boolean "C" []),
    Expr.op (.record (.named "R" []) []), Expr.op (.matchOn .boolean (.varRef 0) []),
    Expr.op (.lambda [] (.natLit 0)), Expr.op (.apply (.varRef 0) []),
    Expr.op (.call "f" [] [])] = Op.all

-- Every type form reports the registry entry it belongs to.
#guard [Ty.kind .boolean, Ty.kind .nat, Ty.kind .string, Ty.kind (.parameter 0),
    Ty.kind (.named "T" []), Ty.kind (.option .boolean), Ty.kind (.except .boolean .boolean),
    Ty.kind (.list .boolean), Ty.kind (.function [] .boolean)] = TyKind.all

-- Exactly the `list` form holds an element type, which is what decides a dense-array representation
-- on the source side and on the lowering side alike.
#guard [(Ty.boolean : Ty).element?.isSome, (Ty.nat : Ty).element?.isSome,
    (Ty.string : Ty).element?.isSome, (Ty.parameter 0).element?.isSome,
    (Ty.named "T" []).element?.isSome, (Ty.option .boolean).element?.isSome,
    (Ty.except .boolean .boolean).element?.isSome, (Ty.list .boolean).element?.isSome,
    (Ty.function [] .boolean).element?.isSome] =
  [false, false, false, false, false, false, false, true, false]

-- An arrow object's own keys are exactly its captured binders, in scope order. The inline code is
-- semantic provenance in the closure payload and trace, not a second heap/table identity.
#guard (Ir.closureEntries []).map Prod.fst = []
#guard (Ir.closureEntries [.primitive .undefined, .primitive .null]).map Prod.fst =
  ["$captured0", "$captured1"]

/-! ## The runtime opcode registry -/

-- Twenty-six runtime opcodes, and every one of them enumerated.
#guard Opcode.all.length = 26

-- The enumeration has no repeats.
#guard Opcode.all.Nodup

-- Every opcode spells a distinct wire kind.
#guard (Opcode.all.map Opcode.kind).Nodup

-- The wire spellings are exactly the ones the exporter emits.
#guard Opcode.all.map Opcode.kind =
  ["bool.and", "bool.or", "bool.not", "bool.equals", "nat.add", "nat.subtract", "nat.multiply",
    "nat.less", "nat.lessOrEqual", "nat.equals", "nat.successor", "string.append", "string.equals",
    "list.length", "list.isEmpty", "list.append", "list.reverse", "list.map", "list.filter",
    "list.foldLeft", "list.foldRight", "list.any", "list.all", "list.head", "list.first",
    "list.rest"]

-- Every opcode records the TypeScript it lowers to.
#guard Opcode.all.all fun code => code.emittedForm ≠ ""

-- Every runtime symbol is tagged by how it reaches the target: an inline form or a generated helper.
#guard Opcode.all.all fun code =>
  code.runtimeSymbol.startsWith "inline:" || code.runtimeSymbol.startsWith "helper:"

-- The tag a symbol carries is one of exactly those two.
#guard Opcode.all.all fun code =>
  code.runtimeSymbolTag == "inline:" || code.runtimeSymbolTag == "helper:"

-- Exactly the generated helpers record the semantic components they compose; an inline form has
-- none, because there is no helper body to certify.
#guard Opcode.all.all fun code =>
  (code.components ≠ []) == (code.runtimeSymbolTag == "helper:")

-- Two opcodes are generated helpers, and they are the two whose emitted form is a guarded
-- composition rather than one operator or one method.
#guard (Opcode.all.filter fun code => code.runtimeSymbolTag == "helper:").map Opcode.kind =
  ["nat.subtract", "list.head"]

-- An inline symbol names the opcode it is the emitted form of, which is what makes the join against
-- `LEAN_RUNTIME_OPCODES` in `src/lean-to-typescript/ir.ts` a bijection rather than a lookup.
#guard Opcode.all.all fun code =>
  code.runtimeSymbolTag != "inline:" || code.runtimeSymbol == "inline:" ++ code.kind

-- Exactly four opcodes reach the target as operators, so exactly four are refused as operation
-- calls, and each records the operand count its operator form takes.
#guard (Opcode.all.filter fun code => code.operator?.isSome).map Opcode.kind =
  ["bool.and", "bool.or", "bool.not", "bool.equals"]
#guard Opcode.all.filterMap (fun code => code.operator?.map OperatorForm.operands) = [2, 2, 1, 2]

-- Exactly six opcodes carry a callback operand, and no opcode is both an operator and a callback:
-- the two kinds are proved differently, so they cannot overlap.
#guard (Opcode.all.filter fun code => code.callback).map Opcode.kind =
  ["list.map", "list.filter", "list.foldLeft", "list.foldRight", "list.any", "list.all"]
#guard Opcode.all.all fun code => !(code.callback && code.operator?.isSome)

-- Every opcode names at least one assumption: none of them is discharged from nothing.
#guard Opcode.all.all fun code => code.requires ≠ []

-- Every assumption an opcode names is one the plane declares.
#guard Opcode.all.all fun code => code.requires.all fun id => Id.all.contains id

-- Every declared assumption is named by at least one opcode, so the plane carries no dead assumption.
#guard Id.all.all fun id => Opcode.all.any fun code => code.requires.contains id

/-! ## The assumption plane -/

-- Nine assumptions, and every one of them enumerated.
#guard Id.all.length = 9

-- The enumeration has no repeats.
#guard Id.all.Nodup

-- Every assumption has a distinct stable identity.
#guard (Id.all.map Id.name).Nodup

-- The stable identities are the ones catalog rows key on.
#guard Id.all.map Id.name =
  ["boolean.logical-operators", "strict-equality.same-type", "bigint.exact-arithmetic",
    "bigint.relational", "conditional.truthy-selection", "string.utf16-concatenation",
    "array.dense-element-sequence", "bigint.from-length", "option.tagged-object"]

-- Every assumption records all four provenance fields.
#guard Id.all.all fun id =>
  id.provenance.clauses ≠ [] && id.provenance.statement ≠ "" && id.provenance.oracle ≠ "" &&
    id.provenance.coverage ≠ [] && Assumption.source.url ≠ "" && Assumption.source.artifact ≠ "" &&
    Assumption.source.digest.startsWith "sha256:" && Assumption.source.digest.length == 71

-- Every assumption names the executed probe group that measures it, and the group is its own id.
#guard Id.all.all fun id => id.provenance.oracle == "semantics-probes/" ++ id.name

-- Distinct assumptions have distinct canonical wordings.
#guard (Id.all.map Id.canonicalWording).Nodup

/-! ## Closure -/

/--
The proof registry is closed over the opcode registry: `Opcode.registry` is a total function on
`Ir.Opcode`, so this instantiation typechecks for every opcode and would fail to elaborate for one
with no theorem.
-/
theorem opcode_registry_closed (runtime : Runtime) :
    ∀ code : Ir.Opcode, Assumption.Holds runtime code.requires → code.Preserves runtime :=
  fun code => Opcode.registry runtime code

/--
The proof registry is closed over the IR expression registry: `Preservation.registry` is a total
function on `Ir.Op`, so this instantiation typechecks for every operation and would fail to elaborate
for one with no theorem.
-/
theorem expression_registry_closed (runtime : Runtime) :
    ∀ op : Ir.Op, Preservation.Op.Preserves runtime op := Preservation.registry runtime

/-- The proof registry is closed over the declaration-family registry. -/
theorem family_registry_closed (runtime : Runtime) :
    ∀ family : Ir.Family, Preservation.Family.Preserves runtime family :=
  Preservation.familyRegistry runtime

/--
The whole-program theorem discharges every hypothesis the per-operation theorems take, from three
premises: the program's lowering, the engine's recorded assumption closures, and ECMAScript's
array-length cap.
-/
theorem whole_program_closed {program : Ir.Program} {target : Target.Program} {runtime : Runtime}
    (lowered : Preservation.LoweredProgram program target)
    (laws : Preservation.RuntimeLaws runtime) (listsFit : Preservation.ListsFit program) :
    (∀ fuel expression emitted, Compile.expr program expression = .ok emitted →
        Preservation.Everywhere program target runtime fuel expression emitted) ∧
      (∀ fuel body emitted, Compile.body program body = .ok emitted →
        Preservation.EverywhereBody program target runtime fuel body emitted) :=
  ⟨fun fuel => Preservation.everywhere lowered laws listsFit fuel,
    fun fuel => Preservation.everywhereBody lowered laws listsFit fuel⟩

/-- The three example-critical opcodes are discharged from the one assumption they name. -/
theorem example_critical_opcodes (runtime : Runtime)
    (holds : (Assumption.Id.booleanLogicalOperators).statement runtime) :
    Ir.Opcode.boolAnd.Preserves runtime ∧ Ir.Opcode.boolOr.Preserves runtime ∧
      Ir.Opcode.boolNot.Preserves runtime :=
  ⟨Opcode.registry runtime .boolAnd ⟨holds, trivial⟩,
    Opcode.registry runtime .boolOr ⟨holds, trivial⟩,
    Opcode.registry runtime .boolNot ⟨holds, trivial⟩⟩

end Tests

end TSLean.LeanToTypeScript.Semantics
