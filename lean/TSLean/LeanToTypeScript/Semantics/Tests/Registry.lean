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

open Ir Opcode Assumption

/-! ## The IR expression registry -/

-- Seventeen expression operations, and every one of them enumerated.
#guard Op.all.length = 17

-- The enumeration has no repeats.
#guard Op.all.Nodup

-- Every enumerated operation spells a distinct wire kind.
#guard (Op.all.map Op.kind).Nodup

-- The wire spellings are exactly the ones `src/lean-to-typescript/ir.ts` decodes.
#guard Op.all.map Op.kind =
  ["variable", "boolean", "let", "field", "if", "equals", "and", "or", "not", "some", "none",
    "variant", "record", "match", "call", "lambda", "apply"]

-- Three declaration families, spelled as the decoder spells them.
#guard Family.all.map Family.kind = ["enum", "record", "function"]

-- Three type forms, spelled as the decoder spells them.
#guard TyKind.all.map TyKind.kind = ["boolean", "option", "named"]

-- Every expression form reports the registry entry it belongs to.
#guard [Expr.op (.varRef 0), Expr.op (.boolLit true), Expr.op (.letBind "x" .noneValue .noneValue),
    Expr.op (.fieldGet .noneValue "f"), Expr.op (.ifThenElse .noneValue .noneValue .noneValue),
    Expr.op (.boolEquals .noneValue .noneValue), Expr.op (.boolAnd .noneValue .noneValue),
    Expr.op (.boolOr .noneValue .noneValue), Expr.op (.boolNot .noneValue),
    Expr.op (.someValue .noneValue), Expr.op .noneValue, Expr.op (.variant "T" "C" []),
    Expr.op (.record "R" []), Expr.op (.matchOn "T" .noneValue []),
    Expr.op (.call "f" []), Expr.op (.lambda [] .noneValue),
    Expr.op (.apply (.varRef 0) [])] = Op.all

-- An arrow object's own keys are exactly its captured binders, in scope order. The inline code is
-- semantic provenance in the closure payload and trace, not a second heap/table identity.
#guard (Ir.closureEntries []).map Prod.fst = []
#guard (Ir.closureEntries [.primitive .undefined, .primitive .null]).map Prod.fst =
  ["$captured0", "$captured1"]

/-! ## The runtime opcode registry -/

-- Twenty-six runtime opcodes, and every one of them enumerated.
#guard Code.all.length = 26

-- The enumeration has no repeats.
#guard Code.all.Nodup

-- Every opcode spells a distinct wire kind.
#guard (Code.all.map Code.kind).Nodup

-- The wire spellings are exactly the ones the exporter emits.
#guard Code.all.map Code.kind =
  ["bool.and", "bool.or", "bool.not", "bool.equals", "nat.add", "nat.subtract", "nat.multiply",
    "nat.less", "nat.lessOrEqual", "nat.equals", "nat.successor", "string.append", "string.equals",
    "list.length", "list.isEmpty", "list.append", "list.reverse", "list.map", "list.filter",
    "list.foldLeft", "list.foldRight", "list.any", "list.all", "list.head", "list.first",
    "list.rest"]

-- Every opcode records the TypeScript it lowers to.
#guard Code.all.all fun code => code.emittedForm ≠ ""

-- Every opcode names at least one assumption: none of them is discharged from nothing.
#guard Code.all.all fun code => code.requires ≠ []

-- Every assumption an opcode names is one the plane declares.
#guard Code.all.all fun code => code.requires.all fun id => Id.all.contains id

-- Every declared assumption is named by at least one opcode, so the plane carries no dead assumption.
#guard Id.all.all fun id => Code.all.any fun code => code.requires.contains id

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
`Code`, so this instantiation typechecks for every opcode and would fail to elaborate for one with
no theorem.
-/
theorem opcode_registry_closed (runtime : Runtime) :
    ∀ code : Code, Assumption.Holds runtime code.requires → code.Preserves runtime :=
  fun code => Opcode.registry runtime code

/--
The proof registry is closed over the IR expression registry: `Preservation.registry` is a total
function on `Ir.Op`, so this instantiation typechecks for every operation and would fail to elaborate
for one with no theorem.
-/
theorem expression_registry_closed : ∀ op : Ir.Op, Preservation.Op.Preserves op :=
  Preservation.registry

/-- The proof registry is closed over the declaration-family registry. -/
theorem family_registry_closed : ∀ family : Ir.Family, Preservation.Family.Preserves family :=
  Preservation.familyRegistry

/--
The whole-program theorem discharges every hypothesis the per-operation theorems take, from one
premise about the program and its lowering.
-/
theorem whole_program_closed {program : Ir.Program} {target : Target.Program}
    (lowered : Preservation.LoweredProgram program target) :
    (∀ fuel expression emitted, Compile.expr program expression = .ok emitted →
        Preservation.Everywhere program target fuel expression emitted) ∧
      (∀ fuel body emitted, Compile.body program body = .ok emitted →
        Preservation.EverywhereBody program target fuel body emitted) :=
  ⟨fun fuel => Preservation.everywhere lowered fuel,
    fun fuel => Preservation.everywhereBody lowered fuel⟩

/-- The three example-critical opcodes are discharged from the one assumption they name. -/
theorem example_critical_opcodes (runtime : Runtime)
    (holds : (Assumption.Id.booleanLogicalOperators).statement runtime) :
    Code.boolAnd.Preserves runtime ∧ Code.boolOr.Preserves runtime ∧
      Code.boolNot.Preserves runtime :=
  ⟨Opcode.registry runtime .boolAnd ⟨holds, trivial⟩,
    Opcode.registry runtime .boolOr ⟨holds, trivial⟩,
    Opcode.registry runtime .boolNot ⟨holds, trivial⟩⟩

end Tests

end TSLean.LeanToTypeScript.Semantics
