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

-- Seventeen type forms, and every one of them enumerated.
#guard TyKind.all.length = 17

-- The enumeration has no repeats, and spells the kinds the decoder decodes.
#guard TyKind.all.Nodup
#guard TyKind.all.map TyKind.kind =
  ["boolean", "nat", "string", "parameter", "named", "option", "except", "list", "function", "int",
    "char", "bytes", "json", "array", "pair", "hashMap", "treeMap"]

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
    Ty.kind (.list .boolean), Ty.kind (.function [] .boolean), Ty.kind .int, Ty.kind .char,
    Ty.kind .bytes, Ty.kind .json, Ty.kind (.array .boolean), Ty.kind (.pair .boolean .nat),
    Ty.kind (.hashMap .nat .boolean), Ty.kind (.treeMap .nat .boolean)] = TyKind.all

-- Exactly the `list` form holds an element type, which is what decides a dense-array representation
-- on the source side and on the lowering side alike.
#guard [(Ty.boolean : Ty).element?.isSome, (Ty.nat : Ty).element?.isSome,
    (Ty.string : Ty).element?.isSome, (Ty.parameter 0).element?.isSome,
    (Ty.named "T" []).element?.isSome, (Ty.option .boolean).element?.isSome,
    (Ty.except .boolean .boolean).element?.isSome, (Ty.list .boolean).element?.isSome,
    (Ty.function [] .boolean).element?.isSome, (Ty.int : Ty).element?.isSome,
    (Ty.char : Ty).element?.isSome, (Ty.bytes : Ty).element?.isSome,
    (Ty.json : Ty).element?.isSome, (Ty.array .boolean).element?.isSome,
    (Ty.pair .boolean .nat).element?.isSome, (Ty.hashMap .nat .boolean).element?.isSome,
    (Ty.treeMap .nat .boolean).element?.isSome] =
  [false, false, false, false, false, false, false, true, false, false, false, false, false, false,
    false, false, false]

-- An `Array` shares the dense-array image with a `List` but is a distinct type form, and it is not
-- destructurable: its values are decided with the `array.*` opcodes, never taken apart by a match.
#guard (Ty.array .nat) ≠ (Ty.list .nat)
#guard ((⟨[]⟩ : Ir.Program).constructorsOf (.array .nat)).isNone
#guard ((⟨[]⟩ : Ir.Program).constructorsOf (.hashMap .nat .boolean)).isNone
#guard ((⟨[]⟩ : Ir.Program).constructorsOf (.treeMap .nat .boolean)).isNone
#guard ((⟨[]⟩ : Ir.Program).constructorsOf .int).isNone
#guard ((⟨[]⟩ : Ir.Program).constructorsOf .char).isNone
#guard ((⟨[]⟩ : Ir.Program).constructorsOf .bytes).isNone

-- A pair is a mapped Lean structure: one constructor, own keys `fst` then `snd`, so it reaches the
-- target through exactly the record machinery rather than a tenth expression form.
#guard ((⟨[]⟩ : Ir.Program).constructorsOf (.pair .nat .string)).map
    (fun constructors => constructors.map fun constructor =>
      (constructor.name, constructor.fields.map Ir.Field.name))
  = some [("mk", ["fst", "snd"])]

-- `JsonValue` is a mapped Lean inductive carrying the six constructors its union image carries.
#guard ((⟨[]⟩ : Ir.Program).constructorsOf .json).map
    (fun constructors => constructors.map Ir.Constructor.name)
  = some ["null", "bool", "int", "string", "array", "object"]

-- An arrow object's own keys are exactly its captured binders, in scope order. The inline code is
-- semantic provenance in the closure payload and trace, not a second heap/table identity.
#guard (Ir.closureEntries []).map Prod.fst = []
#guard (Ir.closureEntries [.primitive .undefined, .primitive .null]).map Prod.fst =
  ["$captured0", "$captured1"]

/-! ## The runtime opcode registry -/

-- Forty-seven runtime opcodes, and every one of them enumerated.
#guard Opcode.all.length = 47

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
    "list.rest", "int.add", "int.subtract", "int.multiply", "int.negate", "int.tdiv", "int.tmod",
    "int.less", "int.lessOrEqual", "int.equals", "int.ofNat", "int.toNat", "char.toNat",
    "char.ofNat", "char.equals", "char.less", "string.length", "string.isEmpty", "string.push",
    "string.singleton", "string.toList", "string.ofList"]

-- Every opcode records the TypeScript it lowers to.
#guard Opcode.all.all fun code => code.emittedForm ≠ ""

-- Every runtime symbol is tagged by how it reaches the target: an inline form or a generated helper.
#guard Opcode.all.all fun code =>
  code.runtimeSymbol.startsWith "inline:" || code.runtimeSymbol.startsWith "helper:"

-- The tag a symbol carries is one of exactly those two.
#guard Opcode.all.all fun code =>
  code.runtimeSymbolTag == "inline:" || code.runtimeSymbolTag == "helper:"

-- Exactly the rows whose model constant is derived record the semantic components it composes; a
-- primitive engine field composes nothing, so it records nothing.
#guard Opcode.all.all fun code => (code.components ≠ []) == code.derived

-- Seven opcodes are generated helpers, and they are exactly the rows whose emitted form is a
-- guarded composition rather than one operator or one method.
#guard (Opcode.all.filter fun code => code.runtimeSymbolTag == "helper:").map Opcode.kind =
  ["nat.subtract", "list.head", "int.tdiv", "int.tmod", "int.toNat", "char.ofNat", "char.less"]

-- Every generated helper is derived, and four more rows are derived without needing a helper: their
-- composition is still one expression at the use site.
#guard (Opcode.all.filter fun code => code.derived).map Opcode.kind =
  ["nat.subtract", "list.head", "int.tdiv", "int.tmod", "int.ofNat", "int.toNat", "char.ofNat",
    "char.less", "string.length", "string.push", "string.singleton"]

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

-- Every opcode is discharged from something recorded: an engine assumption, or — for the two rows
-- that are identities on the image — the representation fact its components name. `int.ofNat` and
-- `string.singleton` claim nothing about the engine, and saying they did would be false.
#guard Opcode.all.all fun code => code.requires ≠ [] || code.components ≠ []
#guard (Opcode.all.filter fun code => code.requires.isEmpty).map Opcode.kind =
  ["int.ofNat", "string.singleton"]

-- Every assumption an opcode names is one the plane declares.
#guard Opcode.all.all fun code => code.requires.all fun id => Id.all.contains id

-- Every declared assumption is named by at least one opcode, so the plane carries no dead assumption.
#guard Id.all.all fun id => Opcode.all.any fun code => code.requires.contains id

/-! ## The host-effect registry -/

-- Nineteen host operations, and every one of them enumerated.
#guard HostOp.all.length = 19

-- The enumeration has no repeats, and every spelling is distinct.
#guard HostOp.all.Nodup
#guard (HostOp.all.map HostOp.wire).Nodup

-- The spellings are exactly the ones `AgentCore.Substrate.Opcode.wire` emits and
-- `spec/semantics/registry.json` joins on. The two libraries are in separate repositories, so this
-- list is the tslean side of that join, checked here rather than assumed.
#guard HostOp.all.map HostOp.wire =
  ["host.store.get", "host.store.put", "host.store.delete", "host.store.list", "host.store.txn",
    "host.alarm.set", "host.alarm.get", "host.alarm.delete", "host.content.put",
    "host.content.get", "host.content.head", "host.content.range", "host.queue.send",
    "host.queue.ack", "host.queue.retry", "host.isolate.load", "host.isolate.call",
    "host.rpc.call", "host.rpc.dispose"]

-- Every host spelling is namespaced, so a host name cannot collide with an exported function name:
-- an emitted identifier never contains a dot.
#guard HostOp.all.all fun host => host.wire.startsWith "host."

-- Exactly a `foreign` declaration names a host operation, and it resolves to its reference body, so
-- the source semantics and the lowering run one body rather than two.
#guard (Ir.Decl.foreign "host.store.get" .storeGet [] .bytes (.natLit 0)).host?.isSome
#guard (Ir.Decl.function "f" [] .nat .nonrecursive (.natLit 0)).host?.isNone
#guard ((⟨[.foreign "host.store.get" .storeGet [] .bytes (.natLit 7)]⟩ : Ir.Program).function?
    "host.store.get").isSome
#guard (⟨[.foreign "host.store.get" .storeGet [] .bytes (.natLit 7)]⟩ : Ir.Program).hosts
  = [.storeGet]

-- Four declaration families, spelled as the decoder spells them.
#guard Family.all.map Family.kind = ["enum", "record", "function", "foreign"]

/-! ## The recursion discipline -/

-- The four disciplines spell the four wire kinds the decoder decodes.
#guard [Ir.Recursion.nonrecursive, .structural 2, .wellFounded, .mutualGroup ["f", "g"]].map
    Ir.Recursion.kind = ["none", "structural", "wellFounded", "mutual"]

-- Only a mutual member carries a group, and it carries every member of its block.
#guard (Ir.Recursion.mutualGroup ["f", "g"]).group = ["f", "g"]
#guard [Ir.Recursion.nonrecursive, .structural 0, .wellFounded].all fun recursion =>
  recursion.group.isEmpty

/-! ## The assumption plane -/

-- Sixteen assumptions, and every one of them enumerated.
#guard Id.all.length = 16

-- The enumeration has no repeats.
#guard Id.all.Nodup

-- Every assumption has a distinct stable identity.
#guard (Id.all.map Id.name).Nodup

-- The stable identities are the ones catalog rows key on.
#guard Id.all.map Id.name =
  ["boolean.logical-operators", "strict-equality.same-type", "bigint.exact-arithmetic",
    "bigint.relational", "conditional.truthy-selection", "string.utf16-concatenation",
    "array.dense-element-sequence", "bigint.from-length", "bigint.negation",
    "bigint.truncated-division", "string.code-point-at", "string.from-code-point",
    "string.code-point-iteration", "string.empty-code-unit-length", "option.tagged-object",
    "array.join-empty-separator"]

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

/--
The host boundary's premise is derivable from the program's lowering, so it is a replacement
requirement on the substrate's binding and not an extra assumption about the model.
-/
theorem host_premise_closed {program : Ir.Program} {target : Target.Program}
    (lowered : Preservation.LoweredProgram program target) :
    Preservation.HostSubstrate program target :=
  Preservation.hostSubstrate_of_loweredProgram lowered

/-- The proof registry is closed over the four declaration families, the fourth being the host
boundary. -/
theorem foreign_family_closed (runtime : Runtime) :
    Preservation.Family.Preserves runtime .foreign := Preservation.familyRegistry runtime .foreign

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
