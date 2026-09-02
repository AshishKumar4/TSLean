import Lean
import TSLean.LeanToTypeScript.Semantics.Tests.Registry

/-!
# The registry report

Prints the three closed registries and the assumption plane as one deterministic JSON document.
`scripts/check-semantics-registry.mjs` reads it, joins it against
`src/lean-to-typescript/ir.ts` and `src/lean-to-typescript/emitter.ts`, and compares it with the
locked copy in `spec/semantics/registry.json`.

The report is derived from the Lean definitions rather than restated, so a registry change appears
here without anyone editing this file.
-/

namespace TSLean.LeanToTypeScript.Semantics

open Lean Ir Assumption

private def kindEntry (constructor kind : String) : Json :=
  Json.mkObj [("constructor", .str constructor), ("kind", .str kind)]

private def opcodeNamespace : String := "TSLean.LeanToTypeScript.Semantics.Opcode"

private def modelNamespace : String := "TSLean.LeanToTypeScript.Semantics.Runtime"

private def opcodeEntry (code : Ir.Opcode) : Json :=
  Json.mkObj [
    ("opcode", .str code.kind),
    ("emittedForm", .str code.emittedForm),
    ("runtimeSymbol", .str code.runtimeSymbol),
    ("theorem", .str (opcodeNamespace ++ "." ++ code.theoremName)),
    ("model", .str (modelNamespace ++ "." ++ code.modelField)),
    ("relation", .str "source = model"),
    ("components", .arr ((code.components.map Json.str).toArray)),
    ("requires", .arr ((code.requires.map fun id => Json.str id.name).toArray))
  ]

private def hostEntry (host : Ir.HostOp) : Json :=
  Json.mkObj [
    ("host", .str host.wire),
    ("constructor", .str (toString (repr host)))
  ]

private def assumptionEntry (id : Id) : Json :=
  Json.mkObj [
    ("id", .str id.name),
    ("sourceUrl", .str Assumption.source.url),
    ("sourceArtifact", .str Assumption.source.artifact),
    ("sourceDigest", .str Assumption.source.digest),
    ("clauses", .arr ((id.provenance.clauses.map Json.str).toArray)),
    ("statement", .str id.provenance.statement),
    ("oracle", .str id.provenance.oracle),
    ("coverage", .arr ((id.provenance.coverage.map Json.str).toArray)),
    ("canonicalWording", .str id.canonicalWording)
  ]

/-- The whole report. -/
def registryReport : Json :=
  Json.mkObj [
    ("schemaVersion", .num 1),
    ("expressionOperations", .arr ((Op.all.map fun op =>
      kindEntry (toString (repr op)) op.kind).toArray)),
    ("declarationFamilies", .arr ((Family.all.map fun family =>
      kindEntry (toString (repr family)) family.kind).toArray)),
    ("typeForms", .arr ((TyKind.all.map fun form =>
      kindEntry (toString (repr form)) form.kind).toArray)),
    ("opcodes", .arr ((Ir.Opcode.all.map opcodeEntry).toArray)),
    ("hostOpcodes", .arr ((Ir.HostOp.all.map hostEntry).toArray)),
    ("assumptions", .arr ((Id.all.map assumptionEntry).toArray))
  ]

end TSLean.LeanToTypeScript.Semantics

/-- Writes the report to standard output, one line, so a checker can compare it byte for byte. -/
def main : IO Unit :=
  IO.println TSLean.LeanToTypeScript.Semantics.registryReport.compress
