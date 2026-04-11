-- TSLean.Main
-- Entry point for the Lean-native transpiler executable.
-- Usage: tslean <input.json> [output.lean] [--v1]
-- where input.json is produced by tsc-to-json.ts
--
-- Default: V2 pipeline (JSON → IR → LeanAST → Printer)
-- --v1:    V1 pipeline (JSON → IR → simple codegen)

import TSLean.JsonAST
import TSLean.Parser
import TSLean.Codegen
import TSLean.V2.Lower
import TSLean.V2.Printer

open TSLean

def transpileV2 (json : Lean.Json) : String :=
  let mod := Parser.parseModule json
  let leanFile := V2.Lower.lowerModule mod
  V2.Printer.printFile leanFile

def transpileV1 (json : Lean.Json) : String :=
  let mod := Parser.parseModule json
  Codegen.generateLean mod

def main (args : List String) : IO Unit := do
  let useV1 := args.any (· == "--v1")
  let paths := args.filter (· != "--v1")
  match paths with
  | [jsonPath, outputPath] =>
    let json ← JsonAST.readJsonFile jsonPath
    let leanCode := if useV1 then transpileV1 json else transpileV2 json
    IO.FS.writeFile ⟨outputPath⟩ leanCode
    IO.eprintln s!"✓ {jsonPath} → {outputPath} ({leanCode.length} bytes)"
  | [jsonPath] =>
    let json ← JsonAST.readJsonFile jsonPath
    let leanCode := if useV1 then transpileV1 json else transpileV2 json
    IO.print leanCode
  | _ =>
    IO.eprintln "Usage: tslean <input.json> [output.lean] [--v1]"
    IO.Process.exit 1
