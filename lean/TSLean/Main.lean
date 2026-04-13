-- TSLean.Main
-- Entry point for the Lean-native transpiler executable.
-- Usage: tslean <input.json> [output.lean]
-- where input.json is produced by tsc-to-json.ts
--
-- Pipeline: JSON AST → V2 LeanAST (FromJSON) → Text (Printer)

import TSLean.JsonAST
import TSLean.V2.FromJSON
import TSLean.V2.Printer

open TSLean

def main (args : List String) : IO Unit := do
  match args with
  | [jsonPath, outputPath] =>
    let json ← JsonAST.readJsonFile jsonPath
    let leanFile := V2.FromJSON.lowerJsonModule json
    let leanCode := V2.Printer.printFile leanFile
    IO.FS.writeFile ⟨outputPath⟩ leanCode
    IO.eprintln s!"✓ {jsonPath} → {outputPath} ({leanCode.length} bytes)"
  | [jsonPath] =>
    let json ← JsonAST.readJsonFile jsonPath
    let leanFile := V2.FromJSON.lowerJsonModule json
    let leanCode := V2.Printer.printFile leanFile
    IO.print leanCode
  | _ =>
    IO.eprintln "Usage: tslean <input.json> [output.lean]"
    IO.Process.exit 1
