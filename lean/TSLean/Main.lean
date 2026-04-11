-- TSLean.Main
-- Entry point for the Lean-native transpiler executable.
-- Usage: tslean <input.json> <output.lean>
-- where input.json is produced by tsc-to-json.ts

import TSLean.JsonAST
import TSLean.Parser
import TSLean.Codegen

open TSLean

def main (args : List String) : IO Unit := do
  match args with
  | [jsonPath, outputPath] =>
    let json ← JsonAST.readJsonFile jsonPath
    let mod := Parser.parseModule json
    let leanCode := Codegen.generateLean mod
    IO.FS.writeFile ⟨outputPath⟩ leanCode
    IO.eprintln s!"✓ {jsonPath} → {outputPath} ({leanCode.length} bytes)"
  | [jsonPath] =>
    let json ← JsonAST.readJsonFile jsonPath
    let mod := Parser.parseModule json
    
    let leanCode := Codegen.generateLean mod
    IO.print leanCode
  | _ =>
    IO.eprintln "Usage: tslean <input.json> [output.lean]"
    IO.Process.exit 1
