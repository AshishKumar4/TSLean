-- TSLean.External.Fs
-- Stubs for Node.js fs module operations (verification-mode only).

namespace TSLean.External.Fs

opaque readFileSync (path : String) (encoding : String := "utf-8") : String
opaque writeFileSync (path : String) (data : String) : Unit
opaque existsSync (path : String) : Bool
opaque mkdirSync (path : String) (opts : Unit := ()) : Unit
opaque readdirSync (path : String) : Array String

def readFile (path : String) : IO String :=
  pure (readFileSync path)

def writeFile (path : String) (data : String) : IO Unit :=
  pure (writeFileSync path data)

end TSLean.External.Fs
