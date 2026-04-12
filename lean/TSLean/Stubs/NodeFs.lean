-- TSLean.Stubs.NodeFs
-- Lean stubs for Node.js `node:fs` and `node:fs/promises` modules.
-- All functions are axiomatized IO actions for verification purposes.

namespace TSLean.Stubs.NodeFs

-- ─── Types ──────────────────────────────────────────────────────────────────

/-- Opaque file stats object. -/
structure Stats where
  size     : Nat
  isFile   : Bool
  isDir    : Bool
  mtime    : Nat   -- milliseconds since epoch
  deriving Repr, Inhabited

/-- File descriptor (opaque handle). -/
abbrev Fd := Nat

/-- Encoding for text operations. -/
abbrev Encoding := String

-- ─── Synchronous operations ─────────────────────────────────────────────────

/-- Read a file synchronously. Returns file contents as a string. -/
axiom readFileSync (path : String) (encoding : Encoding := "utf-8") : String

/-- Write data to a file synchronously. -/
axiom writeFileSync (path : String) (data : String) : Unit

/-- Check if a path exists synchronously. -/
axiom existsSync (path : String) : Bool

/-- Create a directory synchronously (recursive). -/
axiom mkdirSync (path : String) : Unit

/-- Read directory contents synchronously. -/
axiom readdirSync (path : String) : Array String

/-- Get file stats synchronously. -/
axiom statSync (path : String) : Stats

/-- Delete a file synchronously. -/
axiom unlinkSync (path : String) : Unit

/-- Rename/move a file synchronously. -/
axiom renameSync (oldPath newPath : String) : Unit

/-- Copy a file synchronously. -/
axiom copyFileSync (src dest : String) : Unit

-- ─── Async (IO) operations ──────────────────────────────────────────────────

/-- Read a file asynchronously. -/
noncomputable def readFile (path : String) (encoding : Encoding := "utf-8") : IO String :=
  pure (readFileSync path encoding)

/-- Write data to a file asynchronously. -/
noncomputable def writeFile (path : String) (data : String) : IO Unit :=
  pure (writeFileSync path data)

/-- Create a directory asynchronously (recursive). -/
noncomputable def mkdir (path : String) : IO Unit :=
  pure (mkdirSync path)

/-- Get file stats asynchronously. -/
noncomputable def stat (path : String) : IO Stats :=
  pure (statSync path)

/-- Read directory contents asynchronously. -/
noncomputable def readdir (path : String) : IO (Array String) :=
  pure (readdirSync path)

/-- Delete a file asynchronously. -/
noncomputable def unlink (path : String) : IO Unit :=
  pure (unlinkSync path)

/-- Check file existence (async wrapper). -/
noncomputable def exists_ (path : String) : IO Bool :=
  pure (existsSync path)

end TSLean.Stubs.NodeFs
