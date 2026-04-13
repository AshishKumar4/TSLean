-- TSLean.Stubs.Process
-- Lean stubs for Node.js `process` global object.
-- Maps to Lean's IO and System modules where possible.

namespace TSLean.Stubs.Process

-- ─── Environment ────────────────────────────────────────────────────────────

/-- process.env — read environment variables. -/
def env (key : String) : IO (Option String) := IO.getEnv key

/-- process.env access as a map. -/
axiom envMap : IO (List (String × String))

-- ─── Arguments ──────────────────────────────────────────────────────────────

/-- process.argv — command-line arguments. -/
axiom argv : IO (Array String)

-- ─── Control flow ───────────────────────────────────────────────────────────

/-- process.exit — terminate with exit code. -/
axiom exit (code : UInt32 := 0) : IO Unit

-- ─── Working directory ──────────────────────────────────────────────────────

/-- process.cwd — get current working directory. -/
axiom cwd : IO String

-- ─── Standard streams ───────────────────────────────────────────────────────

/-- process.stdout.write — write to stdout without newline. -/
def stdoutWrite (s : String) : IO Unit := IO.print s

/-- process.stderr.write — write to stderr without newline. -/
def stderrWrite (s : String) : IO Unit := IO.eprint s

/-- process.stdin — read a line from stdin. -/
def stdinReadLine : IO String := do
  let stdin ← IO.getStdin
  stdin.getLine

-- ─── Platform info ──────────────────────────────────────────────────────────

/-- process.platform — operating system identifier. -/
axiom platform : String

/-- process.arch — CPU architecture. -/
axiom arch : String

/-- process.version — Node.js version string. -/
axiom version : String

/-- process.pid — process ID. -/
axiom pid : Nat

-- ─── Timing ─────────────────────────────────────────────────────────────────

/-- process.hrtime.bigint — high-resolution nanosecond timer. -/
def hrtimeBigint : IO Nat := IO.monoNanosNow

/-- process.uptime — process uptime in seconds. -/
axiom uptime : IO Float

-- ─── Memory ─────────────────────────────────────────────────────────────────

/-- process.memoryUsage — stub returning zeros. -/
structure MemoryUsage where
  rss : Nat := 0
  heapTotal : Nat := 0
  heapUsed : Nat := 0
  external : Nat := 0
  deriving Repr, Inhabited

def memoryUsage : IO MemoryUsage := pure default

end TSLean.Stubs.Process
