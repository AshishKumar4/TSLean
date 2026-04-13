-- TSLean.Stubs.Console
-- Lean stubs for the global `console` object.
-- Maps to Lean's IO.println/IO.eprintln.

namespace TSLean.Stubs.Console

/-- console.log — print to stdout with newline. -/
def log (msg : String) : IO Unit := IO.println msg

/-- console.error — print to stderr with newline. -/
def error (msg : String) : IO Unit := IO.eprintln msg

/-- console.warn — print to stderr (same as error). -/
def warn (msg : String) : IO Unit := IO.eprintln msg

/-- console.info — print to stdout (same as log). -/
def info (msg : String) : IO Unit := IO.println msg

/-- console.debug — print to stdout (same as log). -/
def debug (msg : String) : IO Unit := IO.println msg

/-- console.time — start a named timer. Stub: no-op. -/
def time (_ : String) : IO Unit := pure ()

/-- console.timeEnd — end a named timer. Stub: no-op. -/
def timeEnd (_ : String) : IO Unit := pure ()

/-- console.timeLog — log timer value. Stub: no-op. -/
def timeLog (_ : String) : IO Unit := pure ()

/-- console.assert — assert with message. -/
def assert_ (cond : Bool) (msg : String := "Assertion failed") : IO Unit :=
  if !cond then IO.eprintln msg else pure ()

/-- console.clear — clear console. Stub: no-op. -/
def clear : IO Unit := pure ()

/-- console.count — count calls. Stub: no-op. -/
def count (_ : String := "default") : IO Unit := pure ()

/-- console.countReset — reset counter. Stub: no-op. -/
def countReset (_ : String := "default") : IO Unit := pure ()

/-- console.table — display tabular data. Maps to log. -/
def table (msg : String) : IO Unit := IO.println msg

/-- console.trace — print stack trace. Maps to log. -/
def trace (msg : String := "") : IO Unit := IO.println s!"Trace: {msg}"

/-- console.group — start indented group. Stub: no-op. -/
def group (_ : String := "") : IO Unit := pure ()

/-- console.groupEnd — end indented group. Stub: no-op. -/
def groupEnd : IO Unit := pure ()

end TSLean.Stubs.Console
