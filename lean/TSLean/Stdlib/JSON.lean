-- TSLean.Stdlib.JSON — JSON parse/stringify + Date basics.
import Lean.Data.Json

namespace TSLean.Stdlib.JSON

/-- JSON.parse: parse a JSON string to a Lean Json value. -/
def jsonParse (s : String) : Except String Lean.Json :=
  Lean.Json.parse s

/-- JSON.stringify: serialize a Lean Json value to a string. -/
def jsonStringify (j : Lean.Json) : String := j.compress

/-- JSON.stringify with indentation. -/
def jsonStringifyPretty (j : Lean.Json) (indent : Nat := 2) : String := j.pretty indent

end TSLean.Stdlib.JSON

-- ─── Date ────────────────────────────────────────────────────────────────────

namespace TSLean.Stdlib.Date

/-- Date representation as milliseconds since epoch. -/
structure Date where
  ms : Nat
  deriving Repr, Inhabited, BEq

/-- Date.now() → current time as milliseconds (IO). -/
def now : IO Date := do
  let ns ← IO.monoNanosNow
  pure { ms := ns / 1000000 }

/-- new Date() → current time. -/
def create : IO Date := now

/-- new Date(ms) → from milliseconds. -/
def fromMs (ms : Nat) : Date := { ms }

/-- date.getTime() → milliseconds since epoch. -/
def getTime (d : Date) : Nat := d.ms

/-- date.toISOString() → stub ISO format string. -/
def toISOString (d : Date) : String := s!"Date({d.ms})"

/-- date.valueOf() → milliseconds since epoch. -/
def valueOf (d : Date) : Nat := d.ms

/-- Date arithmetic. -/
def addMs (d : Date) (ms : Nat) : Date := { ms := d.ms + ms }
def diffMs (a b : Date) : Int := (a.ms : Int) - (b.ms : Int)

end TSLean.Stdlib.Date
