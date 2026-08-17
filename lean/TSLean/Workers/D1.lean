-- TSLean.Workers.D1
-- Cloudflare D1 Database bindings.
--
-- Every operation is `opaque`, never `axiom`: this module is in the emitted trusted base, and an
-- `axiom` is a new assumption that every proof reaching it inherits. `opaque` names the same
-- unknown constant without assuming anything, because each result type is already nonempty.

import TSLean.Runtime.Basic

namespace TSLean.Workers.D1

-- Opaque external service handles. No `Inhabited`: either may be empty, and only
-- the runtime binding (resp. `prepare`) produces one.
opaque D1Database : Type

opaque D1PreparedStatement : Type

structure D1Meta where
  duration : Float
  changes : Nat
  last_row_id : Nat
  rows_read : Nat
  rows_written : Nat
  deriving Inhabited

structure D1Result where
  results : Array String
  success : Bool
  deriving Inhabited

structure D1ExecResult where
  count : Nat
  duration : Float
  deriving Inhabited

-- Prepare a parameterized query, and bind values to a prepared statement.
--
-- Both are in `IO` although the Workers API is synchronous, because `D1PreparedStatement` is opaque
-- and so may be empty: a total function into it would assert an inhabitant this module cannot
-- produce, which is the assumption `opaque` exists to avoid. A statement therefore only ever comes
-- back from the runtime, which is where it comes from in the platform too.
opaque prepare (db : D1Database) (query : String) : IO D1PreparedStatement

opaque bind (stmt : D1PreparedStatement) (values : Array String) : IO D1PreparedStatement

-- Execute queries
opaque first (stmt : D1PreparedStatement) : IO (Option String)
opaque all (stmt : D1PreparedStatement) : IO D1Result
opaque raw (stmt : D1PreparedStatement) : IO (Array (Array String))
opaque run (stmt : D1PreparedStatement) : IO D1ExecResult

-- Direct exec (without prepare)
opaque exec (db : D1Database) (query : String) : IO D1ExecResult

-- Batch multiple statements
opaque batch (db : D1Database) (stmts : Array D1PreparedStatement) : IO (Array D1Result)

-- Dump database
opaque dump (db : D1Database) : IO String

end TSLean.Workers.D1
