-- TSLean.Workers.D1
-- Cloudflare D1 Database bindings (axiomatized).

import TSLean.Runtime.Basic

namespace TSLean.Workers.D1

opaque D1Database : Type
instance : Inhabited D1Database := ⟨sorry⟩

opaque D1PreparedStatement : Type
instance : Inhabited D1PreparedStatement := ⟨sorry⟩

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

-- Prepare a parameterized query
axiom prepare (db : D1Database) (query : String) : D1PreparedStatement

-- Bind values to a prepared statement
axiom bind (stmt : D1PreparedStatement) (values : Array String) : D1PreparedStatement

-- Execute queries
axiom first (stmt : D1PreparedStatement) : IO (Option String)
axiom all (stmt : D1PreparedStatement) : IO D1Result
axiom raw (stmt : D1PreparedStatement) : IO (Array (Array String))
axiom run (stmt : D1PreparedStatement) : IO D1ExecResult

-- Direct exec (without prepare)
axiom exec (db : D1Database) (query : String) : IO D1ExecResult

-- Batch multiple statements
axiom batch (db : D1Database) (stmts : Array D1PreparedStatement) : IO (Array D1Result)

-- Dump database
axiom dump (db : D1Database) : IO String

end TSLean.Workers.D1
