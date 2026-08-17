-- TSLean.Workers.KV
-- Cloudflare Workers KV Namespace bindings.
--
-- Every operation is `opaque`, never `axiom`: this module is in the emitted trusted base, and an
-- `axiom` is a new assumption that every proof reaching it inherits. `opaque` names the same
-- unknown constant without assuming anything, because each result type is already nonempty.

import TSLean.Runtime.Basic
import TSLean.Stdlib.HashMap

namespace TSLean.Workers.KV

-- KV is an opaque external service handle. No `Inhabited`: it may be empty, and
-- only the runtime binding produces one.
opaque KVNamespace : Type

-- Core operations (all IO since they hit the network)
opaque get (ns : KVNamespace) (key : String) : IO (Option String)
opaque put (ns : KVNamespace) (key : String) (value : String) : IO Unit
opaque delete (ns : KVNamespace) (key : String) : IO Unit

structure KVListKey where
  name : String
  expiration : Option Nat := none
  deriving Repr, BEq, Inhabited

structure KVListResult where
  keys : Array KVListKey
  list_complete : Bool
  cursor : Option String := none
  deriving Repr, BEq, Inhabited

opaque list (ns : KVNamespace) (prefix_ : Option String) (limit : Option Nat) : IO KVListResult

structure KVValueWithMetadata where
  value : Option String
  metadata : Option String := none
  deriving Repr, BEq, Inhabited

opaque getWithMetadata (ns : KVNamespace) (key : String) : IO KVValueWithMetadata

end TSLean.Workers.KV
