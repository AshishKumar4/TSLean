-- TSLean.Workers.KV
-- Cloudflare Workers KV Namespace bindings (axiomatized).

import TSLean.Runtime.Basic
import TSLean.Stdlib.HashMap

namespace TSLean.Workers.KV

-- KV is an opaque external service handle.
opaque KVNamespace : Type
instance : Inhabited KVNamespace := ⟨sorry⟩

-- Core operations (all IO since they hit the network)
axiom get (ns : KVNamespace) (key : String) : IO (Option String)
axiom put (ns : KVNamespace) (key : String) (value : String) : IO Unit
axiom delete (ns : KVNamespace) (key : String) : IO Unit

structure KVListKey where
  name : String
  expiration : Option Nat := none
  deriving Repr, BEq, Inhabited

structure KVListResult where
  keys : Array KVListKey
  list_complete : Bool
  cursor : Option String := none
  deriving Repr, BEq, Inhabited

axiom list (ns : KVNamespace) (prefix_ : Option String) (limit : Option Nat) : IO KVListResult

structure KVValueWithMetadata where
  value : Option String
  metadata : Option String := none
  deriving Repr, BEq, Inhabited

axiom getWithMetadata (ns : KVNamespace) (key : String) : IO KVValueWithMetadata

end TSLean.Workers.KV
