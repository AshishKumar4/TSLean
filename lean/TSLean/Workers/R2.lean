-- TSLean.Workers.R2
-- Cloudflare R2 Object Storage bindings.
--
-- Every operation is `opaque`, never `axiom`: this module is in the emitted trusted base, and an
-- `axiom` is a new assumption that every proof reaching it inherits. `opaque` names the same
-- unknown constant without assuming anything, because each result type is already nonempty.

import TSLean.Runtime.Basic
import TSLean.Stdlib.HashMap

namespace TSLean.Workers.R2

-- Opaque external service handle. No `Inhabited`: it may be empty, and only the
-- runtime binding produces one.
opaque R2Bucket : Type

structure R2Object where
  key : String
  size : Nat
  etag : String
  version : String
  httpMetadata : List (String × String) := []
  customMetadata : List (String × String) := []
  deriving Repr, BEq, Inhabited

structure R2Objects where
  objects : Array R2Object
  truncated : Bool
  cursor : Option String := none
  delimitedPrefixes : Array String := #[]
  deriving Repr, BEq, Inhabited

-- Core operations
opaque get (bucket : R2Bucket) (key : String) : IO (Option R2Object)
opaque put (bucket : R2Bucket) (key : String) (value : String) : IO R2Object
opaque delete (bucket : R2Bucket) (key : String) : IO Unit
opaque list (bucket : R2Bucket) (prefix_ : Option String) (limit : Option Nat) : IO R2Objects
opaque head (bucket : R2Bucket) (key : String) : IO (Option R2Object)

-- Text extraction from R2Object body
opaque R2Object.text (obj : R2Object) : IO String
opaque R2Object.json (obj : R2Object) : IO String

end TSLean.Workers.R2
