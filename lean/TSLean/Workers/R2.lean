-- TSLean.Workers.R2
-- Cloudflare R2 Object Storage bindings (axiomatized).

import TSLean.Runtime.Basic
import TSLean.Stdlib.HashMap

namespace TSLean.Workers.R2

opaque R2Bucket : Type
instance : Inhabited R2Bucket := ⟨sorry⟩

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
axiom get (bucket : R2Bucket) (key : String) : IO (Option R2Object)
axiom put (bucket : R2Bucket) (key : String) (value : String) : IO R2Object
axiom delete (bucket : R2Bucket) (key : String) : IO Unit
axiom list (bucket : R2Bucket) (prefix_ : Option String) (limit : Option Nat) : IO R2Objects
axiom head (bucket : R2Bucket) (key : String) : IO (Option R2Object)

-- Text extraction from R2Object body
axiom R2Object.text (obj : R2Object) : IO String
axiom R2Object.json (obj : R2Object) : IO String

end TSLean.Workers.R2
