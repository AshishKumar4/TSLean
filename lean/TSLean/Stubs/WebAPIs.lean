-- TSLean.Stubs.WebAPIs
-- Lean stubs for common Web/Node APIs used in production TypeScript.
-- All types are opaque; operations are axiomatized for verification.
--
-- No `opaque` handle here carries `Inhabited`: an opaque type may be empty, so
-- the instance would be a false proposition, and giving it a carrier would let
-- `default` masquerade as a real handle. A flow needing a value it cannot obtain
-- has to degrade visibly instead.

namespace TSLean.Stubs.WebAPIs

-- ─── TextEncoder / TextDecoder ──────────────────────────────────────────────

structure TextEncoder where
  encoding : String := "utf-8"
  deriving Repr, Inhabited

def TextEncoder.mk' : TextEncoder := default

opaque TextEncoder.encode (te : TextEncoder) (s : String) : Array UInt8

structure TextDecoder where
  encoding : String := "utf-8"
  deriving Repr, Inhabited

def TextDecoder.mk' : TextDecoder := default

opaque TextDecoder.decode (td : TextDecoder) (data : Array UInt8) : String

-- ─── Headers ────────────────────────────────────────────────────────────────

structure Headers where
  entries : List (String × String) := []
  deriving Repr, Inhabited

def Headers.mk' : Headers := default

def Headers.get (h : Headers) (key : String) : Option String :=
  h.entries.findSome? fun (k, v) => if k == key then some v else none

def Headers.set (h : Headers) (key value : String) : Headers :=
  { entries := (key, value) :: h.entries.filter (fun (k, _) => k != key) }

def Headers.has (h : Headers) (key : String) : Bool := (h.get key).isSome

def Headers.delete (h : Headers) (key : String) : Headers :=
  { entries := h.entries.filter (fun (k, _) => k != key) }

-- ─── AbortController / AbortSignal ──────────────────────────────────────────

structure AbortSignal where
  aborted : Bool := false
  reason : Option String := none
  deriving Repr, Inhabited

structure AbortController where
  signal : AbortSignal := default
  deriving Repr, Inhabited

def AbortController.mk' : AbortController := default

def AbortController.abort (ac : AbortController) (reason : String := "Aborted") : AbortController :=
  { signal := { aborted := true, reason := some reason } }

-- ─── EventTarget ────────────────────────────────────────────────────────────

structure EventTarget where
  deriving Repr, Inhabited

def EventTarget.mk' : EventTarget := default

-- ─── AsyncLocalStorage ──────────────────────────────────────────────────────

structure AsyncLocalStorage (α : Type) where
  value : Option α := none
  deriving Inhabited

def AsyncLocalStorage.mk' {α : Type} [Inhabited α] : AsyncLocalStorage α := default

def AsyncLocalStorage.getStore {α : Type} (als : AsyncLocalStorage α) : Option α := als.value

noncomputable def AsyncLocalStorage.run {α β : Type} (als : AsyncLocalStorage α) (value : α) (fn : Unit → IO β) : IO β :=
  fn ()

-- ─── ReadableStream / WritableStream ────────────────────────────────────────

opaque ReadableStream : Type

opaque WritableStream : Type

-- ─── WebSocket ──────────────────────────────────────────────────────────────

structure WebSocket where
  url : String := ""
  readyState : Nat := 0
  deriving Repr, Inhabited

def WebSocket.mk' (url : String) : WebSocket := { url }

opaque WebSocket.send (ws : WebSocket) (data : String) : IO Unit
opaque WebSocket.close (ws : WebSocket) (code : Nat := 1000) : IO Unit

-- ─── Uint8Array ─────────────────────────────────────────────────────────────

abbrev Uint8Array := Array UInt8

-- ─── Disposable ─────────────────────────────────────────────────────────────

structure Disposable where
  dispose : IO Unit := pure ()
  deriving Inhabited

-- ─── Cloudflare Durable Objects API ─────────────────────────────────────────

/-- Opaque stub for DurableObjectNamespace (Cloudflare Workers API). -/
opaque DurableObjectNamespace (T : Type) : Type
instance {T} : BEq (DurableObjectNamespace T) := ⟨fun _ _ => false⟩
instance {T} : Repr (DurableObjectNamespace T) := ⟨fun _ _ => .text "DurableObjectNamespace"⟩

/-- Opaque stub for DurableObjectStub (Cloudflare Workers API). -/
opaque DurableObjectStub (T : Type) : Type
instance {T} : BEq (DurableObjectStub T) := ⟨fun _ _ => false⟩
instance {T} : Repr (DurableObjectStub T) := ⟨fun _ _ => .text "DurableObjectStub"⟩

/-- Opaque stub for DurableObjectId (Cloudflare Workers API). -/
opaque DurableObjectId : Type

/-- Opaque stub for DurableObjectStorage (Cloudflare Workers API). -/
opaque DurableObjectStorage : Type

/-- Opaque stub for DurableObjectState (Cloudflare Workers API). -/
structure DurableObjectState where
  id : String := ""
  deriving Repr, BEq, Inhabited

-- ─── URL / URLSearchParams ──────────────────────────────────────────────────

structure URL where
  href : String := ""
  protocol : String := ""
  hostname : String := ""
  port : String := ""
  pathname : String := ""
  search : String := ""
  hash : String := ""
  origin : String := ""
  deriving Repr, BEq, Inhabited

structure URLSearchParams where
  entries : List (String × String) := []
  deriving Repr, BEq, Inhabited

-- ─── Blob / FormData ────────────────────────────────────────────────────────

opaque Blob : Type

opaque FormData : Type

-- ─── Request / Response ─────────────────────────────────────────────────────

structure Request where
  url : String := ""
  method : String := "GET"
  headers : Headers := default
  body : Option String := none
  deriving Inhabited

structure Response where
  status : Float := 200
  statusText : String := "OK"
  headers : Headers := default
  body : Option String := none
  ok : Bool := true
  deriving Inhabited

-- ─── MessageEvent / CloseEvent ──────────────────────────────────────────────

structure MessageEvent where
  data : String := ""
  deriving Repr, BEq, Inhabited

structure CloseEvent where
  code : Float := 1000
  reason : String := ""
  wasClean : Bool := true
  deriving Repr, BEq, Inhabited

-- ─── Crypto ─────────────────────────────────────────────────────────────────

opaque SubtleCrypto : Type

-- ─── R2Bucket / SqlStorage (Cloudflare) ─────────────────────────────────────

opaque R2Bucket : Type

opaque SqlStorage : Type

end TSLean.Stubs.WebAPIs
