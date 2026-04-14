-- TSLean.Stubs.WebAPIs
-- Lean stubs for common Web/Node APIs used in production TypeScript.
-- All types are opaque; operations are axiomatized for verification.

namespace TSLean.Stubs.WebAPIs

-- ─── TextEncoder / TextDecoder ──────────────────────────────────────────────

structure TextEncoder where
  encoding : String := "utf-8"
  deriving Repr, Inhabited

def TextEncoder.mk' : TextEncoder := default

axiom TextEncoder.encode (te : TextEncoder) (s : String) : Array UInt8

structure TextDecoder where
  encoding : String := "utf-8"
  deriving Repr, Inhabited

def TextDecoder.mk' : TextDecoder := default

axiom TextDecoder.decode (td : TextDecoder) (data : Array UInt8) : String

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
instance : Inhabited ReadableStream := ⟨sorry⟩

opaque WritableStream : Type
instance : Inhabited WritableStream := ⟨sorry⟩

-- ─── WebSocket ──────────────────────────────────────────────────────────────

structure WebSocket where
  url : String := ""
  readyState : Nat := 0
  deriving Repr, Inhabited

def WebSocket.mk' (url : String) : WebSocket := { url }

axiom WebSocket.send (ws : WebSocket) (data : String) : IO Unit
axiom WebSocket.close (ws : WebSocket) (code : Nat := 1000) : IO Unit

-- ─── Uint8Array ─────────────────────────────────────────────────────────────

abbrev Uint8Array := Array UInt8

-- ─── Disposable ─────────────────────────────────────────────────────────────

structure Disposable where
  dispose : IO Unit := pure ()
  deriving Inhabited

-- ─── Cloudflare Durable Objects API ─────────────────────────────────────────

/-- Opaque stub for DurableObjectNamespace (Cloudflare Workers API). -/
opaque DurableObjectNamespace (T : Type) : Type
instance {T} : Inhabited (DurableObjectNamespace T) := ⟨sorry⟩
instance {T} : BEq (DurableObjectNamespace T) := ⟨fun _ _ => false⟩
instance {T} : Repr (DurableObjectNamespace T) := ⟨fun _ _ => .text "DurableObjectNamespace"⟩

/-- Opaque stub for DurableObjectStub (Cloudflare Workers API). -/
opaque DurableObjectStub (T : Type) : Type
instance {T} : Inhabited (DurableObjectStub T) := ⟨sorry⟩
instance {T} : BEq (DurableObjectStub T) := ⟨fun _ _ => false⟩
instance {T} : Repr (DurableObjectStub T) := ⟨fun _ _ => .text "DurableObjectStub"⟩

/-- Opaque stub for DurableObjectId (Cloudflare Workers API). -/
opaque DurableObjectId : Type
instance : Inhabited DurableObjectId := ⟨sorry⟩

/-- Opaque stub for DurableObjectStorage (Cloudflare Workers API). -/
opaque DurableObjectStorage : Type
instance : Inhabited DurableObjectStorage := ⟨sorry⟩

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
instance : Inhabited Blob := ⟨sorry⟩

opaque FormData : Type
instance : Inhabited FormData := ⟨sorry⟩

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
instance : Inhabited SubtleCrypto := ⟨sorry⟩

-- ─── R2Bucket / SqlStorage (Cloudflare) ─────────────────────────────────────

opaque R2Bucket : Type
instance : Inhabited R2Bucket := ⟨sorry⟩

opaque SqlStorage : Type
instance : Inhabited SqlStorage := ⟨sorry⟩

end TSLean.Stubs.WebAPIs
