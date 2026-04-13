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

end TSLean.Stubs.WebAPIs
