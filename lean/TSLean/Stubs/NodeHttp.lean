-- TSLean.Stubs.NodeHttp
-- Lean stubs for Node.js `node:http` module.
-- Minimal types for verification — not executable.

namespace TSLean.Stubs.NodeHttp

-- ─── Types ──────────────────────────────────────────────────────────────────

/-- HTTP method. -/
inductive Method where
  | GET | POST | PUT | DELETE | PATCH | HEAD | OPTIONS
  deriving Repr, Inhabited, BEq

/-- HTTP headers as key-value pairs. -/
abbrev Headers := List (String × String)

/-- Incoming HTTP request. -/
structure IncomingMessage where
  method  : Method
  url     : String
  headers : Headers
  body    : Option String := none
  deriving Repr, Inhabited

/-- HTTP response. -/
structure ServerResponse where
  statusCode : Nat := 200
  headers    : Headers := []
  body       : String := ""
  deriving Repr, Inhabited

-- ─── Server operations ──────────────────────────────────────────────────────

/-- Opaque HTTP server handle. -/
opaque Server : Type
instance : Inhabited Server := ⟨sorry⟩

/-- Create an HTTP server with a request handler. -/
axiom createServer (handler : IncomingMessage → IO ServerResponse) : IO Server

/-- Start listening on a port. -/
axiom Server.listen (s : Server) (port : Nat) : IO Unit

/-- Close the server. -/
axiom Server.close (s : Server) : IO Unit

-- ─── Client operations ──────────────────────────────────────────────────────

/-- Make an HTTP request (simplified). -/
axiom request (url : String) (opts : IncomingMessage := default) : IO ServerResponse

/-- GET request shorthand. -/
noncomputable def get (url : String) : IO ServerResponse :=
  request url { method := .GET, url := url, headers := [] }

end TSLean.Stubs.NodeHttp
