import Lean.Data.Json

namespace TSLean.JS.Oracle

structure Request where
  id : String
  operation : String
  fixtures : Array Lean.Json

structure ProtocolError where
  id : Option String := none
  code : String
  message : String

def objectSize : Lean.Json → Option Nat
  | .obj fields => some (fields.fold (init := 0) fun count _ _ => count + 1)
  | _ => none

def exactObject (value : Lean.Json) (size : Nat) : Except String Unit :=
  match objectSize value with
  | some actual => if actual = size then .ok () else .error s!"expected exactly {size} fields"
  | none => .error "expected object"

def stringField (value : Lean.Json) (name : String) : Except String String := do
  (← value.getObjVal? name).getStr?

def arrayField (value : Lean.Json) (name : String) : Except String (Array Lean.Json) := do
  (← value.getObjVal? name).getArr?

def requestId? (value : Lean.Json) : Option String :=
  (value.getObjVal? "id" >>= (·.getStr?)).toOption

def parseRequest (value : Lean.Json) : Except ProtocolError Request :=
  match do
    exactObject value 3
    let id ← stringField value "id"
    if id.isEmpty then throw "id must not be empty"
    let operation ← stringField value "operation"
    if operation.isEmpty then throw "operation must not be empty"
    let fixtures ← arrayField value "fixtures"
    return Request.mk id operation fixtures
  with
  | .ok request => .ok request
  | .error message => .error { id := requestId? value, code := "invalid-request", message }

def protocolErrorJson (error : ProtocolError) : Lean.Json :=
  Lean.Json.mkObj [
    ("id", error.id.map Lean.Json.str |>.getD .null),
    ("status", "protocol-error"),
    ("error", Lean.Json.mkObj [("code", error.code), ("message", error.message)])
  ]

def observationJson (id : String) (observation : Lean.Json) : Lean.Json :=
  Lean.Json.mkObj [("id", id), ("status", "ok"), ("observation", observation)]

end TSLean.JS.Oracle
