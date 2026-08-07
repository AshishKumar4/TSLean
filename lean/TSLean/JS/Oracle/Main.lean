import TSLean.JS.Oracle.Abstract
import TSLean.JS.Oracle.Primitive

namespace TSLean.JS.Oracle

private def handleLine (line : String) : Lean.Json :=
  match Lean.Json.parse line with
  | .error message => protocolErrorJson { code := "malformed-json", message }
  | .ok json =>
      match parseRequest json with
      | .error error => protocolErrorJson error
      | .ok request =>
          let fixtureIsGraph := request.fixtures[0]?.any fun fixture =>
            (fixture.getObjVal? "kind" >>= (·.getStr?)).toOption = some "graph"
          let result : Except ProtocolError Lean.Json := match operationDomain? request.operation with
            | none => .error {
                id := some request.id
                code := "unknown-operation"
                message := s!"unknown operation: {request.operation}" }
            | some .primitive =>
                if fixtureIsGraph then .error {
                  id := some request.id
                  code := "invalid-domain"
                  message := "primitive operation requires primitive fixtures" }
                else evaluatePrimitive request
            | some .graph =>
                if fixtureIsGraph then evaluateAbstract request
                else .error {
                  id := some request.id
                  code := "invalid-domain"
                  message := "graph operation requires one graph fixture" }
          match result with
          | .ok observation => observationJson request.id observation
          | .error error => protocolErrorJson error

def run : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat do
    let line ← stdin.getLine
    if line.isEmpty then break
    stdout.putStrLn (handleLine line).compress
    stdout.flush
  return 0

end TSLean.JS.Oracle

def main (_arguments : List String) : IO UInt32 :=
  TSLean.JS.Oracle.run
