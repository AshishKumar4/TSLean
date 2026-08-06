import TSLean.JS.Monad

namespace TSLean.JS

namespace External

private def operationName (name : String) : JSString := JSString.ofLeanString name

/-- Reads scripted time, commits platform state, and emits one ordered event. -/
def now : JSM P Nat := fun machine =>
  let (result, platform) := P.now machine.platform
  let next := machine.setPlatform platform
  match result with
  | .ok value => .done (.normal value) (next.emit (.now value))
  | .error fault =>
      .fault (.platform fault) (next.emit (.platformFault (operationName "now") fault))

/-- Reads scripted randomness, commits platform state, and emits one ordered event. -/
def random : JSM P JSNumber := fun machine =>
  let (result, platform) := P.random machine.platform
  let next := machine.setPlatform platform
  match result with
  | .ok value => .done (.normal value) (next.emit (.random value))
  | .error fault =>
      .fault (.platform fault) (next.emit (.platformFault (operationName "random") fault))

/-- Performs synchronous modeled fetch. Rejection is a JavaScript throw; platform failure is not. -/
def fetch (request : FetchRequest) : JSM P FetchResponse := fun machine =>
  let (result, platform) := P.fetch machine.platform request
  let next := machine.setPlatform platform
  match result with
  | .ok fetchResult =>
      let traced := next.emit (.fetch request fetchResult)
      match fetchResult with
      | .resolved response => .done (.normal response) traced
      | .rejected reason => .done (.thrown reason) traced
  | .error fault =>
      .fault (.platform fault) (next.emit (.platformFault (operationName "fetch") fault))

end External
end TSLean.JS
