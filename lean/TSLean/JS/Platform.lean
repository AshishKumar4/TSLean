import TSLean.JS.Number
import TSLean.JS.String
import TSLean.JS.Value

namespace TSLean.JS

/-- A synchronous fetch request at the model boundary. Async source semantics are unsupported. -/
structure FetchRequest where
  url : JSString
  deriving DecidableEq

/-- A synchronous fetch response at the model boundary. -/
structure FetchResponse where
  status : Nat
  body : JSString
  deriving DecidableEq

/-- A modeled fetch either resolves synchronously or rejects with a JavaScript value. -/
inductive FetchResult where
  | resolved (response : FetchResponse)
  | rejected (reason : Value)
  deriving DecidableEq

/-- Host/model failures are distinct from JavaScript throws. -/
inductive PlatformFault where
  | scriptExhausted (operation : JSString)
  | scripted (message : JSString)
  deriving DecidableEq

/-- Pure host capabilities. Every operation returns its updated associated state even on fault. -/
structure Platform where
  State : Type
  initialState : State
  now : State → Except PlatformFault Nat × State
  random : State → Except PlatformFault JSNumber × State
  fetch : State → FetchRequest → Except PlatformFault FetchResult × State

/-- Deterministic capability state backed by finite operation scripts. -/
structure ScriptedPlatformState where
  times : Array (Except PlatformFault Nat)
  randoms : Array (Except PlatformFault JSNumber)
  fetches : Array (Except PlatformFault FetchResult)
  timeIndex : Nat := 0
  randomIndex : Nat := 0
  fetchIndex : Nat := 0

namespace ScriptedPlatform

/-- Consumes one scripted clock entry, advancing only the clock index. -/
def stepNow (state : ScriptedPlatformState) : Except PlatformFault Nat × ScriptedPlatformState :=
  let result := state.times[state.timeIndex]?.getD
    (.error (.scriptExhausted (JSString.ofLeanString "now")))
  (result, { state with timeIndex := state.timeIndex + 1 })

/-- Consumes one scripted random entry, advancing only the random index. -/
def stepRandom (state : ScriptedPlatformState) :
    Except PlatformFault JSNumber × ScriptedPlatformState :=
  let result := state.randoms[state.randomIndex]?.getD
    (.error (.scriptExhausted (JSString.ofLeanString "random")))
  (result, { state with randomIndex := state.randomIndex + 1 })

/-- Consumes one scripted fetch entry, advancing only the fetch index. -/
def stepFetch (state : ScriptedPlatformState) (_request : FetchRequest) :
    Except PlatformFault FetchResult × ScriptedPlatformState :=
  let result := state.fetches[state.fetchIndex]?.getD
    (.error (.scriptExhausted (JSString.ofLeanString "fetch")))
  (result, { state with fetchIndex := state.fetchIndex + 1 })

/-- Builds a deterministic pure platform from finite scripts. -/
def make (state : ScriptedPlatformState) : Platform where
  State := ScriptedPlatformState
  initialState := state
  now := stepNow
  random := stepRandom
  fetch := stepFetch

end ScriptedPlatform
end TSLean.JS
