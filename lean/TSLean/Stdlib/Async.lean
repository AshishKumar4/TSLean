-- TSLean.Stdlib.Async — Promise combinators and async utilities.
namespace TSLean.Stdlib.Async

variable {α β : Type}

/-- Promise.all: run all IO actions and collect results. -/
def promiseAll (tasks : Array (IO α)) : IO (Array α) :=
  tasks.foldlM (fun acc task => do let r ← task; pure (acc.push r)) #[]

/-- Promise.race: run all tasks, return first to complete.
    In pure Lean, we just return the first task's result. -/
def promiseRace (tasks : Array (IO α)) : IO α := do
  if h : 0 < tasks.size then tasks[0]'h
  else throw (IO.Error.userError "Promise.race: empty array")

/-- Promise.allSettled: run all tasks, return results or errors.
    Models PromiseSettledResult as Except. -/
def promiseAllSettled (tasks : Array (IO α)) : IO (Array (Except IO.Error α)) :=
  tasks.mapM fun task => do
    try
      let r ← task
      pure (Except.ok r)
    catch e =>
      pure (Except.error e)

/-- Promise.any: return first successful result, or error if all fail. -/
def promiseAny (tasks : Array (IO α)) : IO α := do
  let results ← promiseAllSettled tasks
  match results.find? Except.isOk with
  | some (Except.ok v) => pure v
  | _ => throw (IO.Error.userError "Promise.any: all promises rejected")

/-- Promise.resolve: lift a pure value into IO. -/
def promiseResolve (v : α) : IO α := pure v

/-- Promise.reject: create a rejected promise (throw). -/
def promiseReject (msg : String) : IO α := throw (IO.Error.userError msg)

/-- setTimeout: sleep for ms milliseconds then execute. -/
def setTimeout (ms : Nat) (action : IO Unit) : IO Unit := do
  IO.sleep (ms.toUInt32)
  action

/-- setInterval: not expressible as a single value in Lean. Stub. -/
def setInterval (_ : Nat) (_ : IO Unit) : IO Unit := pure ()

/-- queueMicrotask: execute immediately in IO (no microtask queue in Lean). -/
def queueMicrotask (action : IO Unit) : IO Unit := action

/-- clearTimeout: no-op in Lean (timers don't exist). -/
def clearTimeout (_id : α) : Unit := ()

/-- clearInterval: no-op in Lean (timers don't exist). -/
def clearInterval (_id : α) : Unit := ()

end TSLean.Stdlib.Async
