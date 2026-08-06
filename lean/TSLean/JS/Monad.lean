import TSLean.JS.Completion
import TSLean.JS.Machine

namespace TSLean.JS

/-- Failures of the executable model, never JavaScript exception values. -/
inductive ModelFault where
  | runtime (fault : RuntimeFault)
  | platform (fault : PlatformFault)
  deriving DecidableEq

/-- A machine run always returns its final committed state. -/
inductive RunResult (P : Platform) (α : Type) where
  | done (completion : Completion α) (machine : Machine P)
  | exhausted (machine : Machine P)
  | fault (fault : ModelFault) (machine : Machine P)

/-- Total JavaScript state computations with explicit non-JavaScript terminal outcomes. -/
def JSM (P : Platform) (α : Type) := Machine P → RunResult P α

namespace JSM

/-- Executes a computation from a supplied valid machine. -/
def run (action : JSM P α) (machine : Machine P) : RunResult P α := action machine

/-- Produces a normal completion without changing state. -/
protected def pure (value : α) : JSM P α := fun machine => .done (.normal value) machine

/-- Sequences normal completion while preserving state for all terminal outcomes. -/
protected def bind (action : JSM P α) (next : α → JSM P β) : JSM P β := fun machine =>
  match action machine with
  | .done (.normal value) nextMachine => next value nextMachine
  | .done (.returned value) nextMachine => .done (.returned value) nextMachine
  | .done (.thrown value) nextMachine => .done (.thrown value) nextMachine
  | .done (.break label) nextMachine => .done (.break label) nextMachine
  | .done (.continue label) nextMachine => .done (.continue label) nextMachine
  | .exhausted nextMachine => .exhausted nextMachine
  | .fault fault nextMachine => .fault fault nextMachine

instance : Monad (JSM P) where
  pure := JSM.pure
  bind := JSM.bind

/-- Reads the complete machine. -/
def get : JSM P (Machine P) := fun machine => .done (.normal machine) machine

/-- Replaces the complete machine. -/
def set (machine : Machine P) : JSM P Unit := fun _ => .done (.normal ()) machine

/-- Applies a pure total machine update. -/
def modify (update : Machine P → Machine P) : JSM P Unit := fun machine =>
  .done (.normal ()) (update machine)

/-- Stops with an explicit model fault. -/
def fail (fault : ModelFault) : JSM P α := fun machine => .fault fault machine

/-- Reads the committed object heap. -/
def readHeap : JSM P Heap := fun machine => .done (.normal machine.heap) machine

/-- Applies a pure heap update and commits it. -/
def modifyHeap (update : Heap → Heap) : JSM P Unit := fun machine =>
  .done (.normal ()) (machine.setHeap (update machine.heap))

/-- Emits one observable event in constant time. -/
def emit (event : TraceEvent) : JSM P Unit := fun machine =>
  .done (.normal ()) (machine.emit event)

/-- Consumes one unit of meta-level execution fuel. -/
def consumeFuel : JSM P Unit := fun machine =>
  match machine.consumeFuel with
  | some next => .done (.normal ()) next
  | none => .exhausted machine

/-- Produces a JavaScript return completion. -/
def returnJS (value : Value) : JSM P α := fun machine => .done (.returned value) machine

/-- Produces a JavaScript throw completion. -/
def throwJS (value : Value) : JSM P α := fun machine => .done (.thrown value) machine

/-- Produces a JavaScript break completion. -/
def breakJS (label : Option JSString := none) : JSM P α := fun machine =>
  .done (.break label) machine

/-- Produces a JavaScript continue completion. -/
def continueJS (label : Option JSString := none) : JSM P α := fun machine =>
  .done (.continue label) machine

end JSM
end TSLean.JS
