import TSLean.JS.Environment

namespace TSLean.JS

namespace Control

/-- Catches only JavaScript throw completion. -/
def tryCatch (action : JSM P α) (handler : Value → JSM P α) : JSM P α := fun machine =>
  match action machine with
  | .done (.thrown value) next => handler value next
  | other => other

/-- Runs finalization after any JavaScript completion with exact override semantics. -/
def tryFinally (action : JSM P α) (finalizer : JSM P Unit) : JSM P α := fun machine =>
  match action machine with
  | .done prior next =>
      match finalizer next with
      | .done finalCompletion finalMachine =>
          .done (Completion.finallyOverride prior finalCompletion) finalMachine
      | .exhausted finalMachine => .exhausted finalMachine
      | .fault fault finalMachine => .fault fault finalMachine
  | .exhausted next => .exhausted next
  | .fault fault next => .fault fault next

/-- Catch is evaluated before finally, matching ECMAScript try/catch/finally order. -/
def tryCatchFinally (action : JSM P α) (handler : Value → JSM P α)
    (finalizer : JSM P Unit) : JSM P α :=
  tryFinally (tryCatch action handler) finalizer

/-- Consumes only an unlabeled break produced by a switch body. -/
def handleSwitchBreak (action : JSM P Unit) : JSM P Unit := fun machine =>
  match action machine with
  | .done (.break none) next => .done (.normal ()) next
  | other => other

/-- Consumes a break whose label exactly matches the supplied statement label. -/
def handleLabeledBreak (label : JSString) (action : JSM P Unit) : JSM P Unit := fun machine =>
  match action machine with
  | .done (.break (some actual)) next =>
      if actual = label then .done (.normal ()) next else .done (.break (some actual)) next
  | other => other

private inductive LoopDisposition where
  | next
  | stop

private def classifyLoop (label : Option JSString) : Completion Unit → Completion LoopDisposition
  | .normal () => .normal .next
  | .break actual => if actual = none || actual = label then .normal .stop else .break actual
  | .continue actual => if actual = none || actual = label then .normal .next else .continue actual
  | .returned value => .returned value
  | .thrown value => .thrown value

/-- Handles loop-local break and continue, preserving nonmatching labeled transfers. -/
def handleLoopControl (label : Option JSString) (action : JSM P Unit) : JSM P Bool := fun machine =>
  match action machine with
  | .done completion next =>
      match classifyLoop label completion with
      | .normal .next => .done (.normal true) next
      | .normal .stop => .done (.normal false) next
      | .returned value => .done (.returned value) next
      | .thrown value => .done (.thrown value) next
      | .break actual => .done (.break actual) next
      | .continue actual => .done (.continue actual) next
  | .exhausted next => .exhausted next
  | .fault fault next => .fault fault next

private def whileLoopAux (label : Option JSString) (condition : JSM P Bool)
    (body : JSM P Unit) : Nat → JSM P Unit
  | 0 => fun machine => .exhausted machine
  | remaining + 1 => fun machine =>
      match JSM.consumeFuel machine with
      | .done (.normal ()) fueled =>
          match condition fueled with
          | .done (.normal false) next => .done (.normal ()) next
          | .done (.normal true) next =>
              match handleLoopControl label body next with
              | .done (.normal false) afterBody => .done (.normal ()) afterBody
              | .done (.normal true) afterBody => whileLoopAux label condition body remaining afterBody
              | .done (.returned value) afterBody => .done (.returned value) afterBody
              | .done (.thrown value) afterBody => .done (.thrown value) afterBody
              | .done (.break actual) afterBody => .done (.break actual) afterBody
              | .done (.continue actual) afterBody => .done (.continue actual) afterBody
              | .exhausted afterBody => .exhausted afterBody
              | .fault fault afterBody => .fault fault afterBody
          | .done (.returned value) next => .done (.returned value) next
          | .done (.thrown value) next => .done (.thrown value) next
          | .done (.break actual) next => .done (.break actual) next
          | .done (.continue actual) next => .done (.continue actual) next
          | .exhausted next => .exhausted next
          | .fault fault next => .fault fault next
      | .exhausted next => .exhausted next
      | .fault fault next => .fault fault next
      | .done completion next => .done (completion.cast id) next

/-- Fuel-bounded while execution. Each condition check consumes one unit of machine fuel. -/
def whileLoop (condition : JSM P Bool) (body : JSM P Unit)
    (label : Option JSString := none) : JSM P Unit := fun machine =>
  whileLoopAux label condition body machine.fuel machine

end Control
end TSLean.JS
