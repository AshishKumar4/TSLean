import TSLean.JS.Conversion
import TSLean.JS.Equality
import TSLean.JS.Heap
import TSLean.Refinement.Heap
import TSLean.LeanToTypeScript.Semantics.Assumption
import TSLean.LeanToTypeScript.Semantics.Ir

/-!
# Target semantics: the emitted TypeScript fragment, over the JavaScript model

`Target.Expr` is the set of TypeScript expression shapes `src/lean-to-typescript/emitter.ts`
constructs for an IR operation, and nothing else. Its semantics runs on `TSLean.JS.Value` and
`TSLean.JS.Heap` — the same ECMAScript value and object model the rest of this repository is
verified against — so the target side of the refinement is a JavaScript semantics rather than a
second idea of what JavaScript is.

A JavaScript function object has an internal callable closure as well as its heap identity. The heap
continues to own the JavaScript object and its own captured-binder properties; `State.closures` owns
the object's internal code, compiled body and captured scope. That is one function object with its
ordinary own properties and its `[[Call]]`-like semantic payload, not a program-wide arrow table or
a host callback. An invocation finds the payload by the object reference, reads the exact captured
properties back out of the heap, checks they still agree with the payload, then evaluates the stored
body.

Three kinds of outcome are distinguished, because a compiler is only correct if it avoids two of
them:

* `thrown` is a JavaScript exception the emitted program itself would raise, currently only the
  `TypeError` from reading a property of `undefined`.
* `fault` is a model failure: a heap invariant refusal, an unmodeled observation, or an inconsistent
  function object. Compiled code reaching one is a hole in the model, and `Preservation` proves
  compiled code never does.
* `exhausted` is entry-fuel exhaustion, matching the source semantics exactly.
-/

namespace TSLean.LeanToTypeScript.Semantics

open TSLean.JS

namespace Target

mutual

/-- An emitted TypeScript expression. Every constructor is a shape `emitter.ts` builds. -/
inductive Expr where
  /-- A parameter or `const` reference, resolved positionally as `emitter.ts` resolves it. -/
  | binding (index : Nat)
  /-- `true` or `false`. -/
  | boolLit (value : Bool)
  /-- `undefined`. -/
  | undefinedLit
  /-- A string literal, the representation of a nullary structural tag. -/
  | stringLit (value : String)
  /-- `target.name`. -/
  | member (target : Expr) (name : String)
  /-- `condition ? consequent : alternate`. -/
  | conditional (condition consequent alternate : Expr)
  /-- `left === right`. -/
  | strictEquals (left right : Expr)
  /-- `left && right`. -/
  | logicalAnd (left right : Expr)
  /-- `left || right`. -/
  | logicalOr (left right : Expr)
  /-- `!operand`. -/
  | logicalNot (operand : Expr)
  /-- `{ name: value, … }`, in the listed order. -/
  | objectLiteral (properties : List (String × Expr))
  /-- `name(argument, …)`. -/
  | callFunction (name : String) (arguments : List Expr)
  /-- A bigint literal, which is how a `Nat` reaches the target exactly at every magnitude. -/
  | bigintLit (value : Nat)
  /-- One runtime opcode applied to its emitted operands. The first-order opcodes denote the engine
  operation the `Runtime` model names. The six higher-order list opcodes do not: their callback is a
  real function object, so the emitted `value.map((element) => transform(element))` enters it once
  per element, and the target semantics runs that entry rather than applying a Lean function. -/
  | operation (opcode : Ir.Opcode) (arguments : List Expr)
  /-- An inline arrow. `code` is semantic provenance for its anonymous trace event; `body` is the
  executable emitted body stored by the function object itself. -/
  | arrow (code : Ir.LambdaCode) (body : Body)
  /-- `callee(argument, …)`, where Coverage v5 has already restricted `callee` to a binding. -/
  | callValue (callee : Expr) (arguments : List Expr)
  deriving Repr

/-- An emitted function body: a run of `const` statements ending in one `return`. -/
inductive Body where
  | constBind (name : String) (value : Expr) (rest : Body)
  | ret (value : Expr)
  deriving Repr

end

/-- The internal callable payload of one heap-allocated arrow object. `code` labels the anonymous
entry in traces. `body` is authoritative when applying this object. `captured` is the positional
scope captured at allocation and is checked against the object's own data properties on every call. -/
structure Closure where
  code : Ir.LambdaCode
  body : Body
  captured : List Value

/-- One emitted function declaration. -/
structure Function where
  name : String
  parameters : Nat
  body : Body
  deriving Repr

/-- One emitted module: the declared functions it contributes. Inline arrows live in expressions and
allocate their own callable payloads; there is deliberately no program arrow table. -/
structure Program where
  functions : List Function
  deriving Repr

/-- The function a name declares. -/
def Program.find? (program : Program) (name : String) : Option Function :=
  program.functions.find? fun declaration => declaration.name == name

/-- One observable entry. A declared call identifies its function name. An inline application carries
its exact lambda code, so two distinct anonymous bodies cannot refine each other merely because they
were called with the same values. -/
inductive Event where
  | function (name : String) (arguments : List Value)
  | application (code : Ir.LambdaCode) (arguments : List Value)

/-- The ordered events one run produced. -/
abbrev Trace := List Event

/-- The mutable state an emitted expression can reach: the JavaScript heap, the events so far, and
internal payloads for live function objects. -/
structure State where
  heap : Heap
  trace : Trace
  closures : List (RefId × Closure)

/-- A JavaScript exception the emitted fragment can raise. -/
inductive Thrown where
  /-- Reading a property of `undefined` or `null`. -/
  | typeError
  deriving DecidableEq, Repr

/-- A failure of the model rather than of the program. -/
inductive Fault where
  /-- A positional binding reference with no binding, which `emitter.ts` refuses to emit. -/
  | unboundBinding (index : Nat)
  /-- A call to a function the module does not declare. -/
  | undeclaredFunction (function : String)
  /-- The heap refused an allocation or a read. -/
  | heap (fault : HeapFault)
  /-- The heap refused a property definition. -/
  | property (fault : DefinePropertyFault)
  /-- A property definition the heap invariants rejected. -/
  | propertyRejected (name : String)
  /-- An accessor property was read. This model does not evaluate getters. -/
  | accessorRead (name : String)
  /-- A property of a primitive other than `undefined` or `null` was read. This model does not box
  primitives, so it gives no meaning to the read. -/
  | primitiveMember (name : String)
  /-- A value was called that is not one of this model's live arrow objects. -/
  | notAnArrow
  /-- The heap properties an arrow call read differ from the closure payload that allocated them. -/
  | capturedScopeMismatch (ref : RefId)
  /-- An operand an opcode requires to be a dense array, and which is not. -/
  | notAnArray
  /-- An opcode applied to the wrong number of emitted operands. -/
  | operandCount (opcode : Ir.Opcode) (actual : Nat)
  deriving DecidableEq

/-- The result of running one emitted expression. -/
inductive Result where
  | ok (value : Value) (state : State)
  | thrown (error : Thrown) (state : State)
  | fault (fault : Fault) (state : State)
  | exhausted (state : State)

/-- The result of running a list of emitted expressions left to right. -/
inductive ListResult where
  | ok (values : List Value) (state : State)
  | thrown (error : Thrown) (state : State)
  | fault (fault : Fault) (state : State)
  | exhausted (state : State)

/-- The result of running an object literal's property values left to right. -/
inductive NamedListResult where
  | ok (properties : List (String × Value)) (state : State)
  | thrown (error : Thrown) (state : State)
  | fault (fault : Fault) (state : State)
  | exhausted (state : State)

/-- The value bound at a positional index, innermost binding first. -/
def lookup (scope : List Value) (index : Nat) : Option Value := scope[index]?

/-- The callable payload a live function object owns. -/
def State.lookupClosure (state : State) (ref : RefId) : Option Closure :=
  (state.closures.find? fun entry => entry.1 == ref).map Prod.snd

/-- Registers the internal payload of a newly allocated function object. New payloads append so a
previously resolved live reference keeps resolving to the exact payload it already carried. -/
def State.registerClosure (state : State) (ref : RefId) (closure : Closure) : State :=
  { state with closures := state.closures ++ [(ref, closure)] }

/-- Records one function entry. -/
def State.record (state : State) (event : Event) : State :=
  { state with trace := state.trace ++ [event] }

/-- Replaces the committed heap while retaining the trace and every function object's internal slot. -/
def State.withHeap (state : State) (heap : Heap) : State := { state with heap }

/-- A state stores only live function objects, and every stored captured value is live in its heap. -/
def State.ClosuresWellFormed (state : State) : Prop :=
  ∀ ref closure, state.lookupClosure ref = some closure →
    state.heap.valueValid (.object ref) = true ∧
      ∀ value ∈ closure.captured, state.heap.valueValid value = true

/-- A state transition extends the heap exactly and preserves every pre-existing callable payload. -/
structure State.Extension (old next : State) : Prop where
  heap : TSLean.Refinement.Heap.ExactExtension old.heap next.heap
  closures : ∀ ref closure, old.lookupClosure ref = some closure →
    next.lookupClosure ref = some closure

/-- The empty state transition. -/
theorem State.Extension.refl (state : State) (heapValid : state.heap.WellFormed) :
    State.Extension state state :=
  ⟨TSLean.Refinement.Heap.ExactExtension.refl state.heap heapValid, fun _ _ found => found⟩

/-- Exact state extensions compose. -/
theorem State.Extension.trans {first second third : State}
    (left : State.Extension first second) (right : State.Extension second third) :
    State.Extension first third :=
  ⟨left.heap.trans right.heap, fun ref closure found => right.closures ref closure (left.closures ref closure found)⟩

/-- A later state in an exact extension has a well-formed heap. -/
theorem State.Extension.nextWellFormed {old next : State}
    (extension : State.Extension old next) : next.heap.WellFormed := extension.heap.nextWellFormed

/-- Reading an own data property or an absent own key. -/
def readMember (state : State) (name : String) (target : Value) : Result :=
  match target with
  | .primitive .undefined | .primitive .null => .thrown .typeError state
  | .primitive _ => .fault (.primitiveMember name) state
  | .object ref =>
      match state.heap.getOwnProperty ref (Ir.propertyKey name) with
      | .error fault => .fault (.heap fault) state
      | .ok none => .ok (.primitive .undefined) state
      | .ok (some (.data descriptor)) => .ok descriptor.value state
      | .ok (some (.accessor _)) => .fault (.accessorRead name) state

/-- Defines the remaining own data properties of a fresh object literal, in listed order. -/
def defineProperties (ref : RefId) (state : State) : List (String × Value) → Result
  | [] => .ok (.object ref) state
  | (name, value) :: rest =>
      match state.heap.createDataProperty ref (Ir.propertyKey name) value with
      | .error fault => .fault (.property fault) state
      | .ok (false, _) => .fault (.propertyRejected name) state
      | .ok (true, heap) => defineProperties ref (state.withHeap heap) rest

/-- Allocates one object literal and defines its own data properties in listed order. -/
def allocateLiteral (state : State) (properties : List (String × Value)) : Result :=
  match state.heap.allocate none true with
  | .error fault => .fault (.heap fault) state
  | .ok (ref, heap) => defineProperties ref (state.withHeap heap) properties

/-- Reads the captured scope out of an arrow object, one own property per binder, in scope order. -/
def readCaptured (state : State) (ref : RefId) (start : Nat) : Nat → ListResult
  | 0 => .ok [] state
  | remaining + 1 =>
      match readMember state (Ir.capturedKey start) (.object ref) with
      | .ok value next =>
          match readCaptured next ref (start + 1) remaining with
          | .ok values last => .ok (value :: values) last
          | .thrown error last => .thrown error last
          | .fault fault last => .fault fault last
          | .exhausted last => .exhausted last
      | .thrown error next => .thrown error next
      | .fault fault next => .fault fault next
      | .exhausted next => .exhausted next

/-- Allocates a real function object: its ordinary own properties carry its captured binders and its
internal closure slot carries its code provenance, compiled body and captured scope. -/
def allocateClosure (state : State) (code : Ir.LambdaCode) (body : Body)
    (captured : List Value) : Result :=
  match allocateLiteral state (Ir.closureEntries captured) with
  | .ok (.object ref) next =>
      .ok (.object ref) (next.registerClosure ref ⟨code, body, captured⟩)
  | .ok _value next => .fault .notAnArrow next
  | .thrown error next => .thrown error next
  | .fault fault next => .fault fault next
  | .exhausted next => .exhausted next

/-- Appending a closure payload preserves every payload already resolved in the state. -/
theorem State.lookupClosure_register_old (state : State) (newRef : RefId) (newClosure : Closure)
    {ref : RefId} {closure : Closure}
    (found : state.lookupClosure ref = some closure) :
    (state.registerClosure newRef newClosure).lookupClosure ref = some closure := by
  simp only [State.lookupClosure, State.registerClosure, List.find?_append] at found ⊢
  cases existing : state.closures.find? (fun entry => entry.1 == ref) with
  | none => simp [existing] at found
  | some entry =>
      have entryValue : entry.2 = closure := by simpa [existing] using found
      simp [entryValue]

/-- A fresh heap reference cannot already name a live closure payload. -/
theorem State.lookupClosure_none_of_fresh (state : State) (valid : state.ClosuresWellFormed)
    (ref : RefId) (fresh : state.heap.size ≤ ref.value) : state.lookupClosure ref = none := by
  match found : state.lookupClosure ref with
  | none => rfl
  | some closure =>
      obtain ⟨live, _⟩ := valid ref closure found
      simp only [Heap.valueValid, decide_eq_true_eq] at live
      exact absurd live (by omega)

/-- A newly appended payload cannot change lookup at a different object reference, because a
beq-guarded find over the appended singleton cannot match a different reference. -/
theorem State.lookupClosure_register_ne (state : State) (newRef : RefId) (newClosure : Closure)
    {ref : RefId} (different : ref ≠ newRef) :
    (state.registerClosure newRef newClosure).lookupClosure ref = state.lookupClosure ref := by
  simp only [State.lookupClosure, State.registerClosure, List.find?_append]
  cases existing : state.closures.find? (fun entry => entry.1 == ref) with
  | none =>
      have missing : (newRef : RefId) ≠ ref := fun same => different same.symm
      simp [missing]
  | some entry =>
      have head : ¬(newRef == ref) := fun equal => different (beq_iff_eq.mp equal).symm
      simp [head]

/-- Appending the unique payload for a fresh reference makes that reference resolve to the new
closure. -/
theorem State.lookupClosure_register_self (state : State) (newRef : RefId) (newClosure : Closure)
    (missing : state.lookupClosure newRef = none) :
    (state.registerClosure newRef newClosure).lookupClosure newRef = some newClosure := by
  simp only [State.lookupClosure, State.registerClosure, List.find?_append] at missing ⊢
  cases existing : state.closures.find? (fun entry => entry.1 == newRef) with
  | none => simp
  | some entry => simp [existing] at missing

/-- Registering a fresh closure payload is an exact state extension. -/
theorem State.registerClosure_extension (state : State) (newRef : RefId) (newClosure : Closure)
    (heapValid : state.heap.WellFormed) :
    State.Extension state (state.registerClosure newRef newClosure) :=
  ⟨(State.Extension.refl state heapValid).heap,
    fun _ _ found => State.lookupClosure_register_old state newRef newClosure found⟩

/-- Recording an entry is an exact state extension: it appends to the trace and touches neither the
heap nor any live function object's callable payload. -/
theorem State.record_extension (state : State) (event : Event)
    (heapValid : state.heap.WellFormed) : State.Extension state (state.record event) :=
  ⟨(State.Extension.refl state heapValid).heap, fun _ _ found => found⟩

/-- Binds a call's arguments to a declared parameter count the way a JavaScript call does: a missing
argument becomes `undefined`, an extra argument is dropped. -/
def bindArguments (parameters : Nat) (arguments : List Value) : List Value :=
  match parameters with
  | 0 => []
  | count + 1 =>
      match arguments with
      | [] => .primitive .undefined :: bindArguments count []
      | value :: rest => value :: bindArguments count rest


/-- Reads the dense elements of an emitted array object, in index order. An absent index is a hole,
which the emitted fragment never produces and which is refused rather than read as `undefined`. -/
def readIndices (heap : Heap) (ref : RefId) : Nat → Nat → Except Fault (List Value)
  | _, 0 => .ok []
  | index, remaining + 1 =>
      match heap.getOwnProperty ref (.string (PropertyKey.arrayIndexString index)) with
      | .error fault => .error (.heap fault)
      | .ok (some (.data descriptor)) =>
          match readIndices heap ref (index + 1) remaining with
          | .ok rest => .ok (descriptor.value :: rest)
          | .error fault => .error fault
      | .ok _ => .error .notAnArray

/-- The elements an emitted array value carries, in index order. -/
def readArray (state : State) : Value → Except Fault (List Value)
  | .object ref =>
      match state.heap.arrayLength ref with
      | .error fault => .error (.heap fault)
      | .ok length => readIndices state.heap ref 0 length
  | .primitive _ => .error .notAnArray

/-- Allocates an emitted array carrying these elements, in order. -/
def allocateArray (state : State) (elements : List Value) : Result :=
  match state.heap.allocateArray (elements.map some) with
  | .error fault => .fault (.property fault) state
  | .ok (ref, heap) => .ok (.object ref) (state.withHeap heap)

/-- Builds the emitted tagged object one `Option` image denotes. -/
def optionValue (state : State) : OptionImage → Result
  | .absent =>
      allocateLiteral state [("kind", .primitive (.string (JSString.ofLeanString "none")))]
  | .present value =>
      allocateLiteral state
        [("kind", .primitive (.string (JSString.ofLeanString "some"))), ("value", value)]

mutual

/-- Runs one emitted expression. -/
def eval (program : Program) (runtime : Runtime) (fuel : Nat) (scope : List Value) (state : State) : Expr → Result
  | .binding index =>
      match lookup scope index with
      | some value => .ok value state
      | none => .fault (.unboundBinding index) state
  | .boolLit value => .ok (.primitive (.boolean value)) state
  | .undefinedLit => .ok (.primitive .undefined) state
  | .stringLit value => .ok (.primitive (.string (JSString.ofLeanString value))) state
  | .bigintLit value => .ok (.primitive (.bigint value)) state
  | .operation opcode arguments =>
      match evalList program runtime fuel scope state arguments with
      | .ok operands next => runOperation program runtime fuel next opcode operands
      | .thrown error next => .thrown error next
      | .fault fault next => .fault fault next
      | .exhausted next => .exhausted next
  | .member target name =>
      match eval program runtime fuel scope state target with
      | .ok value next => readMember next name value
      | other => other
  | .conditional condition consequent alternate =>
      match eval program runtime fuel scope state condition with
      | .ok value next => if value.toBoolean then eval program runtime fuel scope next consequent
          else eval program runtime fuel scope next alternate
      | other => other
  | .strictEquals left right =>
      match eval program runtime fuel scope state left with
      | .ok first next =>
          match eval program runtime fuel scope next right with
          | .ok second last => .ok (.primitive (.boolean (strictEqual first second))) last
          | other => other
      | other => other
  | .logicalAnd left right =>
      match eval program runtime fuel scope state left with
      | .ok first next => if first.toBoolean then eval program runtime fuel scope next right else .ok first next
      | other => other
  | .logicalOr left right =>
      match eval program runtime fuel scope state left with
      | .ok first next => if first.toBoolean then .ok first next else eval program runtime fuel scope next right
      | other => other
  | .logicalNot operand =>
      match eval program runtime fuel scope state operand with
      | .ok value next => .ok (.primitive (.boolean (!value.toBoolean))) next
      | other => other
  | .objectLiteral properties =>
      match evalProperties program runtime fuel scope state properties with
      | .ok values next => allocateLiteral next values
      | .thrown error next => .thrown error next
      | .fault fault next => .fault fault next
      | .exhausted next => .exhausted next
  | .callFunction name arguments =>
      match evalList program runtime fuel scope state arguments with
      | .ok values next => enter program runtime fuel next name values
      | .thrown error next => .thrown error next
      | .fault fault next => .fault fault next
      | .exhausted next => .exhausted next
  | .arrow code body => allocateClosure state code body scope
  | .callValue callee arguments =>
      match eval program runtime fuel scope state callee with
      | .ok value next =>
          match evalList program runtime fuel scope next arguments with
          | .ok values last => invoke program runtime fuel last value values
          | .thrown error last => .thrown error last
          | .fault fault last => .fault fault last
          | .exhausted last => .exhausted last
      | other => other
termination_by expression => (fuel, 3, sizeOf expression)

/--
Runs one runtime opcode on already evaluated operands.

The first-order opcodes denote the engine operation the `Runtime` model names, and cost neither fuel
nor a trace entry. The six higher-order list opcodes are different in kind: their callback operand
is a live function object, so the emitted `value.map((element) => transform(element))` enters it once
per element. This runs those entries, which is why they spend fuel and record their own application
entries, in element order.
-/
def runOperation (program : Program) (runtime : Runtime) (fuel : Nat) (state : State)
    (opcode : Ir.Opcode) (operands : List Value) : Result :=
  match opcode, operands with
  | .boolAnd, [left, right] => .ok (runtime.boolAnd left right) state
  | .boolOr, [left, right] => .ok (runtime.boolOr left right) state
  | .boolNot, [operand] => .ok (runtime.boolNot operand) state
  | .boolEquals, [left, right] => .ok (runtime.boolEquals left right) state
  | .natAdd, [left, right] => .ok (runtime.natAdd left right) state
  | .natSubtract, [left, right] => .ok (runtime.natSubtract left right) state
  | .natMultiply, [left, right] => .ok (runtime.natMultiply left right) state
  | .natLess, [left, right] => .ok (runtime.natLess left right) state
  | .natLessOrEqual, [left, right] => .ok (runtime.natLessOrEqual left right) state
  | .natEquals, [left, right] => .ok (runtime.natEquals left right) state
  | .natSuccessor, [operand] => .ok (runtime.natSuccessor operand) state
  | .stringAppend, [left, right] => .ok (runtime.stringAppend left right) state
  | .stringEquals, [left, right] => .ok (runtime.stringEquals left right) state
  | .listLength, [subject] =>
      match readArray state subject with
      | .error fault => .fault fault state
      | .ok elements => .ok (runtime.listLength elements) state
  | .listIsEmpty, [subject] =>
      match readArray state subject with
      | .error fault => .fault fault state
      | .ok elements => .ok (runtime.listIsEmpty elements) state
  | .listFirst, [subject] =>
      match readArray state subject with
      | .error fault => .fault fault state
      | .ok elements => .ok (runtime.listFirst elements) state
  | .listRest, [subject] =>
      match readArray state subject with
      | .error fault => .fault fault state
      | .ok elements => allocateArray state (runtime.listRest elements)
  | .listReverse, [subject] =>
      match readArray state subject with
      | .error fault => .fault fault state
      | .ok elements => allocateArray state (runtime.listReverse elements)
  | .listAppend, [left, right] =>
      match readArray state left, readArray state right with
      | .ok first, .ok second => allocateArray state (runtime.listAppend first second)
      | .error fault, _ => .fault fault state
      | _, .error fault => .fault fault state
  | .listHead, [subject] =>
      match readArray state subject with
      | .error fault => .fault fault state
      | .ok elements => optionValue state (runtime.listHead elements)
  | .listMap, [callback, subject] =>
      match readArray state subject with
      | .error fault => .fault fault state
      | .ok elements =>
          match mapCalls program runtime fuel state callback elements with
          | .ok images next => allocateArray next images
          | .thrown error next => .thrown error next
          | .fault fault next => .fault fault next
          | .exhausted next => .exhausted next
  | .listFilter, [callback, subject] =>
      match readArray state subject with
      | .error fault => .fault fault state
      | .ok elements =>
          match filterCalls program runtime fuel state callback elements with
          | .ok kept next => allocateArray next kept
          | .thrown error next => .thrown error next
          | .fault fault next => .fault fault next
          | .exhausted next => .exhausted next
  | .listAny, [subject, callback] =>
      match readArray state subject with
      | .error fault => .fault fault state
      | .ok elements => anyCalls program runtime fuel state callback elements
  | .listAll, [subject, callback] =>
      match readArray state subject with
      | .error fault => .fault fault state
      | .ok elements => allCalls program runtime fuel state callback elements
  | .listFoldLeft, [callback, initial, subject] =>
      match readArray state subject with
      | .error fault => .fault fault state
      | .ok elements => foldLeftCalls program runtime fuel state callback initial elements
  | .listFoldRight, [callback, initial, subject] =>
      match readArray state subject with
      | .error fault => .fault fault state
      | .ok elements => foldRightCalls program runtime fuel state callback initial elements
  | opcode, operands => .fault (.operandCount opcode operands.length) state
termination_by (fuel, 2, 0)


/-- Enters the callback once per element, in order, keeping the images. -/
def mapCalls (program : Program) (runtime : Runtime) (fuel : Nat) (state : State) (callback : Value) :
    List Value → ListResult
  | [] => .ok [] state
  | head :: rest =>
      match invoke program runtime fuel state callback [head] with
      | .ok produced next =>
          match mapCalls program runtime fuel next callback rest with
          | .ok images last => .ok (produced :: images) last
          | other => other
      | .thrown error next => .thrown error next
      | .fault fault next => .fault fault next
      | .exhausted next => .exhausted next
termination_by elements => (fuel, 1, sizeOf elements)

/-- Enters the callback once per element, in order, keeping the elements it accepts. -/
def filterCalls (program : Program) (runtime : Runtime) (fuel : Nat) (state : State)
    (callback : Value) : List Value → ListResult
  | [] => .ok [] state
  | head :: rest =>
      match invoke program runtime fuel state callback [head] with
      | .ok decision next =>
          match filterCalls program runtime fuel next callback rest with
          | .ok kept last => .ok (if decision.toBoolean then head :: kept else kept) last
          | other => other
      | .thrown error next => .thrown error next
      | .fault fault next => .fault fault next
      | .exhausted next => .exhausted next
termination_by elements => (fuel, 1, sizeOf elements)

/-- Enters the callback once per element until one accepts. -/
def anyCalls (program : Program) (runtime : Runtime) (fuel : Nat) (state : State) (callback : Value) :
    List Value → Result
  | [] => .ok (Encode.bool false) state
  | head :: rest =>
      match invoke program runtime fuel state callback [head] with
      | .ok decision next =>
          if decision.toBoolean then .ok (Encode.bool true) next
          else anyCalls program runtime fuel next callback rest
      | .thrown error next => .thrown error next
      | .fault fault next => .fault fault next
      | .exhausted next => .exhausted next
termination_by elements => (fuel, 1, sizeOf elements)

/-- Enters the callback once per element until one refuses. -/
def allCalls (program : Program) (runtime : Runtime) (fuel : Nat) (state : State) (callback : Value) :
    List Value → Result
  | [] => .ok (Encode.bool true) state
  | head :: rest =>
      match invoke program runtime fuel state callback [head] with
      | .ok decision next =>
          if decision.toBoolean then allCalls program runtime fuel next callback rest
          else .ok (Encode.bool false) next
      | .thrown error next => .thrown error next
      | .fault fault next => .fault fault next
      | .exhausted next => .exhausted next
termination_by elements => (fuel, 1, sizeOf elements)

/-- Folds the callback over the elements from the left, accumulator first. -/
def foldLeftCalls (program : Program) (runtime : Runtime) (fuel : Nat) (state : State)
    (callback accumulator : Value) : List Value → Result
  | [] => .ok accumulator state
  | head :: rest =>
      match invoke program runtime fuel state callback [accumulator, head] with
      | .ok produced next => foldLeftCalls program runtime fuel next callback produced rest
      | .thrown error next => .thrown error next
      | .fault fault next => .fault fault next
      | .exhausted next => .exhausted next
termination_by elements => (fuel, 1, sizeOf elements)

/-- Folds the callback over the elements from the right, element first, matching `reduceRight`. -/
def foldRightCalls (program : Program) (runtime : Runtime) (fuel : Nat) (state : State)
    (callback accumulator : Value) : List Value → Result
  | [] => .ok accumulator state
  | head :: rest =>
      match foldRightCalls program runtime fuel state callback accumulator rest with
      | .ok produced next => invoke program runtime fuel next callback [head, produced]
      | .thrown error next => .thrown error next
      | .fault fault next => .fault fault next
      | .exhausted next => .exhausted next
termination_by elements => (fuel, 1, sizeOf elements)

/-- Enters one declared function on already evaluated arguments. -/
def enter (program : Program) (runtime : Runtime) (fuel : Nat) (state : State) (name : String)
    (arguments : List Value) : Result :=
  match program.find? name with
  | none => .fault (.undeclaredFunction name) state
  | some declaration =>
      match fuel with
      | 0 => .exhausted state
      | remaining + 1 =>
          evalBody program runtime remaining (bindArguments declaration.parameters arguments).reverse
            (state.record (.function name arguments)) declaration.body
termination_by (fuel, 0, 0)

/-- Invokes the callable payload held by a real arrow object. The payload's body is authoritative;
the heap's captured properties are read and checked before use so an inconsistent object is a model
fault, never a silently different closure. -/
def invoke (program : Program) (runtime : Runtime) (fuel : Nat) (state : State) (callee : Value)
    (arguments : List Value) : Result :=
  match callee with
  | .primitive _ => .fault .notAnArrow state
  | .object ref =>
      match state.lookupClosure ref with
      | none => .fault .notAnArrow state
      | some closure =>
          match readCaptured state ref 0 closure.captured.length with
          | .ok captured next =>
              if captured = closure.captured then
                match fuel with
                | 0 => .exhausted next
                | remaining + 1 =>
                    evalBody program runtime remaining
                      ((bindArguments closure.code.parameters.length arguments).reverse ++ captured)
                      (next.record (.application closure.code arguments)) closure.body
              else .fault (.capturedScopeMismatch ref) next
          | .thrown error next => .thrown error next
          | .fault fault next => .fault fault next
          | .exhausted next => .exhausted next
termination_by (fuel, 0, 0)

/-- Runs one emitted function body: the `const` run, then the `return`. -/
def evalBody (program : Program) (runtime : Runtime) (fuel : Nat) (scope : List Value) (state : State) : Body → Result
  | .ret value => eval program runtime fuel scope state value
  | .constBind _ value rest =>
      match eval program runtime fuel scope state value with
      | .ok bound next => evalBody program runtime fuel (bound :: scope) next rest
      | other => other
termination_by body => (fuel, 3, sizeOf body)

/-- Runs a list of emitted expressions left to right. -/
def evalList (program : Program) (runtime : Runtime) (fuel : Nat) (scope : List Value) (state : State) :
    List Expr → ListResult
  | [] => .ok [] state
  | expression :: rest =>
      match eval program runtime fuel scope state expression with
      | .ok value next =>
          match evalList program runtime fuel scope next rest with
          | .ok values last => .ok (value :: values) last
          | .thrown error last => .thrown error last
          | .fault fault last => .fault fault last
          | .exhausted last => .exhausted last
      | .thrown error next => .thrown error next
      | .fault fault next => .fault fault next
      | .exhausted next => .exhausted next
termination_by expressions => (fuel, 3, sizeOf expressions)

/-- Runs an object literal's property values left to right, keeping the listed order. -/
def evalProperties (program : Program) (runtime : Runtime) (fuel : Nat) (scope : List Value) (state : State) :
    List (String × Expr) → NamedListResult
  | [] => .ok [] state
  | (name, expression) :: rest =>
      match eval program runtime fuel scope state expression with
      | .ok value next =>
          match evalProperties program runtime fuel scope next rest with
          | .ok values last => .ok ((name, value) :: values) last
          | .thrown error last => .thrown error last
          | .fault fault last => .fault fault last
          | .exhausted last => .exhausted last
      | .thrown error next => .thrown error next
      | .fault fault next => .fault fault next
      | .exhausted next => .exhausted next
termination_by properties => (fuel, 3, sizeOf properties)

end

end Target

end TSLean.LeanToTypeScript.Semantics
