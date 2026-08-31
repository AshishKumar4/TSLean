import TSLean.LeanToTypeScript.Semantics.Allocation
import TSLean.LeanToTypeScript.Semantics.Compile

/-!
# The inline arrow object

An emitted arrow is a heap-allocated function object, not an abstract callback. Its ordinary own
data properties carry one captured binder per enclosing scope position. Its internal callable payload
carries the exact inline lambda code and the compiled body. The object reference owns that payload;
no program-wide arrow table and no host callback mediates application.

Coverage v5 fixes the two constraints that make this representation complete: an `apply` target is
always a bound variable, and a lambda captures only the enclosing binders already in scope at its
position. Allocation stores that exact scope. Invocation reads it back in order and executes the
body held by that same object.
-/

namespace TSLean.LeanToTypeScript.Semantics

open TSLean.JS

namespace Closure

/-- Appending a fresh callable payload preserves closure-state validity and makes the new payload
live at its reference. -/
private theorem register_wellFormed (state : Target.State) (ref : RefId) (closure : Target.Closure)
    (stateValid : state.ClosuresWellFormed) (missing : state.lookupClosure ref = none)
    (refValid : state.heap.valueValid (.object ref) = true)
    (capturesValid : ∀ value ∈ closure.captured, state.heap.valueValid value = true) :
    (state.registerClosure ref closure).ClosuresWellFormed := by
  intro observedRef observedClosure found
  by_cases same : observedRef = ref
  · rw [same] at found ⊢
    rw [Target.State.lookupClosure_register_self state ref closure missing] at found
    injection found with closureEq
    subst closureEq
    exact ⟨refValid, capturesValid⟩
  · rw [Target.State.lookupClosure_register_ne state ref closure same] at found
    exact stateValid observedRef observedClosure found

/--
An inline arrow allocates one fresh heap object carrying exactly its captured binders as own data
properties, then installs the object's callable payload with its exact lambda code and compiled body.
The heap grows without changing older objects; older callable payloads remain available; the trace
and fuel do not change.
-/
theorem allocate_shape (state : Target.State) (code : Ir.LambdaCode) (body : Target.Body)
    (captured : List Value) (heapValid : state.heap.WellFormed)
    (closuresValid : state.ClosuresWellFormed)
    (valuesValid : ∀ value ∈ captured, state.heap.valueValid value = true) :
    ∃ ref final,
      Target.allocateClosure state code body captured = .ok (.object ref) final ∧
        final.trace = state.trace ∧ Target.State.Extension state final ∧
          final.ClosuresWellFormed ∧
            final.lookupClosure ref = some ⟨code, body, captured⟩ ∧
              Relation.HasOwnFields final.heap ref (Ir.closureEntries captured) := by
  obtain ⟨ref, allocated, allocatedRun, traceEq, closuresEq, allocationExtension,
    allocatedValid, fresh, shape⟩ :=
    Allocation.allocateLiteral_shape state (Ir.closureEntries captured) heapValid closuresValid
      (Ir.closureEntries_valid captured) (Ir.closureEntries_nodup captured)
      (fun entry member => valuesValid entry.2 (Ir.capturedEntries_mem 0 captured entry member))
  have missingStart : state.lookupClosure ref = none :=
    Target.State.lookupClosure_none_of_fresh state closuresValid ref fresh
  have missingAllocated : allocated.lookupClosure ref = none := by
    simpa [Target.State.lookupClosure, closuresEq] using missingStart
  let closure : Target.Closure := ⟨code, body, captured⟩
  have self : (allocated.registerClosure ref closure).lookupClosure ref = some closure :=
    Target.State.lookupClosure_register_self allocated ref closure missingAllocated
  have refValid : allocated.heap.valueValid (.object ref) = true :=
    Relation.valueValid_of_hasOwnFields shape
  have capturesValid : ∀ value ∈ closure.captured, allocated.heap.valueValid value = true := by
    intro value member
    exact allocationExtension.heap.preserves_valueValid value (valuesValid value member)
  have finalValid : (allocated.registerClosure ref closure).ClosuresWellFormed :=
    register_wellFormed allocated ref closure allocatedValid missingAllocated refValid
      capturesValid
  have registeredExtension : Target.State.Extension allocated (allocated.registerClosure ref closure) :=
    Target.State.registerClosure_extension allocated ref closure allocationExtension.nextWellFormed
  refine ⟨ref, allocated.registerClosure ref closure, ?_, ?_,
    allocationExtension.trans registeredExtension, finalValid, ?_, ?_⟩
  · unfold Target.allocateClosure
    rw [allocatedRun]
  · simpa [Target.State.registerClosure] using traceEq
  · simpa [closure] using self
  · simpa [closure, Target.State.registerClosure] using shape

/--
Reading the captured scope back out of an arrow object answers exactly the binders the allocation
stored, in scope order, and changes neither the heap nor the trace. The statement is over a split of
the captured scope so the induction can walk it: reading from position `taken.length` for
`rest.length` binders answers `rest`.
-/
theorem read_captured {state : Target.State} {ref : RefId} {captured : List Value}
    (shape : Relation.HasOwnFields state.heap ref (Ir.closureEntries captured)) :
    ∀ (rest taken : List Value), captured = taken ++ rest →
      Target.readCaptured state ref taken.length rest.length = .ok rest state
  | [], _, _ => rfl
  | value :: rest, taken, split => by
      have found : Target.readMember state (Ir.capturedKey taken.length) (.object ref)
          = .ok value state := by
        rw [split] at shape
        simp only [Target.readMember, shape.read (Ir.capturedKey taken.length),
          Ir.closureEntries_find_captured]
        rfl
      have step := read_captured shape rest (taken ++ [value]) (by simp [split])
      rw [show (taken ++ [value]).length = taken.length + 1 by simp] at step
      simp only [List.length_cons, Target.readCaptured, found, step]

/-- Reading the whole captured scope back answers exactly the scope the allocation stored. -/
theorem read_captured_all {state : Target.State} {ref : RefId} {captured : List Value}
    (shape : Relation.HasOwnFields state.heap ref (Ir.closureEntries captured)) :
    Target.readCaptured state ref 0 captured.length = .ok captured state := by
  simpa using read_captured shape captured [] (by simp)

end Closure

end TSLean.LeanToTypeScript.Semantics
