import TSLean.Refinement.Heap
import TSLean.LeanToTypeScript.Semantics.Source
import TSLean.LeanToTypeScript.Semantics.Target
import TSLean.LeanToTypeScript.Semantics.Compile

/-!
# The refinement relation

`Represents` is the representation relation between a source value and a JavaScript value in a target
state. It is exactly the representation `src/lean-to-typescript/emitter.ts` builds:

* a `Bool` is a JavaScript boolean;
* `Option.none` is `undefined` and `Option.some x` is whatever `x` is, which is why the exporter
  refuses a nested `Option`;
* a record is an object whose own keys are its field keys in declaration order, each a standard data
  property;
* a value of an enum with no payload anywhere is that constructor's own tag string;
* every other enum value is an object carrying `kind` and then the constructor's declared fields;
* an inline arrow is a heap object whose own properties are exactly its captured binders, and whose
  internal callable payload stores the same captured scope, the exact lambda code and the compiled
  body. The callable payload is owned by the object reference, never by a program-wide table.

`Refines` lifts that to whole runs and covers four observables: the returned value, the ordered entry
trace, failure behaviour and state extension. A source run that produces a value has to be matched by
a target run that produces a representing value, an identical trace and a state that only grows the
heap and adds new callable objects. The target may neither throw, nor reach a model fault, nor run
out of fuel on a source value.

A source run that faults is unconstrained. It is a program the exporter cannot produce, and claiming
anything about it would be claiming something unproved.
-/

namespace TSLean.LeanToTypeScript.Semantics

open TSLean.JS

namespace Relation

/-- An object whose own properties are exactly the listed fields, in the listed order, each a
standard data property. Reading any other name answers absence, so the object carries nothing the
list does not mention. -/
structure HasOwnFields (heap : Heap) (ref : RefId) (entries : List (String × Value)) : Prop where
  keys : heap.ownPropertyKeys ref = .ok (entries.map fun entry => Ir.propertyKey entry.1)
  read : ∀ name, heap.getOwnProperty ref (Ir.propertyKey name) =
    .ok ((entries.find? fun entry => entry.1 == name).map
      fun entry => .data ⟨entry.2, true, true, true⟩)

/-- An own-key answer is evidence that the reference denotes a live object. -/
theorem exists_object_of_keys {heap : Heap} {ref : RefId} {keys : List PropertyKey}
    (found : heap.ownPropertyKeys ref = .ok keys) : ∃ object, heap.get? ref = .ok object := by
  match lookup : heap.get? ref with
  | .ok object => exact ⟨object, rfl⟩
  | .error fault =>
      unfold Heap.ownPropertyKeys at found
      rw [lookup] at found
      simp at found

/-- An object satisfying the record shape is a valid heap reference. -/
theorem valueValid_of_hasOwnFields {heap : Heap} {ref : RefId} {entries : List (String × Value)}
    (shape : HasOwnFields heap ref entries) : heap.valueValid (.object ref) = true := by
  obtain ⟨object, found⟩ := exists_object_of_keys shape.keys
  have valid := Heap.get?_ok_valid heap ref object found
  unfold Heap.valueValid
  exact decide_eq_true valid

/-- The record shape survives a heap extension that changes no existing object. -/
theorem HasOwnFields.stable {old next : Heap} {ref : RefId} {entries : List (String × Value)}
    (extension : TSLean.Refinement.Heap.ExactExtension old next)
    (shape : HasOwnFields old ref entries) : HasOwnFields next ref entries := by
  obtain ⟨object, found⟩ := exists_object_of_keys shape.keys
  refine ⟨?_, ?_⟩
  · rw [extension.preserves_ownPropertyKeys ref object found]
    exact shape.keys
  · intro name
    rw [extension.preserves_getOwnProperty ref object found (Ir.propertyKey name)]
    exact shape.read name

/-- The heap object at `ref` is a dense array carrying exactly these images, in order. It is stated
through `Target.readArray`, the very function the target semantics reads arrays with, so the relation
and the semantics cannot drift apart. -/
def HasDenseElements (state : Target.State) (ref : RefId) (images : List Value) : Prop :=
  Target.readArray state (.object ref) = .ok images

mutual

/-- How one source value is represented in the target state. -/
def Represents (program : Ir.Program) (state : Target.State) : Source.Value → Value → Prop
  | .boolean value, target => target = .primitive (.boolean value)
  | .nat value, target => target = .primitive (.bigint value)
  | .string value, target => target = .primitive (.string (JSString.ofLeanString value))
  | .record _ fields, target =>
      ∃ (ref : RefId) (entries : List (String × Value)),
        target = .object ref ∧ RepresentsFields program state fields entries ∧
          HasOwnFields state.heap ref entries
  | .variant (.list _) "nil" [], target =>
      ∃ ref : RefId, target = .object ref ∧ HasDenseElements state ref []
  | .variant (.list _) "cons" [head, tail], target =>
      ∃ (ref tailRef : RefId) (headImage : Value) (rest : List Value),
        target = .object ref ∧ Represents program state head headImage ∧
          Represents program state tail (.object tailRef) ∧
          HasDenseElements state tailRef rest ∧
          HasDenseElements state ref (headImage :: rest)
  | .variant type name arguments, target =>
      ∃ constructors, program.constructorsOf type = some constructors ∧
        ∃ constructor, Ir.constructor? constructors name = some constructor ∧
          (if Ir.allNullary constructors = true then
              arguments = [] ∧ target = .primitive (.string (JSString.ofLeanString name))
            else
              ∃ (ref : RefId) (entries : List (String × Value)),
                target = .object ref ∧
                  RepresentsArguments program state constructor.fields arguments entries ∧
                  HasOwnFields state.heap ref
                    (("kind", .primitive (.string (JSString.ofLeanString name))) :: entries))
  | .closure captured parameters body, target =>
      ∃ (ref : RefId) (closure : Target.Closure),
        target = .object ref ∧ state.lookupClosure ref = some closure ∧
          closure.code = ⟨parameters, body⟩ ∧ Compile.body program body = .ok closure.body ∧
          RepresentsList program state captured closure.captured ∧
          HasOwnFields state.heap ref (Ir.closureEntries closure.captured)
termination_by value => sizeOf value

/-- A record's fields represented pointwise, keeping names and order. -/
def RepresentsFields (program : Ir.Program) (state : Target.State) :
    List (String × Source.Value) → List (String × Value) → Prop
  | [], entries => entries = []
  | (name, value) :: fields, entries =>
      ∃ (target : Value) (rest : List (String × Value)),
        entries = (name, target) :: rest ∧ Represents program state value target ∧
          RepresentsFields program state fields rest
termination_by fields => sizeOf fields

/-- A constructor's declared fields paired with the argument values they carry. -/
def RepresentsArguments (program : Ir.Program) (state : Target.State) :
    List Ir.Field → List Source.Value → List (String × Value) → Prop
  | fields, [], entries => fields = [] ∧ entries = []
  | fields, value :: rest, entries =>
      ∃ (field : Ir.Field) (remaining : List Ir.Field) (target : Value)
        (restEntries : List (String × Value)),
        fields = field :: remaining ∧ entries = (field.name, target) :: restEntries ∧
          Represents program state value target ∧
          RepresentsArguments program state remaining rest restEntries
termination_by _ arguments _ => sizeOf arguments

/-- A list of source values represented pointwise. -/
def RepresentsList (program : Ir.Program) (state : Target.State) :
    List Source.Value → List Value → Prop
  | [], targets => targets = []
  | value :: rest, targets =>
      ∃ (target : Value) (restTargets : List Value),
        targets = target :: restTargets ∧ Represents program state value target ∧
          RepresentsList program state rest restTargets
termination_by values => sizeOf values

end

/-- One source trace event and one target trace event are the same entry at representing arguments. -/
def RefinesEvent (program : Ir.Program) (state : Target.State) : Source.Event → Target.Event → Prop
  | .function function arguments, .function targetFunction targetArguments =>
      function = targetFunction ∧ RepresentsList program state arguments targetArguments
  | .application code arguments, .application targetCode targetArguments =>
      code = targetCode ∧ RepresentsList program state arguments targetArguments
  | _, _ => False

/-- Two traces record the same entries in the same order. -/
def RefinesTrace (program : Ir.Program) (state : Target.State) : Source.Trace → Target.Trace → Prop
  | [], target => target = []
  | event :: rest, target =>
      ∃ (entry : Target.Event) (restTarget : Target.Trace),
        target = entry :: restTarget ∧ RefinesEvent program state event entry ∧
          RefinesTrace program state rest restTarget

/-! ## Framing -/

mutual

/-- A dense-array read only touches an object that already exists, so an exact extension answers it
identically. -/
theorem readIndices_stable {old next : Heap} (extension : TSLean.Refinement.Heap.ExactExtension old next)
    {ref : RefId} {object : ObjectRecord} (found : old.get? ref = .ok object) :
    ∀ (count index : Nat) (images : List Value),
      Target.readIndices old ref index count = .ok images →
      Target.readIndices next ref index count = .ok images
  | 0, _, _, read => by simpa [Target.readIndices] using read
  | count + 1, index, images, read => by
      simp only [Target.readIndices] at read ⊢
      rw [extension.preserves_getOwnProperty ref object found
        (.string (PropertyKey.arrayIndexString index))]
      cases descriptor : old.getOwnProperty ref (.string (PropertyKey.arrayIndexString index)) with
      | error _ => rw [descriptor] at read; simp at read
      | ok slot =>
          rw [descriptor] at read
          match slot with
          | some (.data value) =>
              cases rest : Target.readIndices old ref (index + 1) count with
              | error _ => rw [rest] at read; simp at read
              | ok tail =>
                  rw [rest] at read
                  rw [readIndices_stable extension found count (index + 1) tail rest]
                  exact read
          | some (.accessor _) => simp at read
          | none => simp at read

/-- Dense-array representation survives an exact state extension. -/
theorem HasDenseElements.stable {old next : Target.State}
    (extension : Target.State.Extension old next) {ref : RefId} {images : List Value}
    (dense : HasDenseElements old ref images) : HasDenseElements next ref images := by
  simp only [HasDenseElements, Target.readArray] at dense ⊢
  cases found : old.heap.get? ref with
  | error fault =>
      have refused : old.heap.arrayLength ref = .error fault := by
        simp only [Heap.arrayLength, found]
        rfl
      rw [refused] at dense
      simp at dense
  | ok object =>
      have carried := extension.heap.get_eq ref object found
      have lengths : next.heap.arrayLength ref = old.heap.arrayLength ref := by
        simp only [Heap.arrayLength, found, carried]
      rw [lengths]
      cases length : old.heap.arrayLength ref with
      | error _ => rw [length] at dense; simp at dense
      | ok count =>
          rw [length] at dense
          exact readIndices_stable extension.heap found count 0 images dense

/-- Representation survives an exact state extension. -/
theorem Represents.stable {program : Ir.Program} {old next : Target.State}
    (extension : Target.State.Extension old next)
    (value : Source.Value) (target : Value)
    (related : Represents program old value target) : Represents program next value target := by
  match value with
  | .boolean _ => unfold Represents at related ⊢; exact related
  | .nat _ => unfold Represents at related ⊢; exact related
  | .string _ => unfold Represents at related ⊢; exact related
  | .record type fields =>
      unfold Represents at related ⊢
      obtain ⟨ref, entries, targetEq, fieldsRelated, shape⟩ := related
      exact ⟨ref, entries, targetEq,
        RepresentsFields.stable extension fields entries fieldsRelated, shape.stable extension.heap⟩
  | .variant (.list _) "nil" [] =>
      unfold Represents at related ⊢
      obtain ⟨ref, targetEq, dense⟩ := related
      exact ⟨ref, targetEq, dense.stable extension⟩
  | .variant (.list element) "cons" [head, tail] =>
      unfold Represents at related ⊢
      obtain ⟨ref, tailRef, headImage, rest, targetEq, headRelated, tailRelated, tailDense,
        dense⟩ := related
      exact ⟨ref, tailRef, headImage, rest, targetEq,
        Represents.stable extension head headImage headRelated,
        Represents.stable extension tail (.object tailRef) tailRelated,
        tailDense.stable extension, dense.stable extension⟩
  | .variant (.list _) _ _
  | .variant (.boolean) name arguments | .variant (.nat) name arguments
  | .variant (.string) name arguments | .variant (.parameter _) name arguments
  | .variant (.named _ _) name arguments | .variant (.option _) name arguments
  | .variant (.except _ _) name arguments | .variant (.function _ _) name arguments =>
      unfold Represents at related ⊢
      obtain ⟨constructors, declared, constructor, selected, body⟩ := related
      refine ⟨constructors, declared, constructor, selected, ?_⟩
      by_cases nullary : Ir.allNullary constructors = true
      · rw [if_pos nullary] at body ⊢
        exact body
      · rw [if_neg nullary] at body ⊢
        obtain ⟨ref, entries, targetEq, argumentsRelated, shape⟩ := body
        exact ⟨ref, entries, targetEq,
          RepresentsArguments.stable extension constructor.fields arguments entries argumentsRelated,
          shape.stable extension.heap⟩
  | .closure captured parameters body =>
      unfold Represents at related ⊢
      obtain ⟨ref, closure, targetEq, found, codeEq, compiled, capturedRelated, shape⟩ := related
      exact ⟨ref, closure, targetEq, extension.closures ref closure found, codeEq, compiled,
        RepresentsList.stable extension captured closure.captured capturedRelated,
        shape.stable extension.heap⟩
termination_by sizeOf value

/-- Field representation survives an exact state extension. -/
theorem RepresentsFields.stable {program : Ir.Program} {old next : Target.State}
    (extension : Target.State.Extension old next)
    (fields : List (String × Source.Value)) (entries : List (String × Value))
    (related : RepresentsFields program old fields entries) :
    RepresentsFields program next fields entries := by
  match fields with
  | [] => unfold RepresentsFields at related ⊢; exact related
  | (name, value) :: rest =>
      unfold RepresentsFields at related ⊢
      obtain ⟨target, restEntries, entriesEq, headRelated, tailRelated⟩ := related
      exact ⟨target, restEntries, entriesEq, Represents.stable extension value target headRelated,
        RepresentsFields.stable extension rest restEntries tailRelated⟩
termination_by sizeOf fields

/-- Argument representation survives an exact state extension. -/
theorem RepresentsArguments.stable {program : Ir.Program} {old next : Target.State}
    (extension : Target.State.Extension old next)
    (fields : List Ir.Field) (arguments : List Source.Value) (entries : List (String × Value))
    (related : RepresentsArguments program old fields arguments entries) :
    RepresentsArguments program next fields arguments entries := by
  match arguments with
  | [] => unfold RepresentsArguments at related ⊢; exact related
  | value :: rest =>
      unfold RepresentsArguments at related ⊢
      obtain ⟨field, remaining, target, restEntries, fieldsEq, entriesEq, headRelated,
        tailRelated⟩ := related
      exact ⟨field, remaining, target, restEntries, fieldsEq, entriesEq,
        Represents.stable extension value target headRelated,
        RepresentsArguments.stable extension remaining rest restEntries tailRelated⟩
termination_by sizeOf arguments

/-- List representation survives an exact state extension. -/
theorem RepresentsList.stable {program : Ir.Program} {old next : Target.State}
    (extension : Target.State.Extension old next)
    (values : List Source.Value) (targets : List Value)
    (related : RepresentsList program old values targets) :
    RepresentsList program next values targets := by
  match values with
  | [] => unfold RepresentsList at related ⊢; exact related
  | value :: rest =>
      unfold RepresentsList at related ⊢
      obtain ⟨target, restTargets, targetsEq, headRelated, tailRelated⟩ := related
      exact ⟨target, restTargets, targetsEq, Represents.stable extension value target headRelated,
        RepresentsList.stable extension rest restTargets tailRelated⟩
termination_by sizeOf values

end

/-- Trace-event refinement survives an exact state extension. -/
theorem RefinesEvent.stable {program : Ir.Program} {old next : Target.State}
    (extension : Target.State.Extension old next) :
    ∀ (source : Source.Event) (target : Target.Event),
      RefinesEvent program old source target → RefinesEvent program next source target
  | .function _ _, .function _ _, related =>
      ⟨related.1, RepresentsList.stable extension _ _ related.2⟩
  | .application _ _, .application _ _, related =>
      ⟨related.1, RepresentsList.stable extension _ _ related.2⟩
  | .function _ _, .application _ _, related => related
  | .application _ _, .function _ _, related => related

/-- Trace refinement survives an exact state extension. -/
theorem RefinesTrace.stable {program : Ir.Program} {old next : Target.State}
    (extension : Target.State.Extension old next) :
    ∀ (trace : Source.Trace) (target : Target.Trace),
      RefinesTrace program old trace target → RefinesTrace program next trace target
  | [], _, related => related
  | event :: rest, _, related => by
      unfold RefinesTrace at related ⊢
      obtain ⟨entry, restTarget, targetEq, eventRelated, tailRelated⟩ := related
      exact ⟨entry, restTarget, targetEq, RefinesEvent.stable extension event entry eventRelated,
        RefinesTrace.stable extension rest restTarget tailRelated⟩

/-- The refinement between a source list outcome and a target list result. -/
def RefinesList (program : Ir.Program) (start : Target.State) :
    Source.ListOutcome → Target.ListResult → Prop
  | .values values trace, .ok targets state =>
      Target.State.Extension start state ∧ state.ClosuresWellFormed ∧
        RepresentsList program state values targets ∧ RefinesTrace program state trace state.trace
  | .exhausted trace, .exhausted state =>
      Target.State.Extension start state ∧ state.ClosuresWellFormed ∧
        RefinesTrace program state trace state.trace
  | .fault _ _, _ => True
  | _, _ => False

/-- The refinement between a source field-list outcome and a target property-list result. -/
def RefinesFields (program : Ir.Program) (start : Target.State) :
    Source.FieldsOutcome → Target.NamedListResult → Prop
  | .fields fields trace, .ok entries state =>
      Target.State.Extension start state ∧ state.ClosuresWellFormed ∧
        RepresentsFields program state fields entries ∧ RefinesTrace program state trace state.trace
  | .exhausted trace, .exhausted state =>
      Target.State.Extension start state ∧ state.ClosuresWellFormed ∧
        RefinesTrace program state trace state.trace
  | .fault _ _, _ => True
  | _, _ => False

/-- The refinement between one source outcome and one target result, over values, entries, failure
and state extension. -/
def Refines (program : Ir.Program) (start : Target.State) :
    Source.Outcome → Target.Result → Prop
  | .value value trace, .ok target state =>
      Target.State.Extension start state ∧ state.ClosuresWellFormed ∧
        Represents program state value target ∧ RefinesTrace program state trace state.trace
  | .exhausted trace, .exhausted state =>
      Target.State.Extension start state ∧ state.ClosuresWellFormed ∧
        RefinesTrace program state trace state.trace
  | .fault _ _, _ => True
  | _, _ => False

/-- A refined successful run does not raise a JavaScript exception. -/
theorem not_thrown_of_refines_value {program : Ir.Program} {start : Target.State} {value : Source.Value}
    {trace : Source.Trace} {error : Target.Thrown} {state : Target.State}
    (refines : Refines program start (.value value trace) (.thrown error state)) : False := refines

/-- A refined successful run does not reach a model fault. -/
theorem not_fault_of_refines_value {program : Ir.Program} {start : Target.State} {value : Source.Value}
    {trace : Source.Trace} {fault : Target.Fault} {state : Target.State}
    (refines : Refines program start (.value value trace) (.fault fault state)) : False := refines

/-- A refined successful run does not run out of fuel. -/
theorem not_exhausted_of_refines_value {program : Ir.Program} {start : Target.State}
    {value : Source.Value} {trace : Source.Trace} {state : Target.State}
    (refines : Refines program start (.value value trace) (.exhausted state)) : False := refines

end Relation

end TSLean.LeanToTypeScript.Semantics
