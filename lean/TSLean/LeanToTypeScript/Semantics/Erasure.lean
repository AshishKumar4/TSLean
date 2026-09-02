import TSLean.LeanToTypeScript.Semantics.Relation

/-!
# Erasure, as laws rather than as a convention

`Export.lean` drops four kinds of thing on its way from an elaborated Lean term to the IR: a
`Prop`-typed binder, a proof in argument position, a `Decidable` instance, and a subtype wrapper. It
also drops every type argument, because the IR carries `Ty` annotations for representation only and
the emitted TypeScript carries none at all.

Each of those drops is sound for a reason, and this module states the reason as a theorem instead of
leaving it as a convention. Three of the four are facts about Lean itself and hold for every program;
the fourth is a fact about this model's own refinement relation, so it is stated where it is used.

Nothing here is an axiom, and the file adds no premise: it is the justification the exporter's
refusals are written against.
-/

namespace TSLean.LeanToTypeScript.Semantics

open TSLean.JS

namespace Erasure

/-! ## Proofs and `Prop`-typed binders

Proof irrelevance is definitional in Lean, so a function of a proof cannot observe which proof it
received. Dropping the binder therefore cannot change what the function computes — not merely for
the proofs a program happens to build, but for any two proofs of the same proposition.
-/

/-- A function of a proof answers the same value at every proof of the same proposition. -/
theorem proof_irrelevant {claim : Prop} {α : Sort u} (function : claim → α)
    (left right : claim) : function left = function right := rfl

/-- Dropping a `Prop`-typed binder is sound: the function the exporter emits, which fixes one proof,
agrees with the original at every argument the original could have been given. -/
theorem prop_binder_erasable {claim : Prop} {α : Sort u} (function : claim → α)
    (fixed : claim) : ∀ given : claim, function given = function fixed :=
  fun given => proof_irrelevant function given fixed

/-- A `Prop`-typed binder in the middle of a telescope is erasable too, so the drop composes through
a parameter list rather than only at its head. -/
theorem prop_binder_erasable_under {α : Sort u} {claim : Prop} {β : Sort v}
    (function : α → claim → β) (fixed : claim) :
    ∀ (value : α) (given : claim), function value given = function value fixed :=
  fun value given => proof_irrelevant (function value) given fixed

/-! ## `Decidable`

A `Decidable` argument becomes the `Bool` its `decide` answers. Two things make that faithful: the
`Bool` decides the proposition in both directions, and the instance itself is irrelevant, so the
exporter may pick whichever instance elaboration produced.
-/

/-- The boolean an instance answers decides its proposition, in both directions. -/
theorem decide_faithful (claim : Prop) [Decidable claim] : decide claim = true ↔ claim :=
  decide_eq_true_iff

/-- The boolean does not depend on which instance was used, so erasing the instance to its boolean
loses nothing. -/
theorem decide_instance_irrelevant (claim : Prop) (left right : Decidable claim) :
    @decide claim left = @decide claim right := by
  rw [Subsingleton.elim left right]

/-- A `Decidable`-indexed function is determined by the boolean, which is why the emitted program can
take the boolean and nothing else. -/
theorem decidable_binder_erasable {claim : Prop} {α : Sort u} (function : Bool → α)
    (left right : Decidable claim) :
    function (@decide claim left) = function (@decide claim right) := by
  rw [decide_instance_irrelevant claim left right]

/-! ## Subtypes

A subtype reaches the target as its carrier. That is faithful because the wrapper carries no data
beyond the carrier value: two subtype values with the same carrier are the same value, so the
carrier determines the value it came from.
-/

/-- A subtype value is determined by its carrier. -/
theorem subtype_carrier_determines {α : Sort u} {property : α → Prop} {left right : Subtype property}
    (carriers : left.val = right.val) : left = right := Subtype.ext carriers

/-- Reading a subtype's carrier is the identity on the value the exporter kept, so a `.val` read
erases to nothing rather than to a projection. -/
theorem subtype_val_erasable {α : Sort u} {property : α → Prop} (value : Subtype property) :
    (⟨value.val, value.property⟩ : Subtype property) = value := rfl

/-- A function of a subtype is determined by the carrier and the proof, and the proof is irrelevant,
so it is determined by the carrier alone. -/
theorem subtype_function_erasable {α : Sort u} {property : α → Prop} {β : Sort v}
    (function : Subtype property → β) (carrier : α) (left right : property carrier) :
    function ⟨carrier, left⟩ = function ⟨carrier, right⟩ := rfl

/-! ## Type arguments and universes

The IR carries a `Ty` on an array, a record and a variant, and the emitted TypeScript carries none of
them: a generated function is monomorphic in its runtime behaviour and its type parameters exist only
in the type positions the printer writes. This is where that erasure is justified.

Two of the three annotations are not read at all by the refinement relation. The third — a variant's
type — is read, but only through `constructorsOf`, so two types with the same constructor set have
the same representation. That is the precise boundary: a type parameter is erasable, and a *tag set*
is not.
-/

/-- A first-order opcode's result does not mention its type arguments. `applyStrict` takes none at
all, so erasing them is exact rather than an approximation. -/
theorem applyOperation_firstOrder_type_free {program : Ir.Program} {fuel : Nat}
    {trace : Source.Trace} {opcode : Ir.Opcode} {values : List Source.Value}
    (firstOrder : opcode.callback = false) (left right : List Ir.Ty) :
    Source.applyOperation program fuel trace opcode left values
      = Source.applyOperation program fuel trace opcode right values := by
  cases opcode <;> simp_all [Source.applyOperation, Ir.Opcode.callback]

/-- An array's element annotation is not read by the representation relation: the image is the dense
element sequence, and the sequence does not mention the type. -/
theorem represents_array_type_free {program : Ir.Program} {state : Target.State}
    (left right : Ir.Ty) (elements : List Source.Value) (image : Value)
    (related : Relation.Represents program state (.array left elements) image) :
    Relation.Represents program state (.array right elements) image := by
  unfold Relation.Represents at related ⊢
  exact related

/-- A record's type annotation is not read either: the image is the own-key sequence its field list
names. -/
theorem represents_record_type_free {program : Ir.Program} {state : Target.State}
    (left right : Ir.Ty) (fields : List (String × Source.Value)) (image : Value)
    (related : Relation.Represents program state (.record left fields) image) :
    Relation.Represents program state (.record right fields) image := by
  unfold Relation.Represents at related ⊢
  exact related

/-- A variant's annotation *is* read, and exactly through `constructorsOf`: two types declaring the
same constructors have the same variant representation. A type parameter is therefore erasable and a
tag set is not, which is why the IR keeps the annotation on a variant and the emitter keeps the tag
string. -/
theorem represents_variant_type_through_constructors {program : Ir.Program} {state : Target.State}
    (left right : Ir.Ty) (name : String) (arguments : List Source.Value) (image : Value)
    (constructors : program.constructorsOf left = program.constructorsOf right)
    (related : Relation.Represents program state (.variant left name arguments) image) :
    Relation.Represents program state (.variant right name arguments) image := by
  unfold Relation.Represents at related ⊢
  obtain ⟨declared, foundLeft, constructor, selected, body⟩ := related
  exact ⟨declared, constructors ▸ foundLeft, constructor, selected, body⟩

/-- Substituting a type's own arguments into a `parameter` index it does not reach leaves the index
open, which the compiler then refuses rather than guesses. Erasure never invents an instantiation. -/
theorem substitute_open_parameter (arguments : List Ir.Ty) (index : Nat)
    (unreached : arguments[index]? = none) :
    Ir.Ty.substitute arguments (.parameter index) = .parameter index := by
  simp [Ir.Ty.substitute, unreached]

/-- Substitution at a reached index is exactly the argument, so an instantiated annotation is the
caller's own type and not a widened one. -/
theorem substitute_reached_parameter (arguments : List Ir.Ty) (index : Nat) (argument : Ir.Ty)
    (reached : arguments[index]? = some argument) :
    Ir.Ty.substitute arguments (.parameter index) = argument := by
  simp [Ir.Ty.substitute, reached]

end Erasure

end TSLean.LeanToTypeScript.Semantics
