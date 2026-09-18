import TSLean.LeanToTypeScript.Semantics.Relation

/-!
# Erasure, as laws rather than as a convention

`Export.lean` drops five kinds of thing on its way from an elaborated Lean term to the IR: a
`Prop`-typed binder, a proof in argument position, a `Decidable` instance, a subtype wrapper, and a
type former's term-level index. It also drops every type argument, because the IR carries `Ty`
annotations for representation only and the emitted TypeScript carries none at all.

Each of those drops is sound for a reason, and this module states the reason as a theorem instead of
leaving it as a convention. Three of the first four are facts about Lean itself and hold for every
program; the fourth is a fact about this model's own refinement relation, so it is stated where it is
used. The fifth — the index — is the one drop that is *not* sound for every program, so its section
states both the condition that makes it sound and a witness that the condition is necessary.

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

/-! ## Term-level indices

A type former may take a parameter that is a value rather than a type: agent-core's kernel
identifier is `structure TextId (kind : IdKind)`, whose `kind` separates `TextId .run` from
`TextId .turn` in the type checker and appears in no field. Erasing such a parameter is what lets
one TypeScript type stand for the whole family.

Unlike the four erasures above, this one is **not** sound in general, and that is the point of this
section. Lean's own compiler erases a term-level index unconditionally — in
`Lean.Compiler.LCNF.toMonoType` a parameter whose LCNF type is neither `lcErased` nor a sort has its
argument replaced by `lcAny` — but Lean can afford that because its runtime boxes every value and
carries no types. Measured under the pinned toolchain, `toMonoType` answers the same mono type at two
different indices for a genuinely dependent structure as it does for a phantom-indexed one, so
reading Lean's erasure alone would erase a length index.

The condition that makes it sound for a target that carries types is that the family's content does
not depend on the index. `Phantom` below is that shape, and `Sized` is a witness that the condition
cannot be dropped: there is no uniform content type for a family whose content varies, so no single
emitted type could be correct at every index. `Export.lean:erasedDataParameters` decides the
condition per type by checking that no surviving field's type mentions the parameter, and refuses
the type by name when one does.
-/

/-- A family indexed by a term whose content does not mention the index. This is the shape
`erasedDataParameters` admits: the index is a parameter of the type and of nothing else. -/
structure Phantom (ι : Type u) (α : Type v) (_index : ι) where
  content : α

namespace Phantom

/-- Moving a value from one index to another, which is the identity on content. This map is what the
emitted program's single type *is*: one TypeScript value stands for the whole family because every
member has the same content and this transport witnesses it. -/
def reindex {ι : Type u} {α : Type v} {source target : ι} (value : Phantom ι α source) :
    Phantom ι α target := ⟨value.content⟩

/-- **Reindexing keeps the content.** The emitted value is unchanged by the index it is read at. -/
theorem reindex_content {ι : Type u} {α : Type v} {source target : ι} (value : Phantom ι α source) :
    (reindex value : Phantom ι α target).content = value.content := rfl

/-- **Reindexing is invertible.** Going to another index and back is the identity, so no information
is lost by erasing the index — the family is one type's worth of data, not many. -/
theorem reindex_reindex {ι : Type u} {α : Type v} {source target : ι} (value : Phantom ι α source) :
    (reindex (reindex value : Phantom ι α target) : Phantom ι α source) = value := rfl

/-- **Content determines the value.** Together with `reindex_content` this is the statement that the
emitted record is a faithful image: two members of the family agree exactly when their contents do,
at any pair of indices. -/
theorem eq_of_content {ι : Type u} {α : Type v} {index : ι} {left right : Phantom ι α index}
    (contents : left.content = right.content) : left = right := by
  cases left
  cases right
  simp only [mk.injEq]
  exact contents

/-- **The index is not observable.** A function of a phantom-indexed value factors through the
content, so no emitted program can tell which index its argument was built at. That is why dropping
the index cannot change what a generated function computes. -/
theorem function_factors_through_content {ι : Type u} {α : Type v} {β : Sort w} {index : ι}
    (function : α → β) (value : Phantom ι α index) :
    function value.content = function (reindex value : Phantom ι α index).content := rfl

end Phantom

/-! ### Why the condition is necessary

`Sized` is a family whose content genuinely depends on its index. It is the `Vector α n` case in its
smallest honest form: at one index the content type is inhabited and at the other it is empty, so
there is no uniform content type and therefore no `reindex`. A compiler that erased this index would
be claiming a value exists where none can.
-/

/-- A family whose content type varies with the index. -/
def Sized : Bool → Type
  | true => Unit
  | false => Empty

/-- **A dependent index has no uniform content type.** There is no single type the family's content
always is, so one emitted TypeScript type cannot be correct at every index and the type former is
refused rather than erased. -/
theorem sized_not_uniform : Sized true ≠ Sized false := fun uniform =>
  (uniform ▸ (() : Sized true) : Sized false).elim

/-- The same fact as the statement `erasedDataParameters` is written against: it is not the case that
every term index admits a uniform content type, so erasability has to be decided per type. -/
theorem index_erasability_is_not_universal :
    ¬ ∀ (left right : Bool), Sized left = Sized right :=
  fun uniform => sized_not_uniform (uniform true false)

/-- **A phantom index, by contrast, admits a transport in both directions.** `reindex` is its own
inverse between any two indices, so the family is one type's worth of data presented at many
indices — which is what makes a single emitted TypeScript type correct at every one of them. This is
the positive half of the condition `erasedDataParameters` decides; `sized_not_uniform` is why it has
to be decided rather than assumed.

`Sized` admits no such pair: a transport `Sized true → Sized false` would inhabit `Empty`. -/
theorem phantom_transport_inverse {ι : Type u} {α : Type v} (left right : ι) :
    (∀ value : Phantom ι α left,
        (Phantom.reindex (Phantom.reindex value : Phantom ι α right) : Phantom ι α left) = value) ∧
      ∀ value : Phantom ι α right,
        (Phantom.reindex (Phantom.reindex value : Phantom ι α left) : Phantom ι α right) = value :=
  ⟨fun _ => rfl, fun _ => rfl⟩

/-- **No transport exists for a dependent index.** Stated over `Sized` directly: a total map from the
inhabited index to the empty one cannot exist, so there is no emitted type that stands for both. -/
theorem sized_no_transport : ¬ ∃ _ : Sized true → Sized false, True :=
  fun ⟨transport, _⟩ => (transport ()).elim
/-! ## Universes

A universe-polymorphic declaration reaches the target with its levels gone, because TypeScript has
no universes to carry them to. The erasure is the declaration's own level-zero instance: the
exporter instantiates the level parameters at zero and exports that, so what the emitted program
computes is a declaration Lean itself elaborated rather than a level-erased approximation of one.

Two things a level could have changed are both absent from the image, and that is what makes the
instance the right one to pick. First, the type image: `Ir.Ty` has no universe form at all, so a
type's `Ty` is the same at every level its head constants could be taken at. Second, the value
image: the semantics reads a `Ty` annotation only through `Program.constructorsOf` and
`Ty.element?`, and neither mentions a level — the theorems below state exactly that, for the two
expression forms that read an annotation.

What is left is the identity of the callee, which no theorem can settle: a call at levels other
than the ones the exported body was elaborated at would be a call to another instance. The exporter
pins it by refusing such a call rather than erasing it, which is the refusal `docs/trust.md` records
for this form.
-/

/-- The type registry carries no universe: every `Ty` belongs to the finite registry `TyKind.all`,
which has no form for a level. A type's image is therefore the same at every level, which is what
lets the exporter export one instance rather than one per level. -/
theorem no_universe_type_form (type : Ir.Ty) : type.kind ∈ Ir.TyKind.all :=
  Ir.TyKind.mem_all type.kind

/--
The one way `Source.eval` reads a `match`'s type annotation: structural equality against the
annotation the scrutinised value carries, and nothing else.

That is what makes a level unobservable rather than merely unrecorded. The equality is decided on
`Ir.Ty`, whose grammar `no_universe_type_form` shows has no form for a universe, so two
instantiations of one Lean type produce one annotation and are decided identically.
-/
theorem eval_matchOn_reads_annotation {program : Ir.Program} {fuel : Nat}
    {scope : List Source.Value} {trace : Source.Trace} (type valueType : Ir.Ty)
    (scrutinee : Ir.Expr) (cases : List (String × Ir.Expr)) (name : String)
    (arguments : List Source.Value)
    (read : Source.eval program fuel scope trace scrutinee
      = .value (.variant valueType name arguments) trace) :
    Source.eval program fuel scope trace (.matchOn type scrutinee cases)
      = if valueType = type then Source.evalCases program fuel scope trace name arguments cases
        else .fault .notAVariant trace := by
  rw [Source.eval.eq_def]
  simp only [read]

/-- The one way `Source.eval` reads a `variant`'s type annotation: `Ty.element?`, to decide whether
the constructor builds a dense array or a tagged variant. A type carrying no element type keeps its
annotation on the value and nothing is read out of it. -/
theorem eval_variant_reads_element {program : Ir.Program} {fuel : Nat} {scope : List Source.Value}
    {trace : Source.Trace} (type : Ir.Ty) (name : String) (notList : type.element? = none) :
    Source.eval program fuel scope trace (.variant type name [])
      = .value (.variant type name []) trace := by
  rw [Source.eval.eq_def]
  simp only [Source.evalList, notList]

/-! ## A dependent match whose motive erases

A dependent match is admitted only when its motive erases to one result type. That is the condition
under which the dependent eliminator *is* the ordinary case analysis, which these two theorems
state on Lean's own eliminators: at a constant motive, `casesOn` is the `match` the fragment already
lowers. A motive that does not erase to one type has no such theorem, and the exporter refuses it by
name.
-/

/-- At a constant motive, `Bool`'s dependent eliminator is the ordinary conditional. -/
theorem bool_casesOn_constant_motive {α : Sort u} (whenFalse whenTrue : α) (value : Bool) :
    @Bool.casesOn (fun _ => α) value whenFalse whenTrue = (if value then whenTrue else whenFalse) := by
  cases value <;> rfl

/-- At a constant motive, `Nat`'s dependent eliminator is the ordinary case analysis — the very one
`MatchForms.natDecision` lowers. -/
theorem nat_casesOn_constant_motive {α : Sort u} (whenZero : α) (whenSuccessor : Nat → α)
    (value : Nat) :
    @Nat.casesOn (fun _ => α) value whenZero whenSuccessor
      = (match value with | 0 => whenZero | next + 1 => whenSuccessor next) := by
  cases value <;> rfl

/-- A motive that erases to one type is a motive no alternative can disagree with: the result type
every arm is checked against is that one type, which is what the emitted function's single return
type has to be. -/
theorem constant_motive_result {α : Sort u} {β : Sort v} (motive : α → Sort v)
    (erases : ∀ value : α, motive value = β) (value : α) : motive value = β := erases value

end Erasure

end TSLean.LeanToTypeScript.Semantics
