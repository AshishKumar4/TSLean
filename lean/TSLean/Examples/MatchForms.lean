/-!
# The match and binding forms, as one compiled example each

Every declaration here exercises one of the forms `docs/lean-to-typescript.md` used to refuse. Each
one lowers into IR the fragment already carries, so the emitted TypeScript is the `if`, `const` and
tag-comparison shapes the statement-form dispatch already proves, and
`TSLean/LeanToTypeScript/Semantics/MatchForms.lean` states the correspondence between each Lean form
and the decision it becomes.

## What this module does and does not evidence

Compiling is not proving, and this module is labelled so it cannot be read as more than it is.

Every declaration here compiles end to end, type-checks in its generated package, and regenerates
byte for byte — that is what `bun run lean-to-typescript:match-forms:check` establishes. Coverage by
the *refinement model* is a separate claim, and it holds for every declaration except one:
`firstOf` matches on a `List`, whose alternatives the emitter decides by a length test and by
`subject[0]`/`subject.slice(1)` reads. `Compile.returnBody` refuses that shape by name with
`Compile.listMatch`, so `firstOf`'s own lowering rests on the emitter and on differential agreement
rather than on `Preservation.branchBody`. It is here because the universe-erasure example needs a
polymorphic callee, and the *universe* claim — that the exported declaration is the level-zero
instance — is independent of how its body's `List` match is decided. `docs/trust.md` requirement 20
is the standing record of the `List` dispatch shape.

No declaration here is exhaustively enumerated against Lean's own evaluation; the roots whose
signatures allow that live in `TSLean/Examples/Roundtrip/Decisions.lean`, which
`bun run roundtrip:check` runs over its whole domain in both directions.
-/

namespace TSLean.Examples.MatchForms

/-- Which way a request was routed. -/
inductive Lane where
  | fast
  | slow

/-- Whether a request carried a credential. -/
inductive Credential where
  | present
  | absent

/-- A `Nat` pattern: the zero test comes first and the predecessor is bound under it. -/
def stepsRemaining (budget : Nat) : Nat :=
  match budget with
  | 0 => 0
  | next + 1 => next

/-- A `Nat` pattern whose successor arm reads the predecessor more than once. -/
def doubledPredecessor (budget : Nat) : Nat :=
  match budget with
  | 0 => 0
  | next + 1 => next + next

/-- Two discriminants, decided lexicographically in Lean's own arm order. The last arm is a pair of
wildcards, so the expansion places it on every combination the earlier arms do not accept. -/
def admits (lane : Lane) (credential : Credential) : Bool :=
  match lane, credential with
  | .fast, .present => true
  | .slow, .present => false
  | _, _ => false

/-- Two discriminants where one position binds its payload and the other is a wildcard. -/
def preferredLane (requested : Option Lane) (credential : Credential) : Lane :=
  match requested, credential with
  | some lane, .present => lane
  | some _, .absent => Lane.slow
  | none, _ => Lane.slow

/-- Three discriminants, one of them a `Nat`. -/
def clampedLane (lane : Lane) (budget : Nat) (credential : Credential) : Lane :=
  match lane, budget, credential with
  | .fast, 0, _ => Lane.slow
  | .fast, _ + 1, .present => Lane.fast
  | .fast, _ + 1, .absent => Lane.slow
  | .slow, _, _ => Lane.slow

/-- A `let` inside an argument. The sibling operand is a literal, so the hoist steps over nothing
that computes. -/
def bothPresent (credential : Credential) : Bool :=
  Bool.and
    (let decided := match credential with
      | .present => true
      | .absent => false
     decided)
    true

/-- A `let` inside an argument whose sibling operand is a binder read, which is the condition the
hoist steps over: reading a binder produces no trace event, so the binding may move in front of
it. -/
def laneOf (lane : Lane) (allowed : Bool) : Bool :=
  Bool.or
    (let fast := match lane with
      | .fast => true
      | .slow => false
     fast)
    allowed

/-- A `let` inside an argument of a declared call, with a binder read on either side of it. -/
def routed (lane : Lane) (credential : Credential) : Bool :=
  admits lane (let decided := credential; decided)

/--
A universe-polymorphic definition, exported as its own level-zero instance.

Its body matches on a `List`, which `Compile.returnBody` refuses by name (`Compile.listMatch`): the
emitter decides a list's alternatives by a length test and by `subject[0]`/`subject.slice(1)`
reads, a dispatch shape the refinement model does not carry. So this declaration's *universe*
erasure is the claim the example makes, and its body's lowering is not covered by
`Preservation.branchBody`. The module docstring records the same boundary.
-/
def firstOf.{u} {α : Type u} (fallback : α) (values : List α) : α :=
  match values with
  | [] => fallback
  | head :: _ => head

/-- A universe-polymorphic definition called from a monomorphic root, which is what makes the
level-zero instance the one the emitted module needs. -/
def firstLane (values : List Lane) : Lane := firstOf Lane.slow values

/-- A dependent match: the motive mentions the discriminant, and erases to one result type because
the only place it mentions it is a subtype's predicate, which erasure drops. -/
def atLeastOne (budget : Nat) : { value : Nat // 0 < value + 1 } :=
  match budget with
  | 0 => ⟨0, Nat.succ_pos 0⟩
  | next + 1 => ⟨next + 1, Nat.succ_pos (next + 1)⟩

/-- A dependent match binding its discriminant equation, which is a proof and so is dropped. -/
def laneWeight (lane : Lane) : Nat :=
  match _h : lane with
  | .fast => 2
  | .slow => 1

end TSLean.Examples.MatchForms
