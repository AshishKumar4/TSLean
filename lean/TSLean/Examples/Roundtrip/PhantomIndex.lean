/-
A type former indexed by a term, and the three shapes that index appears in.

`Tag` separates `Label .run` from `Label .turn` in the type checker: the two are different types, so
handing one where the other is wanted is a compile error rather than a runtime `false`. Nothing in
`Label` depends on which tag it was built at, so the two are the same record at runtime and the
emitted TypeScript is one type carrying one field. That is what makes the index erasable, and
`Export.lean:erasedDataParameters` checks it per type rather than assuming it for the shape.

The module is written so all three shapes the erasure has to handle occur once each:

* the phantom-indexed type former itself, `Label`;
* a declaration whose result type varies only in that index, `parse`, whose `tag` is erased from the
  result type and kept in the value — the emitted function still takes it, because `admits` reads
  it;
* use sites at a concrete index, `Pair`'s two fields and `runLabel`.

This is the shape of agent-core's kernel identifier `TextId (kind : IdKind)`
(`formal/AgentCore/Kernel/Core/Id.lean:73`). Two things there are deliberately left out. Its `Prop`
field belongs to a different erasure: a record field carrying no data is refused for its own reason.
And its payload is a `String`, which the round-trip profile does not carry — the profile admits
booleans, string-literal enumerations, and structures and options of those — so the payload here is
an enumeration instead. The index is what this fixture is about, and an enumeration payload keeps it
the only thing under test.
-/

namespace TSLean.Examples.Roundtrip.PhantomIndex

/-- Which kind of thing a label names. Every constructor is nullary, so an index is a name. -/
inductive Tag where
  | run
  | turn
  deriving DecidableEq, Repr

/-- How much a label is allowed to claim. -/
inductive Level where
  | low
  | high
  deriving DecidableEq, Repr

/-- Whether the level is the demanding one. -/
def isHigh : Level → Bool
  | .low => false
  | .high => true

/-- Which tags may carry the demanding level. This is the one thing a tag is read for at runtime,
and it is why `parse` keeps its `tag` parameter after the index leaves its result type. -/
def allowsHigh : Tag → Bool
  | .run => true
  | .turn => false

/-- Whether a tag admits a level. -/
def admits (tag : Tag) (level : Level) : Bool :=
  if isHigh level then allowsHigh tag else true

/-- One label: its level, and in its type the tag it names. The tag reaches no field, which is the
obligation that makes it erasable. -/
structure Label (tag : Tag) where
  level : Level
  deriving DecidableEq

/-- **The index is erased from the type and kept in the value.** `tag` is dropped from both the
parameter type and the result type, because no field of `Label` depends on it; it survives as a
parameter, because `admits` reads it. That pairing — the same binder erased in the type and kept in
the value — is the shape this fixture exists to exercise. -/
def parse (tag : Tag) (label : Label tag) : Option (Label tag) :=
  if admits tag label.level then some label else none

/-- Reading a label's level does not mention the index, which is why one projection serves every
tag. -/
def levelOf (tag : Tag) (label : Label tag) : Level := label.level

/-- Two labels at two different concrete indices. In Lean these fields have different types; in the
emitted TypeScript they have the same one, and that is sound precisely because neither type's
content depends on its index. -/
structure Pair where
  left : Label .run
  right : Label .turn
  deriving DecidableEq

/-- A use site that fixes the index to a nullary constructor. -/
def runLabel (label : Label .run) : Option (Label .run) := parse .run label

/-- Building a pair constructs a phantom-indexed record at each concrete index. -/
def pairOf (left right : Level) : Pair :=
  { left := { level := left }, right := { level := right } }

/-- **A run label admits every level.** The tag is read here, so the emitted function genuinely
needs the parameter the type erased. -/
theorem runLabel_admits (label : Label .run) : runLabel label = some label := by
  obtain ⟨level⟩ := label
  cases level <;> rfl

/-- **A turn label refuses the demanding level.** The two tags disagree, which is what makes `tag` a
runtime value rather than dead weight. -/
theorem parse_turn_high : parse .turn { level := .high } = none := rfl

/-- **The tag is not the content.** Two labels at different tags can carry the same level, which is
exactly the fact that makes the index erasable at runtime. -/
theorem level_independent_of_tag (level : Level) :
    (Label.mk level : Label .run).level = (Label.mk level : Label .turn).level := rfl

end TSLean.Examples.Roundtrip.PhantomIndex
