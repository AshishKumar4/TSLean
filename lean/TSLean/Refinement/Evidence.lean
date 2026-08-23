namespace TSLean.Refinement

-- Backfills two core lemmas absent from Lean 4.16.
private theorem orEqLeftIffImp : ∀ {a b : Bool}, ((a || b) = a) ↔ (b → a) := by decide

private theorem permAnyEq {α : Type u} {l₁ l₂ : List α} {f : α → Bool} (perm : l₁.Perm l₂) :
    l₁.any f = l₂.any f := by
  rw [Bool.eq_iff_iff]; simp [perm.mem_iff]

/-- The source of authority carried by evidence. -/
inductive EvidenceKind where
  | proved
  | guarded
  | assumed
  deriving DecidableEq, Repr

/-- Stable assumption metadata with a deterministic ID. -/
structure Assumption where
  private mk ::
  id : String
  statement : String
  reason : String
  deriving DecidableEq, Repr

/-- Deterministic, human-readable ID derived from an assumption's contents. -/
def Assumption.deterministicId (statement reason : String) : String :=
  s!"{statement.length}:{statement}:{reason.length}:{reason}"

/-- The invariant enforced for every assumption accepted as evidence. -/
def Assumption.Valid (assumption : Assumption) : Prop :=
  assumption.statement ≠ "" ∧ assumption.reason ≠ "" ∧
    assumption.id = deterministicId assumption.statement assumption.reason

/-- Executable form of `Assumption.Valid`. -/
def Assumption.isValid (assumption : Assumption) : Bool :=
  assumption.statement != "" && assumption.reason != "" &&
    assumption.id == deterministicId assumption.statement assumption.reason

private theorem Assumption.isValid_iff (assumption : Assumption) :
    assumption.isValid = true ↔ assumption.Valid := by
  simp [isValid, Valid, and_assoc]

/-- Creates deterministic assumption metadata, rejecting empty statements or reasons. -/
def Assumption.create (statement reason : String) : Option Assumption :=
  if statement = "" ∨ reason = "" then none
  else some (Assumption.mk (deterministicId statement reason) statement reason)

/-- Metadata returned by `Assumption.create` satisfies the assumption invariant. -/
theorem Assumption.valid_of_create {statement reason : String} {assumption : Assumption}
    (created : Assumption.create statement reason = some assumption) : assumption.Valid := by
  unfold Assumption.create at created
  split at created
  · contradiction
  · rename_i nonempty
    simp only [Option.some.injEq] at created
    subst assumption
    exact ⟨fun empty => nonempty (Or.inl empty), fun empty => nonempty (Or.inr empty), rfl⟩

/-- A successful `Assumption.create` result selected with `Option.get` is valid. -/
theorem Assumption.valid_get_create (statement reason : String)
    (present : (Assumption.create statement reason).isSome) :
    (Assumption.create statement reason).get present |>.Valid :=
  Assumption.valid_of_create (Option.some_get present).symm

/-- A nonempty, valid assumption set with unique IDs. -/
structure ValidAssumptions where
  private mk ::
  entries : List Assumption
  nonempty : entries ≠ []
  valid : ∀ assumption, assumption ∈ entries → assumption.Valid
  uniqueIds : (entries.map (·.id)).Nodup

/-- Validates the complete assumption set before it can authorize assumed evidence. -/
def ValidAssumptions.create (entries : List Assumption) : Option ValidAssumptions :=
  if accepted : entries ≠ [] ∧
      entries.all Assumption.isValid = true ∧
      (entries.map (·.id)).Nodup then
    some ⟨entries, accepted.1, fun assumption member =>
      assumption.isValid_iff.mp ((List.all_eq_true.mp accepted.2.1) assumption member),
      accepted.2.2⟩
  else none

/-- Creates a valid singleton requirement set from already validated metadata. -/
def ValidAssumptions.singleton (assumption : Assumption) (valid : assumption.Valid) :
    ValidAssumptions :=
  ⟨[assumption], by simp, by simpa using valid, by simp⟩

private def guardDeterministicId (statement : String) : String :=
  s!"{statement.length}:{statement}"

/-- A runtime check and its proof-producing interpretation. -/
structure Guard (α : Type u) (predicate : α → Prop) where
  private mk ::
  id : String
  statement : String
  check : α → Bool
  sound : ∀ value, check value = true → predicate value
  statementNonempty : statement ≠ ""
  idDeterministic : id = guardDeterministicId statement

/-- Stable guard IDs are derived solely from their statement. -/
def Guard.deterministicId (statement : String) : String := guardDeterministicId statement

/-- Creates a guard from an executable check and its soundness proof. -/
def Guard.create (statement : String) (nonempty : statement ≠ "")
    (check : α → Bool) (sound : ∀ value, check value = true → predicate value) :
    Guard α predicate :=
  Guard.mk (guardDeterministicId statement) statement check sound nonempty rfl

/-- A receipt indexed by the guard and value that actually passed its check. -/
structure GuardReceipt {α : Type u} {predicate : α → Prop}
    (guard : Guard α predicate) (value : α) where
  private mk ::
  accepted : guard.check value = true

/-- Proof-free guard provenance retained in evidence metadata. -/
structure GuardMetadata where
  private mk ::
  id : String
  statement : String
  deriving DecidableEq, Repr

/-- The invariant enforced for every retained guard record. -/
def GuardMetadata.Valid (guard : GuardMetadata) : Prop :=
  guard.statement ≠ "" ∧ guard.id = guardDeterministicId guard.statement

private def Guard.metadata (guard : Guard α predicate) : GuardMetadata :=
  ⟨guard.id, guard.statement⟩

private def Assumption.sortKey (assumption : Assumption) : String :=
  s!"{assumption.id.length}:{assumption.id}:{assumption.statement.length}:{assumption.statement}:" ++
    s!"{assumption.reason.length}:{assumption.reason}"

private def GuardMetadata.sortKey (guard : GuardMetadata) : String :=
  s!"{guard.id.length}:{guard.id}:{guard.statement.length}:{guard.statement}"

private def insertAssumption (entries : List Assumption) (assumption : Assumption) :
    List Assumption :=
  if entries.any (·.id == assumption.id) then entries else assumption :: entries

private def insertGuard (entries : List GuardMetadata) (guard : GuardMetadata) :
    List GuardMetadata :=
  if entries.any (·.id == guard.id) then entries else guard :: entries

private def normalizeAssumptions (entries : List Assumption) : List Assumption :=
  let sorted := entries.mergeSort fun left right => decide (left.sortKey ≤ right.sortKey)
  sorted.foldl insertAssumption []

private def normalizeGuards (entries : List GuardMetadata) : List GuardMetadata :=
  let sorted := entries.mergeSort fun left right => decide (left.sortKey ≤ right.sortKey)
  sorted.foldl insertGuard []

/-- Canonical proof-free metadata. Lists are sorted and deduplicated by stable ID. -/
structure EvidenceMetadata where
  private mk ::
  assumptions : List Assumption
  guards : List GuardMetadata
  deriving DecidableEq, Repr

/-- Metadata validity requires valid records and unique IDs. -/
def EvidenceMetadata.Valid (metadata : EvidenceMetadata) : Prop :=
  (∀ assumption, assumption ∈ metadata.assumptions → assumption.Valid) ∧
  (metadata.assumptions.map (·.id)).Nodup ∧
  (∀ guard, guard ∈ metadata.guards → guard.Valid) ∧
  (metadata.guards.map (·.id)).Nodup

/-- Metadata equivalence observes stable requirement IDs, not list construction history. -/
def EvidenceMetadata.Equivalent (left right : EvidenceMetadata) : Prop :=
  (∀ id, left.assumptions.any (·.id == id) = right.assumptions.any (·.id == id)) ∧
  (∀ id, left.guards.any (·.id == id) = right.guards.any (·.id == id))

private inductive EvidenceAuthority (claim : Prop) where
  | proved (proof : claim)
  | guarded (proof : claim)
  | assumed

/-- Evidence with inaccessible raw constructors and orthogonal provenance metadata. -/
structure Evidence (claim : Prop) where
  private mk ::
  private authority : EvidenceAuthority claim
  private rawAssumptions : List Assumption
  private rawGuards : List GuardMetadata
  private assumptionsValid : ∀ assumption, assumption ∈ rawAssumptions → assumption.Valid
  private guardsValid : ∀ guard, guard ∈ rawGuards → guard.Valid

/-- An optional proposition proof whose absent case does not prove the proposition. -/
inductive ProofStatus (claim : Prop) where
  | none
  | some (proof : claim)

/-- Creates evidence directly from a proof, with no requirements. -/
def Evidence.proved (proof : claim) : Evidence claim :=
  Evidence.mk (.proved proof) [] [] (by simp) (by simp)

/-- Runs a sound guard and records the exact accepted check as provenance. -/
def Evidence.ofGuard (guard : Guard α predicate) (value : α)
    (accepted : guard.check value = true) : Evidence (predicate value) :=
  let receipt : GuardReceipt guard value := ⟨accepted⟩
  Evidence.mk (.guarded (guard.sound value receipt.accepted)) [] [guard.metadata]
    (by simp) (by
      intro metadata member
      simp only [List.mem_singleton] at member
      subst metadata
      exact ⟨guard.statementNonempty, by
        unfold Guard.metadata
        exact guard.idDeterministic⟩)

/-- Creates assumed evidence only from a validated, nonempty assumption set. -/
def Evidence.assumed (requirements : ValidAssumptions) : Evidence claim :=
  Evidence.mk .assumed requirements.entries [] requirements.valid (by simp)

/-- The evidence category, independent of provenance metadata. -/
def Evidence.kind (evidence : Evidence claim) : EvidenceKind :=
  match evidence.authority with
  | .proved _ => .proved
  | .guarded _ => .guarded
  | .assumed => .assumed

/-- Returns canonical proof-free provenance metadata. -/
def Evidence.metadata (evidence : Evidence claim) : EvidenceMetadata :=
  ⟨normalizeAssumptions evidence.rawAssumptions, normalizeGuards evidence.rawGuards⟩

/-- Proof extraction is deliberately partial: assumed evidence returns `none`. -/
def Evidence.proof? (evidence : Evidence claim) : ProofStatus claim :=
  match evidence.authority with
  | .proved proof | .guarded proof => .some proof
  | .assumed => .none

/-- Kind composition: assumptions absorb, while proved evidence is the identity. -/
def EvidenceKind.join : EvidenceKind → EvidenceKind → EvidenceKind
  | .assumed, _ | _, .assumed => .assumed
  | .guarded, _ | _, .guarded => .guarded
  | .proved, .proved => .proved

/-- Kind composition is associative. -/
theorem EvidenceKind.join_assoc (first second third : EvidenceKind) :
    join (join first second) third = join first (join second third) := by
  cases first <;> cases second <;> cases third <;> rfl

/-- Kind composition is commutative. -/
theorem EvidenceKind.join_comm (left right : EvidenceKind) :
    join left right = join right left := by
  cases left <;> cases right <;> rfl

/-- Kind composition is idempotent. -/
theorem EvidenceKind.join_idem (kind : EvidenceKind) : join kind kind = kind := by
  cases kind <;> rfl

/-- Proved evidence is the identity kind. -/
theorem EvidenceKind.join_proved (kind : EvidenceKind) : join kind .proved = kind := by
  cases kind <;> rfl

/-- Assumed evidence is absorbing. -/
theorem EvidenceKind.join_assumed (kind : EvidenceKind) : join kind .assumed = .assumed := by
  cases kind <;> rfl

private def EvidenceAuthority.and (left : EvidenceAuthority leftClaim)
    (right : EvidenceAuthority rightClaim) : EvidenceAuthority (leftClaim ∧ rightClaim) :=
  match left, right with
  | .proved leftProof, .proved rightProof => .proved ⟨leftProof, rightProof⟩
  | .proved leftProof, .guarded rightProof | .guarded leftProof, .proved rightProof |
      .guarded leftProof, .guarded rightProof => .guarded ⟨leftProof, rightProof⟩
  | .assumed, _ | _, .assumed => .assumed

/-- Composition retains every assumption and guard regardless of proof status. -/
def Evidence.and (left : Evidence leftClaim) (right : Evidence rightClaim) :
    Evidence (leftClaim ∧ rightClaim) :=
  Evidence.mk (left.authority.and right.authority)
    (left.rawAssumptions ++ right.rawAssumptions)
    (left.rawGuards ++ right.rawGuards)
    (by
      intro assumption member
      simp only [List.mem_append] at member
      cases member with
      | inl found => exact left.assumptionsValid assumption found
      | inr found => exact right.assumptionsValid assumption found)
    (by
      intro guard member
      simp only [List.mem_append] at member
      cases member with
      | inl found => exact left.guardsValid guard found
      | inr found => exact right.guardsValid guard found)

/-- Maps available proofs while retaining all provenance; assumptions remain assumptions. -/
def Evidence.map (transform : claim → nextClaim) (evidence : Evidence claim) : Evidence nextClaim :=
  let authority := match evidence.authority with
    | .proved proof => EvidenceAuthority.proved (transform proof)
    | .guarded proof => EvidenceAuthority.guarded (transform proof)
    | .assumed => EvidenceAuthority.assumed
  Evidence.mk authority evidence.rawAssumptions evidence.rawGuards
    evidence.assumptionsValid evidence.guardsValid

/-- Mapping a claim does not alter provenance metadata. -/
theorem Evidence.metadata_map (transform : claim → nextClaim) (evidence : Evidence claim) :
    (evidence.map transform).metadata = evidence.metadata := by
  unfold Evidence.map Evidence.metadata
  cases evidence.authority <;> rfl

/-- Mapping a claim does not alter its authority kind. -/
theorem Evidence.kind_map (transform : claim → nextClaim) (evidence : Evidence claim) :
    (evidence.map transform).kind = evidence.kind := by
  unfold Evidence.map Evidence.kind
  cases evidence.authority <;> rfl

/-- Evidence composition follows kind composition. -/
theorem Evidence.kind_and (left : Evidence leftClaim) (right : Evidence rightClaim) :
    (left.and right).kind = left.kind.join right.kind := by
  unfold Evidence.and Evidence.kind
  cases left.authority <;> cases right.authority <;> rfl

private theorem insertAssumption_valid (entries : List Assumption) (assumption : Assumption)
    (entriesValid : ∀ entry, entry ∈ entries → entry.Valid) (valid : assumption.Valid) :
    ∀ entry, entry ∈ insertAssumption entries assumption → entry.Valid := by
  intro entry member
  unfold insertAssumption at member
  split at member
  · exact entriesValid entry member
  · simp only [List.mem_cons] at member
    cases member with
    | inl equal => simpa [equal] using valid
    | inr found => exact entriesValid entry found

private theorem insertAssumption_nodup (entries : List Assumption) (assumption : Assumption)
    (unique : (entries.map (·.id)).Nodup) :
    ((insertAssumption entries assumption).map (·.id)).Nodup := by
  unfold insertAssumption
  split
  · exact unique
  · simp only [List.map_cons, List.nodup_cons]
    constructor
    · intro member
      rw [List.mem_map] at member
      obtain ⟨entry, entryMember, equal⟩ := member
      have found : entries.any (·.id == assumption.id) = true :=
        List.any_eq_true.mpr ⟨entry, entryMember, by simp [equal]⟩
      contradiction
    · exact unique

private theorem foldAssumption_valid (source accumulator : List Assumption)
    (sourceValid : ∀ entry, entry ∈ source → entry.Valid)
    (accumulatorValid : ∀ entry, entry ∈ accumulator → entry.Valid) :
    ∀ entry, entry ∈ source.foldl insertAssumption accumulator → entry.Valid := by
  induction source generalizing accumulator with
  | nil => exact accumulatorValid
  | cons current rest ih =>
      simp only [List.foldl_cons]
      apply ih
      · intro entry member
        exact sourceValid entry (List.mem_cons_of_mem current member)
      · apply insertAssumption_valid accumulator current accumulatorValid
        exact sourceValid current (List.mem_cons_self _ _)

private theorem foldAssumption_nodup (source accumulator : List Assumption)
    (unique : (accumulator.map (·.id)).Nodup) :
    ((source.foldl insertAssumption accumulator).map (·.id)).Nodup := by
  induction source generalizing accumulator with
  | nil => exact unique
  | cons current rest ih =>
      simp only [List.foldl_cons]
      exact ih _ (insertAssumption_nodup accumulator current unique)

private theorem normalizeAssumptions_valid (entries : List Assumption)
    (valid : ∀ entry, entry ∈ entries → entry.Valid) :
    ∀ entry, entry ∈ normalizeAssumptions entries → entry.Valid := by
  intro entry member
  unfold normalizeAssumptions at member
  apply foldAssumption_valid _ [] _ (by simp) entry member
  intro source sourceMember
  exact valid source (List.mem_mergeSort.mp sourceMember)

private theorem normalizeAssumptions_nodup (entries : List Assumption) :
    ((normalizeAssumptions entries).map (·.id)).Nodup := by
  unfold normalizeAssumptions
  exact foldAssumption_nodup _ [] (by simp)

private theorem insertGuard_valid (entries : List GuardMetadata) (guard : GuardMetadata)
    (entriesValid : ∀ entry, entry ∈ entries → entry.Valid) (valid : guard.Valid) :
    ∀ entry, entry ∈ insertGuard entries guard → entry.Valid := by
  intro entry member
  unfold insertGuard at member
  split at member
  · exact entriesValid entry member
  · simp only [List.mem_cons] at member
    cases member with
    | inl equal => simpa [equal] using valid
    | inr found => exact entriesValid entry found

private theorem insertGuard_nodup (entries : List GuardMetadata) (guard : GuardMetadata)
    (unique : (entries.map (·.id)).Nodup) :
    ((insertGuard entries guard).map (·.id)).Nodup := by
  unfold insertGuard
  split
  · exact unique
  · simp only [List.map_cons, List.nodup_cons]
    constructor
    · intro member
      rw [List.mem_map] at member
      obtain ⟨entry, entryMember, equal⟩ := member
      have found : entries.any (·.id == guard.id) = true :=
        List.any_eq_true.mpr ⟨entry, entryMember, by simp [equal]⟩
      contradiction
    · exact unique

private theorem foldGuard_valid (source accumulator : List GuardMetadata)
    (sourceValid : ∀ entry, entry ∈ source → entry.Valid)
    (accumulatorValid : ∀ entry, entry ∈ accumulator → entry.Valid) :
    ∀ entry, entry ∈ source.foldl insertGuard accumulator → entry.Valid := by
  induction source generalizing accumulator with
  | nil => exact accumulatorValid
  | cons current rest ih =>
      simp only [List.foldl_cons]
      apply ih
      · intro entry member
        exact sourceValid entry (List.mem_cons_of_mem current member)
      · apply insertGuard_valid accumulator current accumulatorValid
        exact sourceValid current (List.mem_cons_self _ _)

private theorem foldGuard_nodup (source accumulator : List GuardMetadata)
    (unique : (accumulator.map (·.id)).Nodup) :
    ((source.foldl insertGuard accumulator).map (·.id)).Nodup := by
  induction source generalizing accumulator with
  | nil => exact unique
  | cons current rest ih =>
      simp only [List.foldl_cons]
      exact ih _ (insertGuard_nodup accumulator current unique)

private theorem normalizeGuards_valid (entries : List GuardMetadata)
    (valid : ∀ entry, entry ∈ entries → entry.Valid) :
    ∀ entry, entry ∈ normalizeGuards entries → entry.Valid := by
  intro entry member
  unfold normalizeGuards at member
  apply foldGuard_valid _ [] _ (by simp) entry member
  intro source sourceMember
  exact valid source (List.mem_mergeSort.mp sourceMember)

private theorem normalizeGuards_nodup (entries : List GuardMetadata) :
    ((normalizeGuards entries).map (·.id)).Nodup := by
  unfold normalizeGuards
  exact foldGuard_nodup _ [] (by simp)

/-- Every publicly constructible evidence value has valid canonical metadata. -/
theorem Evidence.metadata_valid (evidence : Evidence claim) : evidence.metadata.Valid :=
  ⟨normalizeAssumptions_valid evidence.rawAssumptions evidence.assumptionsValid,
    normalizeAssumptions_nodup evidence.rawAssumptions,
    normalizeGuards_valid evidence.rawGuards evidence.guardsValid,
    normalizeGuards_nodup evidence.rawGuards⟩

private theorem any_insertAssumption (entries : List Assumption) (assumption : Assumption)
    (id : String) :
    (insertAssumption entries assumption).any (·.id == id) =
      (entries.any (·.id == id) || assumption.id == id) := by
  unfold insertAssumption
  cases samePresent : entries.any (·.id == assumption.id) <;>
    simp only [Bool.false_eq_true, ↓reduceIte, List.any_cons]
  · exact Bool.or_comm _ _
  · apply Eq.symm
    apply orEqLeftIffImp.mpr
    intro same
    have sameId : assumption.id = id := beq_iff_eq.mp same
    subst id
    exact samePresent

private theorem any_foldAssumptions (source accumulator : List Assumption) (id : String) :
    (source.foldl insertAssumption accumulator).any (·.id == id) =
      (accumulator.any (·.id == id) || source.any (·.id == id)) := by
  induction source generalizing accumulator with
  | nil => simp
  | cons current rest ih =>
      simp only [List.foldl_cons, ih, List.any_cons, any_insertAssumption]
      cases accumulator.any (·.id == id) <;> cases current.id == id <;>
        cases rest.any (·.id == id) <;> rfl

private theorem normalizeAssumptions_any (entries : List Assumption) (id : String) :
    (normalizeAssumptions entries).any (·.id == id) = entries.any (·.id == id) := by
  unfold normalizeAssumptions
  rw [any_foldAssumptions]
  simp only [List.any_nil, Bool.false_or]
  exact permAnyEq (List.mergeSort_perm entries _)

private theorem any_insertGuard (entries : List GuardMetadata) (guard : GuardMetadata)
    (id : String) :
    (insertGuard entries guard).any (·.id == id) =
      (entries.any (·.id == id) || guard.id == id) := by
  unfold insertGuard
  cases samePresent : entries.any (·.id == guard.id) <;>
    simp only [Bool.false_eq_true, ↓reduceIte, List.any_cons]
  · exact Bool.or_comm _ _
  · apply Eq.symm
    apply orEqLeftIffImp.mpr
    intro same
    have sameId : guard.id = id := beq_iff_eq.mp same
    subst id
    exact samePresent

private theorem any_foldGuards (source accumulator : List GuardMetadata) (id : String) :
    (source.foldl insertGuard accumulator).any (·.id == id) =
      (accumulator.any (·.id == id) || source.any (·.id == id)) := by
  induction source generalizing accumulator with
  | nil => simp
  | cons current rest ih =>
      simp only [List.foldl_cons, ih, List.any_cons, any_insertGuard]
      cases accumulator.any (·.id == id) <;> cases current.id == id <;>
        cases rest.any (·.id == id) <;> rfl

private theorem normalizeGuards_any (entries : List GuardMetadata) (id : String) :
    (normalizeGuards entries).any (·.id == id) = entries.any (·.id == id) := by
  unfold normalizeGuards
  rw [any_foldGuards]
  simp only [List.any_nil, Bool.false_or]
  exact permAnyEq (List.mergeSort_perm entries _)

/-- Composition preserves metadata validity. -/
theorem Evidence.and_metadata_valid (left : Evidence leftClaim) (right : Evidence rightClaim) :
    (left.and right).metadata.Valid :=
  (left.and right).metadata_valid

/-- Metadata composition is associative without comparing proposition proof terms. -/
theorem Evidence.metadata_and_assoc (first : Evidence firstClaim) (second : Evidence secondClaim)
    (third : Evidence thirdClaim) :
    ((first.and second).and third).metadata = (first.and (second.and third)).metadata := by
  simp [Evidence.and, Evidence.metadata, List.append_assoc]

/-- Metadata composition is commutative by stable requirement identity. -/
theorem Evidence.metadata_and_comm (left : Evidence leftClaim) (right : Evidence rightClaim) :
    (left.and right).metadata.Equivalent (right.and left).metadata := by
  constructor <;> intro id <;>
    simp [Evidence.and, Evidence.metadata, normalizeAssumptions_any, normalizeGuards_any,
      List.any_append, Bool.or_comm]

/-- Metadata composition is idempotent by stable requirement identity. -/
theorem Evidence.metadata_and_idem (evidence : Evidence claim) :
    (evidence.and evidence).metadata.Equivalent evidence.metadata := by
  constructor <;> intro id <;>
    simp [Evidence.and, Evidence.metadata, normalizeAssumptions_any, normalizeGuards_any,
      List.any_append]

end TSLean.Refinement
