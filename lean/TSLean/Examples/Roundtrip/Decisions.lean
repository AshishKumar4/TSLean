namespace TSLean.Examples.Roundtrip.Decisions

/-- Which way a request was routed. -/
inductive Lane where
  | fast
  | slow
  deriving DecidableEq, Repr

/-- Whether a request carried a credential. -/
inductive Credential where
  | present
  | absent
  deriving DecidableEq, Repr

/-- One request, as the two decisions it carries. -/
structure Request where
  lane : Lane
  credential : Credential
  deriving DecidableEq, Repr

/--
A match on two discriminants, decided lexicographically in Lean's own arm order. The last arm is a
pair of wildcards, so the expansion places it on every combination the earlier arms do not accept.
-/
def admits (lane : Lane) (credential : Credential) : Bool :=
  match lane, credential with
  | .fast, .present => true
  | .slow, .present => false
  | _, _ => false

/-- A match on two discriminants that are field reads rather than binders. A field read is
re-readable, which is what the expansion requires of every discriminant it reads again. -/
def decide (request : Request) : Bool :=
  match request.lane, request.credential with
  | .fast, .present => true
  | .fast, .absent => false
  | .slow, _ => false

/-- A `let` inside an argument, hoisted to a `const` in front of the call it was an operand of. The
sibling operand is a binder read, which the hoist may step over. -/
def hoisted (lane : Lane) (allowed : Bool) : Bool :=
  Bool.or
    (let fast := match lane with
      | .fast => true
      | .slow => false
     fast)
    allowed

/-- A dependent match: the alternative binds the discriminant equation, which is a proof and so has
no runtime image. -/
def weight (lane : Lane) : Credential :=
  match _h : lane with
  | .fast => Credential.present
  | .slow => Credential.absent

/-- The two-discriminant decision admits exactly the fast-and-credentialled combination. -/
theorem admits_iff (lane : Lane) (credential : Credential) :
    admits lane credential = true ↔ (lane = Lane.fast ∧ credential = Credential.present) := by
  cases lane <;> cases credential <;> simp [admits]

/-- Reading the discriminants out of a request decides what reading them as binders decides. -/
theorem decide_eq_admits (request : Request) :
    decide request = admits request.lane request.credential := by
  cases request with
  | mk lane credential => cases lane <;> cases credential <;> rfl

/-- The hoisted binding decides the fast lane, exactly as the unhoisted source does. -/
theorem hoisted_fast (allowed : Bool) : hoisted Lane.fast allowed = true := by
  simp [hoisted]

/-- The dependent match's equation binder changes nothing it decides. -/
theorem weight_fast : weight Lane.fast = Credential.present := rfl

end TSLean.Examples.Roundtrip.Decisions
