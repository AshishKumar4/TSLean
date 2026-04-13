-- TSLean.Veil.Core
-- Adaptation of Veil's RelationalTransitionSystem for Lean 4.29
-- (no Mathlib, no lean-smt, no lean-auto required).
-- Inspired by verse-lab/veil (MIT License).

namespace TSLean.Veil

/-! ## Core Transition System Typeclass -/

/-- A relational transition system over state type `σ`.
    Mirrors Veil's `RelationalTransitionSystem`. -/
class TransitionSystem (σ : Type) where
  init       : σ → Prop
  assumptions : σ → Prop
  next       : σ → σ → Prop
  safe       : σ → Prop
  inv        : σ → Prop

namespace TransitionSystem

/-! ## Core properties -/

def invSafe [TransitionSystem σ] : Prop :=
  ∀ s : σ, TransitionSystem.assumptions s → TransitionSystem.inv s → TransitionSystem.safe s

def invInit [TransitionSystem σ] : Prop :=
  ∀ s : σ, TransitionSystem.assumptions s → TransitionSystem.init s → TransitionSystem.inv s

def invConsecution [TransitionSystem σ] : Prop :=
  ∀ s s' : σ, TransitionSystem.assumptions s → TransitionSystem.inv s →
    TransitionSystem.next s s' → TransitionSystem.inv s'

def invInductive [TransitionSystem σ] : Prop :=
  @invInit σ _ ∧ @invConsecution σ _

/-! ## Reachability -/

inductive reachable [TransitionSystem σ] : σ → Prop where
  | init : ∀ s : σ, TransitionSystem.init s → reachable s
  | step : ∀ s s' : σ, reachable s → TransitionSystem.next s s' → reachable s'

def isInvariant [TransitionSystem σ] (p : σ → Prop) : Prop :=
  ∀ s : σ, reachable s → p s

theorem invInductive_to_isInvariant [TransitionSystem σ]
    (hassu : isInvariant (TransitionSystem.assumptions (σ := σ)))
    (hinv : invInductive (σ := σ)) :
    isInvariant (TransitionSystem.inv (σ := σ)) := by
  obtain ⟨hinit, hcons⟩ := hinv
  intro s hr
  induction hr with
  | init s hi => exact hinit s (hassu s (reachable.init s hi)) hi
  | step s s' hrs hn ih =>
    exact hcons s s' (hassu s hrs) ih hn

theorem safe_of_invInductive [TransitionSystem σ]
    (hassu : isInvariant (TransitionSystem.assumptions (σ := σ)))
    (hinv : invInductive (σ := σ))
    (hsafe : invSafe (σ := σ)) :
    isInvariant (TransitionSystem.safe (σ := σ)) := by
  intro s hr
  exact hsafe s (hassu s hr) (invInductive_to_isInvariant hassu hinv s hr)

/-! ## Bounded reachability -/

inductive reachableIn [TransitionSystem σ] : Nat → σ → Prop where
  | zero : ∀ s : σ, TransitionSystem.init s → reachableIn 0 s
  | succ : ∀ n (s s' : σ), reachableIn n s → TransitionSystem.next s s' →
             reachableIn (n + 1) s'

theorem reachableIn_implies_reachable [TransitionSystem σ] :
    ∀ n (s : σ), reachableIn n s → reachable s := by
  intro n s h
  induction h with
  | zero s hi => exact reachable.init s hi
  | succ n s s' _ hn ih => exact reachable.step s s' ih hn

/-! ## Invariant splitting and merging -/

theorem isInvariant_and [TransitionSystem σ] (p q : σ → Prop) :
    isInvariant p → isInvariant q → isInvariant (fun s => p s ∧ q s) := by
  intro hp hq s hr; exact ⟨hp s hr, hq s hr⟩

theorem isInvariant_imp [TransitionSystem σ] (p q : σ → Prop)
    (h : ∀ s, p s → q s) : isInvariant p → isInvariant q := by
  intro hp s hr; exact h s (hp s hr)

/-! ## Liveness scaffolding -/

def Eventually [TransitionSystem σ] (s : σ) (p : σ → Prop) : Prop :=
  ∃ s', reachable s' ∧ p s'

def LeadsTo [TransitionSystem σ] (p q : σ → Prop) : Prop :=
  ∀ s, reachable s → p s → Eventually s q

/-! ## Invariant transitivity -/

theorem isInvariant_or [TransitionSystem σ] (p q : σ → Prop)
    (hp : isInvariant p) (hq : isInvariant q) : isInvariant (fun s => p s ∨ q s) := by
  intro s hr; exact Or.inl (hp s hr)

theorem isInvariant_true [TransitionSystem σ] : isInvariant (fun _ : σ => True) :=
  fun _ _ => trivial

theorem isInvariant_refl [TransitionSystem σ] (p : σ → Prop)
    (h : ∀ s, p s) : isInvariant p := fun s _ => h s

theorem isInvariant_congr [TransitionSystem σ] (p q : σ → Prop)
    (heq : ∀ s, p s ↔ q s) (hp : isInvariant p) : isInvariant q :=
  fun s hr => (heq s).mp (hp s hr)

/-! ## Bounded invariants -/

theorem safe_of_reachableIn [TransitionSystem σ]
    (hassu : isInvariant (TransitionSystem.assumptions (σ := σ)))
    (hinv : invInductive (σ := σ))
    (hsafe : invSafe (σ := σ))
    (n : Nat) (s : σ) (hr : reachableIn n s) :
    TransitionSystem.safe s :=
  safe_of_invInductive hassu hinv hsafe s (reachableIn_implies_reachable n s hr)

/-! ## Composed invariants -/

theorem invInductive_implies_isInvariant [TransitionSystem σ]
    (hassu : isInvariant (TransitionSystem.assumptions (σ := σ)))
    (hinit : invInit (σ := σ))
    (hcons : invConsecution (σ := σ)) :
    isInvariant (TransitionSystem.inv (σ := σ)) :=
  invInductive_to_isInvariant hassu ⟨hinit, hcons⟩

theorem isInvariant_of_safe [TransitionSystem σ]
    (hassu : isInvariant (TransitionSystem.assumptions (σ := σ)))
    (hinv : invInductive (σ := σ))
    (hsafe : invSafe (σ := σ)) :
    isInvariant (TransitionSystem.safe (σ := σ)) :=
  safe_of_invInductive hassu hinv hsafe

/-! ## Reachability properties -/

theorem reachable_init_of_init [TransitionSystem σ] (s : σ)
    (h : TransitionSystem.init s) : reachable s :=
  reachable.init s h

theorem reachable_step_closure [TransitionSystem σ] (s s' : σ)
    (hr : reachable s) (hn : TransitionSystem.next s s') : reachable s' :=
  reachable.step s s' hr hn

theorem reachable_trans [TransitionSystem σ] (s s' : σ)
    (hr : reachable s) (hn : TransitionSystem.next s s') (p : σ → Prop)
    (hp : isInvariant p) : p s' :=
  hp s' (reachable_step_closure s s' hr hn)

/-! ## Safety lifting -/

theorem safe_preserved_by_step [TransitionSystem σ]
    (hassu : isInvariant (TransitionSystem.assumptions (σ := σ)))
    (hinv : invInductive (σ := σ))
    (hsafe : invSafe (σ := σ))
    (s s' : σ) (hr : reachable s)
    (hn : TransitionSystem.next s s') :
    TransitionSystem.safe s' :=
  safe_of_invInductive hassu hinv hsafe s' (reachable_step_closure s s' hr hn)

/-! ## Induction principles -/

theorem reachable_ind [TransitionSystem σ] (p : σ → Prop)
    (hinit : ∀ s, TransitionSystem.init s → p s)
    (hstep : ∀ s s', reachable s → p s → TransitionSystem.next s s' → p s') :
    ∀ s, reachable s → p s := by
  intro s hr; induction hr with
  | init s hi => exact hinit s hi
  | step s s' _ hn ih => exact hstep s s' (by assumption) ih hn

theorem invInductive_ind [TransitionSystem σ] (p : σ → Prop)
    (hassu : isInvariant (TransitionSystem.assumptions (σ := σ)))
    (hinit : ∀ s, TransitionSystem.assumptions s → TransitionSystem.init s → p s)
    (hcons : ∀ s s', TransitionSystem.assumptions s → p s →
              TransitionSystem.next s s' → p s') :
    isInvariant p := by
  intro s hr; induction hr with
  | init s hi => exact hinit s (hassu s (reachable.init s hi)) hi
  | step s s' hrs hn ih =>
    exact hcons s s' (hassu s hrs) ih hn

/-! ## Property composition -/

theorem isInvariant_forall [TransitionSystem σ] (P : α → σ → Prop)
    (h : ∀ a, isInvariant (P a)) : isInvariant (fun s => ∀ a, P a s) :=
  fun s hr a => h a s hr

theorem isInvariant_exists [TransitionSystem σ] (P : α → σ → Prop)
    (a : α) (h : isInvariant (P a)) : isInvariant (fun s => ∃ b, P b s) :=
  fun s hr => ⟨a, h s hr⟩

/-! ## Refinement -/

/-- A simulation relation between two transition systems.
    If `R s t` holds for correlated states, every step in the concrete system
    has a matching step in the abstract system. -/
def Simulation (σ τ : Type) [TransitionSystem σ] [TransitionSystem τ]
    (R : σ → τ → Prop) : Prop :=
  (∀ s t, TransitionSystem.init (σ := σ) s → R s t → TransitionSystem.init (σ := τ) t) ∧
  (∀ s s' t, R s t → TransitionSystem.next (σ := σ) s s' →
    ∃ t', TransitionSystem.next (σ := τ) t t' ∧ R s' t')

/-- If concrete states always have a paired abstract state, and the abstract system
    is safe, and safety transfers across R, then the concrete system is safe.
    This is the forward simulation theorem. -/
theorem safety_via_simulation (σ τ : Type) [TransitionSystem σ] [TransitionSystem τ]
    (R : σ → τ → Prop)
    (hsim : Simulation σ τ R)
    (habstract : isInvariant (σ := τ) TransitionSystem.safe)
    (hsafe_transfer : ∀ s t, R s t → TransitionSystem.safe (σ := τ) t →
                      TransitionSystem.safe (σ := σ) s)
    -- Every reachable concrete state has a paired reachable abstract state
    (hpair : ∀ s, reachable (σ := σ) s → ∃ t, reachable (σ := τ) t ∧ R s t) :
    isInvariant (σ := σ) TransitionSystem.safe := by
  intro s hr
  obtain ⟨t, hrt, hR⟩ := hpair s hr
  exact hsafe_transfer s t hR (habstract t hrt)

/-! ## Temporal properties -/

/-- After at least `n` steps from an initial state, property `p` holds.
    This is a bounded liveness variant. -/
def HoldsAfterN [TransitionSystem σ] (n : Nat) (p : σ → Prop) : Prop :=
  ∀ s, reachableIn n s → p s

theorem holdsAfterN_zero [TransitionSystem σ] (p : σ → Prop)
    (h : ∀ s, TransitionSystem.init s → p s) :
    HoldsAfterN 0 p := by
  intro s hr; cases hr; exact h _ ‹_›

theorem holdsAfterN_of_invariant [TransitionSystem σ] (p : σ → Prop) (n : Nat)
    (h : isInvariant p) : HoldsAfterN n p :=
  fun s hr => h s (reachableIn_implies_reachable n s hr)

theorem isInvariant_not_false [TransitionSystem σ] :
    isInvariant (fun _ : σ => ¬False) := fun _ _ h => h

end TransitionSystem

end TSLean.Veil
