-- TSLean.Veil.DSL
-- Lightweight DSL for declaring and verifying transition systems.
-- No external dependencies (no Mathlib, lean-smt, lean-auto).

import TSLean.Veil.Core

open TSLean.Veil TransitionSystem

namespace TSLean.Veil.DSL

/-! ## Proof automation tactics -/

/-- Try a cascade of standard tactics for transition system goals. -/
macro "veil_auto" : tactic => `(tactic|
  first
  | omega
  | simp_all (config := { decide := true })
  | decide
  | assumption
  | (constructor <;> first | omega | simp_all | decide | assumption))

/-- Extensionality for state structures — prove `s1 = s2` field-by-field. -/
macro "state_ext" : tactic => `(tactic| ext <;> simp_all)

/-! ## Two/Three/Four-action disjunction helpers -/

-- Rather than using `List (σ → σ → Prop)` (universe issues with Prop),
-- we define disjunction combinators for fixed arities.

def next2 (a1 a2 : σ → σ → Prop) (pre post : σ) : Prop :=
  a1 pre post ∨ a2 pre post

def next3 (a1 a2 a3 : σ → σ → Prop) (pre post : σ) : Prop :=
  a1 pre post ∨ a2 pre post ∨ a3 pre post

def next4 (a1 a2 a3 a4 : σ → σ → Prop) (pre post : σ) : Prop :=
  a1 pre post ∨ a2 pre post ∨ a3 pre post ∨ a4 pre post

def next5 (a1 a2 a3 a4 a5 : σ → σ → Prop) (pre post : σ) : Prop :=
  a1 pre post ∨ a2 pre post ∨ a3 pre post ∨ a4 pre post ∨ a5 pre post

/-- If every action in a two-action system preserves inv, next2 preserves inv. -/
theorem next2_preserves {a1 a2 : σ → σ → Prop} {assu inv : σ → Prop}
    (h1 : ∀ pre post, assu pre → inv pre → a1 pre post → inv post)
    (h2 : ∀ pre post, assu pre → inv pre → a2 pre post → inv post)
    {pre post : σ} (ha : assu pre) (hi : inv pre) (hn : next2 a1 a2 pre post) :
    inv post := by
  rcases hn with h | h
  · exact h1 pre post ha hi h
  · exact h2 pre post ha hi h

theorem next3_preserves {a1 a2 a3 : σ → σ → Prop} {assu inv : σ → Prop}
    (h1 : ∀ pre post, assu pre → inv pre → a1 pre post → inv post)
    (h2 : ∀ pre post, assu pre → inv pre → a2 pre post → inv post)
    (h3 : ∀ pre post, assu pre → inv pre → a3 pre post → inv post)
    {pre post : σ} (ha : assu pre) (hi : inv pre) (hn : next3 a1 a2 a3 pre post) :
    inv post := by
  rcases hn with h | h | h
  · exact h1 pre post ha hi h
  · exact h2 pre post ha hi h
  · exact h3 pre post ha hi h

theorem next4_preserves {a1 a2 a3 a4 : σ → σ → Prop} {assu inv : σ → Prop}
    (h1 : ∀ pre post, assu pre → inv pre → a1 pre post → inv post)
    (h2 : ∀ pre post, assu pre → inv pre → a2 pre post → inv post)
    (h3 : ∀ pre post, assu pre → inv pre → a3 pre post → inv post)
    (h4 : ∀ pre post, assu pre → inv pre → a4 pre post → inv post)
    {pre post : σ} (ha : assu pre) (hi : inv pre) (hn : next4 a1 a2 a3 a4 pre post) :
    inv post := by
  rcases hn with h | h | h | h
  · exact h1 pre post ha hi h
  · exact h2 pre post ha hi h
  · exact h3 pre post ha hi h
  · exact h4 pre post ha hi h

theorem next5_preserves {a1 a2 a3 a4 a5 : σ → σ → Prop} {assu inv : σ → Prop}
    (h1 : ∀ pre post, assu pre → inv pre → a1 pre post → inv post)
    (h2 : ∀ pre post, assu pre → inv pre → a2 pre post → inv post)
    (h3 : ∀ pre post, assu pre → inv pre → a3 pre post → inv post)
    (h4 : ∀ pre post, assu pre → inv pre → a4 pre post → inv post)
    (h5 : ∀ pre post, assu pre → inv pre → a5 pre post → inv post)
    {pre post : σ} (ha : assu pre) (hi : inv pre)
    (hn : next5 a1 a2 a3 a4 a5 pre post) :
    inv post := by
  rcases hn with h | h | h | h | h
  · exact h1 pre post ha hi h
  · exact h2 pre post ha hi h
  · exact h3 pre post ha hi h
  · exact h4 pre post ha hi h
  · exact h5 pre post ha hi h

/-! ## Safety proof combinator -/

/-- Prove safety for a transition system where:
    - `hassu`: assumptions hold for all reachable states
    - `hinit`: init establishes the invariant
    - `hcons`: the `next` relation preserves the invariant
    - `hsafe`: the invariant implies safety -/
theorem safety_of_inv_inductive (σ : Type) [inst : TransitionSystem σ]
    (hassu : ∀ s, @reachable σ inst s → inst.assumptions s)
    (hinit : ∀ s, inst.assumptions s → inst.init s → inst.inv s)
    (hcons : ∀ s s', inst.assumptions s → inst.inv s → inst.next s s' → inst.inv s')
    (hsafe : ∀ s, inst.assumptions s → inst.inv s → inst.safe s) :
    ∀ s, @reachable σ inst s → inst.safe s := by
  intro s hr
  have : inst.inv s := by
    induction hr with
    | init s hi => exact hinit s (hassu s (.init s hi)) hi
    | step s s' hrs hn ih => exact hcons s s' (hassu s hrs) ih hn
  exact hsafe s (hassu s hr) this

/-! ## DSL syntax macros -/

/-! ## DSL syntax macros

Users define the state structure normally, then use these macros to declare
actions, safety properties, and invariants in a uniform way. -/

-- Functional action: post = f(pre)
syntax "veil_action" ident "(" ident ":" ident ")" "where" term : command
macro_rules
  | `(veil_action $n ($s : $ty) where $body) =>
    `(def $n (pre post : $ty) : Prop := post = (fun ($s : $ty) => $body) pre)

-- Relational action: two-state predicate
syntax "veil_relation" ident "(" ident ident ":" ident ")" "where" term : command
macro_rules
  | `(veil_relation $n ($pre $post : $ty) where $body) =>
    `(def $n ($pre $post : $ty) : Prop := $body)

-- Safety property
syntax "veil_safety" ident "(" ident ":" ident ")" "where" term : command
macro_rules
  | `(veil_safety $n ($s : $ty) where $body) =>
    `(def $n ($s : $ty) : Prop := $body)

end TSLean.Veil.DSL
