/-
  TSLean.Proofs.EffectLattice
  Correctness theorems for the effect algebra: isPure, joinEffects, type defaults.
-/
import TSLean.Generated.SelfHost.ir_types
import TSLean.Generated.SelfHost.effects_index

open TSLean.Generated.Types
open TSLean.Generated.SelfHost.EffectsIndex

-- ─── isPure is correct for every Effect constructor ─────────────────────────────

theorem isPure_Pure : isPure Effect.Pure = true := by rfl
theorem isPure_IO : isPure Effect.IO = false := by rfl
theorem isPure_Async : isPure Effect.Async = false := by rfl
theorem isPure_State (t : IRType) : isPure (Effect.State t) = false := by rfl
theorem isPure_Except (t : IRType) : isPure (Effect.Except t) = false := by rfl
theorem isPure_Combined (es : Array Effect) : isPure (Effect.Combined es) = false := by rfl

-- isPure characterization: exactly Effect.Pure maps to true
theorem isPure_iff (e : Effect) : isPure e = true ↔ e = Effect.Pure := by
  constructor
  · intro h; cases e <;> simp [isPure] at h ⊢ <;> exact h
  · intro h; subst h; rfl

-- ─── Inhabited instances use concrete defaults (no sorry) ────────────────────────

theorem Effect_default_is_Pure : (default : Effect) = Effect.Pure := by rfl
theorem IRType_default_is_Unit : (default : IRType) = IRType.Unit := by rfl

-- ─── joinEffects with Pure is identity ──────────────────────────────────────────

theorem joinEffects_Pure_left (b : Effect) :
    joinEffects Effect.Pure b = b := by
  simp [joinEffects, isPure]

theorem joinEffects_Pure_right (a : Effect) :
    joinEffects a Effect.Pure = a := by
  simp [joinEffects]
  cases a <;> simp [isPure]

-- ─── monadString maps each effect constructor to a string ────────────────────────

theorem monadString_Pure_val : monadString Effect.Pure = PURE_MONAD := by rfl
theorem monadString_IO_val : monadString Effect.IO = "IO" := by rfl
theorem monadString_Async_val : monadString Effect.Async = "IO" := by rfl
theorem monadString_Async_eq_IO : monadString Effect.Async = monadString Effect.IO := by rfl

-- ─── doMonadType format ──────────────────────────────────────────────────────────

theorem doMonadType_format (s : String) :
    doMonadType s = s!"DOMonad {s}" := by rfl

-- ─── isAssignOp / isIncrDecr correctness ─────────────────────────────────────────

theorem isAssignOp_EqualsToken : isAssignOp "EqualsToken" = true := by native_decide
theorem isIncrDecr_PlusPlusToken : isIncrDecr "PlusPlusToken" = true := by native_decide
theorem isIncrDecr_not_equals : isIncrDecr "EqualsToken" = false := by native_decide
theorem isAssignOp_not_plusplus : isAssignOp "PlusPlusToken" = false := by native_decide

-- ─── getFunctionBody ──────────────────────────────────────────────────────────────

theorem getFunctionBody_empty : getFunctionBody "" = none := by
  simp [getFunctionBody]

theorem getFunctionBody_nonempty :
    getFunctionBody "someNode" = some "someNode" := by native_decide
