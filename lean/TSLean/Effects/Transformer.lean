-- TSLean.Effects.Transformer
import TSLean.Effects.Core
import TSLean.Runtime.Monad

namespace TSLean.Effects

open TSLean EffectSet

/-- Map from EffectSet to the appropriate monad stack -/
def effectMonad (σ : Type) (eff : EffectSet) (α : Type) : Type :=
  if eff.mem .except_ then StateT σ (ExceptT TSError IO) α else StateT σ IO α

-- Key type class: a monad that can express a given set of effects
class EffectfulMonad (m : Type → Type) (eff : EffectSet) where
  liftPure : ∀ {α}, α → m α
  liftIO   : ∀ {α}, IO α → m α

instance (σ : Type) : EffectfulMonad (StateT σ IO) (empty) where
  liftPure a := pure a
  liftIO  io := liftM io

instance (σ : Type) : EffectfulMonad (StateT σ (ExceptT TSError IO)) doMonadEffects where
  liftPure a := pure a
  liftIO  io := liftM io

-- Effect composition theorems
theorem combine_idempotent_mem (s : EffectSet) (e : EffectKind) (h : mem e s) :
    mem e (combine s s) = true := by
  -- e ∈ s implies e ∈ combine s s, since combine s t ⊇ s (by le_combine_left)
  simp only [mem, List.contains_iff_mem]
  have hle := le_combine_left s s
  simp only [subset, List.all_eq_true, List.contains_iff_mem] at hle
  exact hle e (List.contains_iff_mem.mp h)

theorem empty_subset_all (s : EffectSet) : subset empty s = true := pure_le s

/-! ## ExceptT / DO monad integration -/

/-- Run an ExceptT action, converting the error to TSError if it fails. -/
def runExceptT_asTSError [Monad m] (action : ExceptT String m α) : ExceptT TSError m α :=
  ExceptT.mk do
    match ← action.run with
    | .ok a    => pure (.ok a)
    | .error s => pure (.error (TSError.typeError s))

/-- Lift an Except into ExceptT. -/
def liftExcept [Monad m] (e : Except ε α) : ExceptT ε m α :=
  ExceptT.mk (pure e)

/-- Run an IO action inside a StateT+ExceptT stack, discarding state. -/
def runDO [Inhabited σ] (action : StateT σ (ExceptT TSError IO) α) : IO (Except TSError α) := do
  match ← (action.run default).run with
  | .ok (a, _) => pure (.ok a)
  | .error e   => pure (.error e)

end TSLean.Effects
