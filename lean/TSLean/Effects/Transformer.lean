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

end TSLean.Effects
