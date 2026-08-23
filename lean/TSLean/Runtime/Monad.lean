-- TSLean.Runtime.Monad
-- TaskM and DOMonad definitions, MonadLift instances, monad laws.
-- IO monad laws are declared as axioms because IO does not have
-- LawfulMonad in Lean 4 core — they hold semantically but cannot
-- be proved in pure Lean 4.

import TSLean.Runtime.Basic

namespace TSLean

abbrev TaskM α := IO α
abbrev DOMonad (σ : Type) (α : Type) := StateT σ (ExceptT TSError IO) α

def runDOMonad {σ α : Type} (m : DOMonad σ α) (s : σ) : IO (Except TSError (α × σ)) :=
  ExceptT.run (StateT.run m s)

section DOMonadOps
variable {σ : Type}

def pureDO {α} (a : α) : DOMonad σ α := pure a
def liftIO_DO {α} (io : IO α) : DOMonad σ α := liftM io
def throwDO {α} (e : TSError) : DOMonad σ α := throw e
def getDO : DOMonad σ σ := get
def setDO (s : σ) : DOMonad σ Unit := set s
def modifyDO (f : σ → σ) : DOMonad σ Unit := modify f
def catchDO {α} (m : DOMonad σ α) (h : TSError → DOMonad σ α) : DOMonad σ α := tryCatch m h
end DOMonadOps

instance : MonadLift IO (DOMonad σ) where monadLift io := liftIO_DO io
instance : MonadLift (Except TSError) (DOMonad σ) where
  monadLift e := match e with | .ok a => pure a | .error err => throwDO err

/-! ## Monad laws

Deliberately absent. An earlier version asserted thirteen `axiom`s here -- the `DOMonad` and `TaskM`
monad, state and catch laws -- on the grounds that the runtime implements them correctly and the type
theory cannot see it. Two things were wrong with that. `REBUILD_PLAN.md` §6 rule 6 requires platform
behaviour to be a capability parameter, never an axiom, and rule 7 allows exactly three axioms. And
every generated module that is not pure imports this file, so those thirteen sat in the trusted base
of every artifact the compiler produced, where the audit could not see them.

Measured before removal: nothing anywhere consumed any of the thirteen. They were decoration. If a
law is genuinely needed later, the honest form is the one `TSLean.Refinement.Float` already uses -- a
`Prop`-valued definition taken as a hypothesis, with `Assumption` metadata that appears in the
artifact's ledger. -/

end TSLean
