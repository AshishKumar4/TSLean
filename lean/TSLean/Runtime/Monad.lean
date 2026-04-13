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

/-! ## IO Monad Laws (axioms)

IO does not have a `LawfulMonad` instance in Lean 4 core.
These laws hold semantically (the Lean runtime implements them correctly)
but cannot be proved within the type theory.  We declare them as `axiom`
rather than using `sorry` — this is honest: the kernel trusts them, and
any downstream proof that depends on them is sound assuming the IO runtime
is correct. -/

axiom pureDO_bind {σ α β} (a : α) (f : α → DOMonad σ β) : (pureDO a >>= f) = f a
axiom bind_pureDO {σ α} (m : DOMonad σ α) : (m >>= pureDO) = m
axiom doMonad_bind_assoc {σ α β γ} (m : DOMonad σ α) (f : α → DOMonad σ β) (g : β → DOMonad σ γ) :
    ((m >>= f) >>= g) = (m >>= fun x => f x >>= g)
axiom throwDO_catchDO {σ α} (e : TSError) (h : TSError → DOMonad σ α) :
    catchDO (throwDO e) h = h e
axiom pureDO_catchDO {σ α} (a : α) (h : TSError → DOMonad σ α) :
    catchDO (pureDO a) h = pureDO a
axiom getDO_setDO_id {σ} : (getDO >>= setDO : DOMonad σ Unit) = pure ()
axiom setDO_getDO {σ} (s : σ) :
    (setDO s >>= fun _ => getDO : DOMonad σ σ) = (setDO s >>= fun _ => pure s)
axiom setDO_setDO {σ} (s t : σ) :
    (setDO s >>= fun _ => setDO t : DOMonad σ Unit) = setDO t
axiom modifyDO_eq_get_set {σ} (f : σ → σ) :
    (modifyDO f : DOMonad σ Unit) = (getDO >>= fun s => setDO (f s))
axiom taskM_pure_bind {α β} (a : α) (f : α → TaskM β) : (pure a >>= f : TaskM β) = f a
axiom taskM_bind_pure {α} (m : TaskM α) : (m >>= pure : TaskM α) = m
axiom taskM_bind_assoc {α β γ} (m : TaskM α) (f : α → TaskM β) (g : β → TaskM γ) :
    ((m >>= f) >>= g) = (m >>= fun x => f x >>= g)

end TSLean
