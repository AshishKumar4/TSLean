-- TSLean.Stdlib.OptionResult
import TSLean.Runtime.Basic

namespace TSLean.Stdlib.OptionResult
open TSLean

def orElse  {α} (o : Option α) (d : α) : α := o.getD d
def mapOpt  {α β} (o : Option α) (f : α → β) : Option β := o.map f
def bindOpt {α β} (o : Option α) (f : α → Option β) : Option β := o.bind f
def liftA2  {α β γ} (f : α → β → γ) (o₁ : Option α) (o₂ : Option β) : Option γ :=
  o₁.bind fun a => o₂.map (f a)
def fromOption {α} (o : Option α) (e : TSError) : TSResult α :=
  match o with | none => .error e | some a => .ok a
def toOption {α} (r : TSResult α) : Option α :=
  match r with | .ok a => some a | .error _ => none
def filterOpt {α} (o : Option α) (p : α → Bool) : Option α := o.filter p
def sequenceList {α} (opts : List (Option α)) : Option (List α) := opts.mapM id
def mapResult    {α β} (r : TSResult α) (f : α → β) : TSResult β := r.map f
def bindResult   {α β} (r : TSResult α) (f : α → TSResult β) : TSResult β := r.bind f
def recoverResult {α} (r : TSResult α) (f : TSError → TSResult α) : TSResult α :=
  match r with | .ok a => .ok a | .error e => f e
def isOk    {α} (r : TSResult α) : Bool := r.isOk
def isError {α} (r : TSResult α) : Bool := !r.isOk
def liftOption {α} (o : Option α) (err : TSError) : TSResult α :=
  match o with | some a => .ok a | none => .error err

-- Theorems
theorem option_pure_bind {α β} (a : α) (f : α → Option β) : (pure a : Option α) >>= f = f a := by simp
theorem option_bind_pure {α} (o : Option α) : o >>= (pure : α → Option α) = o := by cases o <;> simp
theorem option_bind_assoc {α β γ} (o : Option α) (f : α → Option β) (g : β → Option γ) :
    (o >>= f) >>= g = o >>= fun x => f x >>= g := Option.bind_assoc o f g
theorem none_bind {α β} (f : α → Option β) : (none : Option α) >>= f = none := rfl
theorem some_bind {α β} (a : α) (f : α → Option β) : some a >>= f = f a := rfl
theorem mapOpt_eq {α β} (o : Option α) (f : α → β) : mapOpt o f = o.map f := rfl
theorem mapOpt_none {α β} (f : α → β) : mapOpt (none : Option α) f = none := rfl
theorem mapOpt_some {α β} (a : α) (f : α → β) : mapOpt (some a) f = some (f a) := rfl
theorem orElse_none {α} (d : α) : orElse (none : Option α) d = d := rfl
theorem orElse_some {α} (a d : α) : orElse (some a) d = a := rfl
theorem toOption_fromOption {α} (a : α) (e : TSError) : toOption (fromOption (some a) e) = some a := rfl
theorem fromOption_none {α} (e : TSError) : fromOption (none : Option α) e = .error e := rfl
theorem toOption_ok {α} (a : α) : toOption (.ok a : TSResult α) = some a := rfl
theorem toOption_error {α} (e : TSError) : toOption (.error e : TSResult α) = none := rfl
theorem result_pure_bind {α β} (a : α) (f : α → TSResult β) :
    (pure a : TSResult α) >>= f = f a := by simp [bind, Except.bind, pure, Except.pure]
theorem result_bind_pure {α} (r : TSResult α) :
    r >>= (pure : α → TSResult α) = r := by cases r <;> simp [bind, Except.bind, pure, Except.pure]
theorem result_bind_assoc {α β γ} (r : TSResult α) (f : α → TSResult β) (g : β → TSResult γ) :
    (r >>= f) >>= g = r >>= fun x => f x >>= g := by cases r <;> simp [bind, Except.bind]
theorem isOk_iff {α} (r : TSResult α) : isOk r = true ↔ ∃ a, r = .ok a := by
  cases r with | ok a => simp [isOk, Except.isOk, Except.toBool] | error e => simp [isOk, Except.isOk, Except.toBool]
theorem isError_iff {α} (r : TSResult α) : isError r = true ↔ ∃ e, r = .error e := by
  cases r with
  | ok a => simp [isError, Except.isOk, Except.toBool]
  | error e =>
    constructor
    · intro _; exact ⟨e, rfl⟩
    · intro _; simp [isError, Except.isOk, Except.toBool]
theorem recoverResult_ok {α} (a : α) (f : TSError → TSResult α) : recoverResult (.ok a) f = .ok a := rfl
theorem recoverResult_error {α} (e : TSError) (f : TSError → TSResult α) : recoverResult (.error e) f = f e := rfl
theorem liftA2_none_left {α β γ} (f : α → β → γ) (o₂ : Option β) : liftA2 f none o₂ = none := rfl
theorem liftA2_none_right {α β γ} (f : α → β → γ) (a : α) : liftA2 f (some a) none = none := rfl
theorem liftA2_some {α β γ} (f : α → β → γ) (a : α) (b : β) : liftA2 f (some a) (some b) = some (f a b) := rfl
theorem filterOpt_true {α} (a : α) (p : α → Bool) (h : p a = true) : filterOpt (some a) p = some a := by
  simp [filterOpt, Option.filter, h]
theorem filterOpt_false {α} (a : α) (p : α → Bool) (h : p a = false) : filterOpt (some a) p = none := by
  simp [filterOpt, Option.filter, h]

theorem filterOpt_none {α} (p : α → Bool) : filterOpt (none : Option α) p = none := rfl

theorem mapOpt_comp {α β γ} (f : α → β) (g : β → γ) (o : Option α) :
    mapOpt (mapOpt o f) g = mapOpt o (g ∘ f) := by
  cases o <;> simp [mapOpt, Function.comp]

theorem bindOpt_assoc {α β γ} (o : Option α) (f : α → Option β) (g : β → Option γ) :
    bindOpt (bindOpt o f) g = bindOpt o (fun x => bindOpt (f x) g) := by
  cases o <;> simp [bindOpt]

theorem liftOption_ok {α} (a : α) (e : TSError) : liftOption (some a) e = .ok a := rfl
theorem liftOption_error {α} (e : TSError) : liftOption (none : Option α) e = .error e := rfl

theorem mapResult_id {α} (r : TSResult α) : mapResult r id = r := by
  cases r <;> simp [mapResult]

theorem mapResult_comp {α β γ} (f : α → β) (g : β → γ) (r : TSResult α) :
    mapResult (mapResult r f) g = mapResult r (g ∘ f) := by
  cases r <;> simp [mapResult, Except.map, Function.comp]

theorem bindResult_ok {α β} (a : α) (f : α → TSResult β) :
    bindResult (.ok a) f = f a := by simp [bindResult, Except.bind]

theorem bindResult_error {α β} (e : TSError) (f : α → TSResult β) :
    bindResult (.error e) f = .error e := by simp [bindResult, Except.bind]

theorem toOption_toResult {α} (o : Option α) (e : TSError) :
    toOption (fromOption o e) = o := by
  cases o <;> simp [toOption, fromOption]

theorem sequenceList_nil {α} : sequenceList ([] : List (Option α)) = some [] := by
  simp [sequenceList]

theorem sequenceList_cons_none {α} (l : List (Option α)) :
    sequenceList ((none : Option α) :: l) = none := by simp [sequenceList]

theorem isOk_ok {α} (a : α) : isOk (.ok a : TSResult α) = true := by
  simp [isOk, Except.isOk, Except.toBool]

theorem isError_error {α} (e : TSError) : isError (.error e : TSResult α) = true := by
  simp [isError, Except.isOk, Except.toBool]

end TSLean.Stdlib.OptionResult
