-- TSLean.DurableObjects.Alarm
import TSLean.Runtime.Monad

namespace TSLean.DO.Alarm
open TSLean

structure Alarm where
  id          : Nat
  scheduledAt : Nat
  createdAt   : Nat
  deriving Repr, BEq

structure AlarmState where
  pending  : List Alarm
  fired    : List Alarm
  nextId   : Nat
  deriving Repr

def AlarmState.empty : AlarmState := { pending := [], fired := [], nextId := 0 }

def AlarmState.schedule (st : AlarmState) (scheduledAt now : Nat) : AlarmState :=
  let alarm : Alarm := { id := st.nextId, scheduledAt, createdAt := now }
  { st with pending := st.pending ++ [alarm], nextId := st.nextId + 1 }

def AlarmState.cancel (st : AlarmState) (id : Nat) : AlarmState :=
  { st with pending := st.pending.filter (fun a => a.id != id) }

def AlarmState.tick (st : AlarmState) (now : Nat) : AlarmState :=
  let due := st.pending.filter (fun a => a.scheduledAt ≤ now)
  let rem := st.pending.filter (fun a => a.scheduledAt > now)
  { st with pending := rem, fired := st.fired ++ due }

def AlarmState.next (st : AlarmState) : Option Alarm :=
  st.pending.foldl (fun acc a => match acc with
    | none   => some a
    | some b => if a.scheduledAt < b.scheduledAt then some a else some b) none

def AlarmState.hasDue (st : AlarmState) (now : Nat) : Bool :=
  st.pending.any (fun a => a.scheduledAt ≤ now)

theorem schedule_nextId_succ (st : AlarmState) (scheduledAt now : Nat) :
    (st.schedule scheduledAt now).nextId = st.nextId + 1 := by simp [AlarmState.schedule]

theorem nextId_monotone (st : AlarmState) (scheduledAt now : Nat) :
    st.nextId ≤ (st.schedule scheduledAt now).nextId := by simp [AlarmState.schedule]

theorem tick_fires_due (st : AlarmState) (now : Nat) (a : Alarm)
    (h : a ∈ st.pending) (hdue : a.scheduledAt ≤ now) :
    a ∈ (st.tick now).fired := by simp [AlarmState.tick, List.mem_append, List.mem_filter]; exact Or.inr ⟨h, hdue⟩

theorem tick_keeps_not_due (st : AlarmState) (now : Nat) (a : Alarm)
    (h : a ∈ st.pending) (hnot : a.scheduledAt > now) :
    a ∈ (st.tick now).pending := by simp [AlarmState.tick, List.mem_filter, h, hnot]

theorem cancel_removes (st : AlarmState) (id : Nat) :
    ¬∃ a ∈ (st.cancel id).pending, a.id = id := by
  simp only [AlarmState.cancel, List.mem_filter]
  intro ⟨a, ⟨_, hne⟩, ha⟩
  simp only [bne_iff_ne, ne_eq] at hne
  exact hne ha

theorem hasDue_monotone (st : AlarmState) (now now' : Nat) (h : now ≤ now')
    (hdue : st.hasDue now = true) : st.hasDue now' = true := by
  simp [AlarmState.hasDue, List.any_eq_true] at *
  obtain ⟨a, hmem, hle⟩ := hdue; exact ⟨a, hmem, Nat.le_trans hle h⟩

-- fired_monotone: as time advances, more alarms fire (the filter grows).
private theorem filter_mono {α} (l : List α) (p q : α → Bool) (hpq : ∀ x, p x = true → q x = true) :
    (l.filter p).length ≤ (l.filter q).length := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.filter_cons]
    rcases Bool.eq_false_or_eq_true (p hd) with hp | hp <;>
    rcases Bool.eq_false_or_eq_true (q hd) with hq | hq
    · simp [hp, hq]; exact ih
    · exact absurd (hpq hd hp) (by simp [hq])
    · simp [hp, hq]; omega
    · simp [hp, hq]; exact ih

theorem fired_monotone (st : AlarmState) (now now' : Nat) (h : now ≤ now') :
    (st.tick now).fired.length ≤ (st.tick now').fired.length := by
  simp only [AlarmState.tick, List.length_append]
  apply Nat.add_le_add_left
  apply filter_mono
  intro a ha
  simp only [decide_eq_true_eq] at *
  exact Nat.le_trans ha h

theorem schedule_increases_pending (st : AlarmState) (scheduledAt now : Nat) :
    (st.schedule scheduledAt now).pending.length = st.pending.length + 1 := by
  simp [AlarmState.schedule, List.length_append]

theorem cancel_preserves_fired (st : AlarmState) (id : Nat) :
    (st.cancel id).fired = st.fired := rfl

theorem alarm_scheduled_id_is_nextId (st : AlarmState) (scheduledAt now : Nat) :
    ((st.schedule scheduledAt now).pending.getLast?).map (·.id) =
    some st.nextId := by
  simp [AlarmState.schedule, List.getLast?_append]

theorem tick_empty_pending_when_all_fired (st : AlarmState) (now : Nat)
    (h : ∀ a ∈ st.pending, a.scheduledAt ≤ now) :
    (st.tick now).pending = [] := by
  simp only [AlarmState.tick]
  apply List.filter_eq_nil_iff.mpr
  intro a ha; simp only [decide_eq_true_eq]; exact Nat.not_lt.mpr (h a ha)

-- Generalized helper: foldl min-finder returns an element of the list or the accumulator.
-- (unused: was placeholder)

-- Key lemma: foldl over alarms either returns acc or an element of the list
private theorem alarm_foldl_membership (l : List Alarm) (acc : Option Alarm) :
    ∀ a, l.foldl (fun acc' x => match acc' with
        | none => some x
        | some b => if x.scheduledAt < b.scheduledAt then some x else some b) acc = some a →
    a ∈ l ∨ acc = some a := by
  induction l generalizing acc with
  | nil => intro a h; right; exact h
  | cons hd tl ih =>
    intro a h
    simp only [List.foldl_cons] at h
    rcases acc with _ | acc_val
    · -- acc = none: first step sets acc = some hd
      rcases ih (some hd) a h with hmem | heq
      · exact Or.inl (List.mem_cons_of_mem _ hmem)
      · simp only [Option.some.injEq] at heq
        exact Or.inl (List.mem_cons.mpr (Or.inl heq.symm))
    · -- acc = some acc_val
      let next_acc := if hd.scheduledAt < acc_val.scheduledAt then some hd else some acc_val
      rcases ih next_acc a h with hmem | heq
      · exact Or.inl (List.mem_cons_of_mem _ hmem)
      · simp only [next_acc] at heq
        split at heq
        · simp only [Option.some.injEq] at heq
          exact Or.inl (List.mem_cons.mpr (Or.inl heq.symm))
        · exact Or.inr heq

-- next_in_pending: the min alarm returned is in pending.
theorem next_in_pending (st : AlarmState) (a : Alarm)
    (h : st.next = some a) : a ∈ st.pending := by
  simp only [AlarmState.next] at h
  rcases alarm_foldl_membership st.pending none a h with hmem | hnone
  · exact hmem
  · simp at hnone

theorem schedule_preserves_fired (st : AlarmState) (scheduledAt now : Nat) :
    (st.schedule scheduledAt now).fired = st.fired := rfl

theorem empty_pending_no_due (now : Nat) :
    AlarmState.empty.hasDue now = false := by
  simp [AlarmState.empty, AlarmState.hasDue]

theorem tick_fired_includes_original (st : AlarmState) (now : Nat) :
    st.fired.Sublist (st.tick now).fired := by
  simp only [AlarmState.tick]
  exact List.sublist_append_left _ _

theorem nextId_zero_initially : AlarmState.empty.nextId = 0 := rfl


-- Additional Alarm deep theorems


theorem schedule_increases_nextId (st : AlarmState) (at' now : Nat) :
    (st.schedule at' now).nextId = st.nextId + 1 := schedule_nextId_succ st at' now

theorem hasDue_iff (st : AlarmState) (now : Nat) :
    st.hasDue now = true ↔ ∃ a ∈ st.pending, a.scheduledAt ≤ now := by
  simp [AlarmState.hasDue, List.any_eq_true, decide_eq_true_eq]

theorem cancel_idempotent (st : AlarmState) (id : Nat) :
    (st.cancel id).cancel id = st.cancel id := by
  simp [AlarmState.cancel, List.filter_filter, Bool.and_self]

theorem next_is_none_of_empty (st : AlarmState) (h : st.pending = []) :
    st.next = none := by
  simp [AlarmState.next, h]

-- If next returns some, pending was nonempty (follows from next_in_pending)
theorem next_some_implies_pending_nonempty (st : AlarmState) (a : Alarm)
    (h : st.next = some a) : st.pending ≠ [] := by
  intro hemp
  simp [AlarmState.next, hemp] at h

theorem schedule_pending_nonempty (st : AlarmState) (at' now : Nat) :
    (st.schedule at' now).pending ≠ [] := by
  simp only [AlarmState.schedule]
  exact List.ne_nil_of_length_pos (by simp [List.length_append])

theorem tick_clears_due_alarms (st : AlarmState) (now : Nat)
    (h : ∀ a ∈ st.pending, a.scheduledAt ≤ now) :
    (st.tick now).pending = [] := tick_empty_pending_when_all_fired st now h

theorem alarm_in_fired_was_pending (st : AlarmState) (now : Nat) (a : Alarm)
    (h : a ∈ (st.tick now).fired) (hori : a ∉ st.fired) :
    a ∈ st.pending := by
  simp only [AlarmState.tick, List.mem_append] at h
  rcases h with hori2 | hfire
  · exact absurd hori2 hori
  · simp [List.mem_filter, decide_eq_true_eq] at hfire; exact hfire.1

theorem nextId_grows_on_schedule (st : AlarmState) (at' now : Nat) :
    st.nextId < (st.schedule at' now).nextId := by
  simp [AlarmState.schedule]

end TSLean.DO.Alarm
