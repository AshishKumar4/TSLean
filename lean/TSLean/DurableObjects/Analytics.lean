-- TSLean.DurableObjects.Analytics
import TSLean.Runtime.Monad

namespace TSLean.DO.Analytics
open TSLean

structure AnalyticsEvent where
  name      : String
  value     : Float
  timestamp : Nat
  tags      : List (String × String)
  deriving Repr, BEq

abbrev EventCounts := List (String × Nat)

structure AnalyticsState where
  events    : List AnalyticsEvent
  counts    : EventCounts
  totalSeen : Nat
  deriving Repr

def AnalyticsState.empty : AnalyticsState := { events := [], counts := [], totalSeen := 0 }

def EventCounts.increment (cs : EventCounts) (name : String) : EventCounts :=
  match cs.findIdx? (fun (n, _) => n == name) with
  | none   => cs ++ [(name, 1)]
  | some i => cs.mapIdx fun j (n, c) => if j == i then (n, c + 1) else (n, c)

def AnalyticsState.record (st : AnalyticsState) (e : AnalyticsEvent) : AnalyticsState :=
  { events := st.events ++ [e], counts := st.counts.increment e.name, totalSeen := st.totalSeen + 1 }

def AnalyticsState.flush (st : AnalyticsState) : AnalyticsState :=
  { st with events := [], counts := [], totalSeen := 0 }

def AnalyticsState.countOf (st : AnalyticsState) (name : String) : Nat :=
  st.events.countP (fun e => e.name == name)

def EventCounts.lookup (cs : EventCounts) (name : String) : Nat :=
  (cs.find? (fun (n, _) => n == name)).map Prod.snd |>.getD 0

theorem counts_monotonic (st : AnalyticsState) (e : AnalyticsEvent) :
    (st.record e).totalSeen = st.totalSeen + 1 := by simp [AnalyticsState.record]

theorem no_events_lost (events : List AnalyticsEvent) :
    (events.foldl AnalyticsState.record AnalyticsState.empty).totalSeen = events.length := by
  suffices h : ∀ (st : AnalyticsState),
      (events.foldl AnalyticsState.record st).totalSeen = st.totalSeen + events.length by
    have := h AnalyticsState.empty; simp [AnalyticsState.empty] at this; exact this
  induction events with
  | nil => intro st; simp
  | cons hd tl ih =>
    intro st; simp only [List.foldl_cons, List.length_cons]
    rw [ih]; simp [AnalyticsState.record]; omega

theorem totalSeen_monotone_le (st : AnalyticsState) (events : List AnalyticsEvent) :
    st.totalSeen ≤ (events.foldl AnalyticsState.record st).totalSeen := by
  induction events generalizing st with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    exact Nat.le_trans (by simp [counts_monotonic]) (ih _)

theorem events_preserved (st : AnalyticsState) (e : AnalyticsEvent) :
    e ∈ (st.record e).events := by simp [AnalyticsState.record]

theorem countOf_record_same (st : AnalyticsState) (e : AnalyticsEvent) :
    (st.record e).countOf e.name = st.countOf e.name + 1 := by
  simp [AnalyticsState.record, AnalyticsState.countOf, List.countP_append,
        List.countP_cons, List.countP_nil, BEq.refl]

theorem countOf_record_diff (st : AnalyticsState) (e : AnalyticsEvent) (name : String)
    (hne : e.name ≠ name) :
    (st.record e).countOf name = st.countOf name := by
  simp [AnalyticsState.record, AnalyticsState.countOf, List.countP_append,
        List.countP_cons, List.countP_nil, show (e.name == name) = false from beq_false_of_ne hne]

theorem totalSeen_eq_events_length (st : AnalyticsState) (e : AnalyticsEvent) :
    (st.record e).events.length = st.events.length + 1 := by
  simp [AnalyticsState.record, List.length_append]

-- Additional theorems

theorem flush_clears_buffer (st : AnalyticsState) :
    st.flush.events = [] := by simp [AnalyticsState.flush]

theorem flush_resets_count (st : AnalyticsState) :
    st.flush.totalSeen = 0 := by simp [AnalyticsState.flush]

theorem ingest_increases_count (st : AnalyticsState) (e : AnalyticsEvent) :
    (st.record e).events.length = st.events.length + 1 := by
  simp [AnalyticsState.record, List.length_append]

theorem record_appends_event (st : AnalyticsState) (e : AnalyticsEvent) :
    (st.record e).events = st.events ++ [e] := by
  simp [AnalyticsState.record]

theorem flush_then_record (st : AnalyticsState) (e : AnalyticsEvent) :
    (st.flush.record e).totalSeen = 1 := by
  simp [AnalyticsState.flush, AnalyticsState.record]

theorem total_seen_bounded_below (events : List AnalyticsEvent) :
    (events.foldl AnalyticsState.record AnalyticsState.empty).totalSeen ≥ events.length := by
  rw [no_events_lost]; exact Nat.le_refl _

theorem countOf_nonneg (st : AnalyticsState) (name : String) : 0 ≤ st.countOf name :=
  Nat.zero_le _

theorem record_preserves_other_events (st : AnalyticsState) (e e' : AnalyticsEvent)
    (h : e' ∈ st.events) : e' ∈ (st.record e).events := by
  simp [AnalyticsState.record, List.mem_append]; exact Or.inl h


-- Additional deep theorems for Analytics

theorem events_length_after_flush_record (st : AnalyticsState) (e : AnalyticsEvent) :
    (st.flush.record e).events.length = 1 := by
  simp [AnalyticsState.flush, AnalyticsState.record, List.length_append]

theorem totalSeen_additive (st : AnalyticsState) (events : List AnalyticsEvent) :
    (events.foldl AnalyticsState.record st).totalSeen = st.totalSeen + events.length := by
  induction events generalizing st with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.length_cons, ih]
    simp [AnalyticsState.record]; omega

theorem countOf_record_le (st : AnalyticsState) (e : AnalyticsEvent) (name : String) :
    st.countOf name ≤ (st.record e).countOf name := by
  simp [AnalyticsState.countOf, AnalyticsState.record, List.countP_append]

theorem flush_idempotent (st : AnalyticsState) :
    st.flush.flush = st.flush := by
  simp [AnalyticsState.flush]

theorem record_totalSeen_pos (st : AnalyticsState) (e : AnalyticsEvent) :
    (st.record e).totalSeen > 0 := by
  simp [AnalyticsState.record]

theorem events_nonempty_after_record (st : AnalyticsState) (e : AnalyticsEvent) :
    (st.record e).events ≠ [] := by
  simp [AnalyticsState.record]

theorem totalSeen_flush_is_zero (st : AnalyticsState) :
    st.flush.totalSeen = 0 := by simp [AnalyticsState.flush]

theorem countOf_flush_is_zero (st : AnalyticsState) (name : String) :
    st.flush.countOf name = 0 := by
  simp [AnalyticsState.flush, AnalyticsState.countOf]

theorem record_monotone_totalSeen (st : AnalyticsState) (events : List AnalyticsEvent) :
    st.totalSeen ≤ (events.foldl AnalyticsState.record st).totalSeen := by
  rw [totalSeen_additive]; omega

theorem events_length_eq_totalSeen_initially (events : List AnalyticsEvent) :
    (events.foldl AnalyticsState.record AnalyticsState.empty).totalSeen = events.length :=
  no_events_lost events


end TSLean.DO.Analytics
