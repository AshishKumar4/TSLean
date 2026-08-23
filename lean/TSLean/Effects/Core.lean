-- TSLean.Effects.Core
namespace TSLean.Effects

inductive EffectKind : Type where
  | pure | stateRead | stateWrite | io | async_ | except_ | network | storage
  deriving Repr, BEq, DecidableEq

instance : LawfulBEq EffectKind where
  eq_of_beq {x y} h := by cases x <;> cases y <;> (first | rfl | exact absurd h (by decide))
  rfl := by intro x; cases x <;> rfl

namespace EffectKind
def involves_state (e : EffectKind) : Bool := e == stateRead || e == stateWrite
end EffectKind

structure EffectSet where
  elems : List EffectKind
  nodup : elems.Nodup
  deriving Repr

namespace EffectSet

private def insertEff (e : EffectKind) (l : List EffectKind) : List EffectKind :=
  if l.contains e then l else e :: l

private theorem insertEff_nodup (e : EffectKind) (l : List EffectKind) (h : l.Nodup) :
    (insertEff e l).Nodup := by
  simp only [insertEff]; split
  · exact h
  · refine List.nodup_cons.mpr ⟨?_, h⟩
    simp only [List.contains_iff_mem] at *; assumption

private def unionElems : List EffectKind → List EffectKind → List EffectKind
  | [],      acc => acc
  | e :: es, acc => unionElems es (insertEff e acc)

private theorem unionElems_nodup : ∀ (l1 l2 : List EffectKind), l2.Nodup → (unionElems l1 l2).Nodup := by
  intro l1; induction l1 with
  | nil => intro l2 h; exact h
  | cons hd tl ih => intro l2 h; simp only [unionElems]; exact ih _ (insertEff_nodup hd l2 h)

def empty       : EffectSet := { elems := [], nodup := List.nodup_nil }
def pure_set    : EffectSet := empty
def io_set      : EffectSet := { elems := [.io],     nodup := by decide }
def async_set   : EffectSet := { elems := [.async_], nodup := by decide }
def except_set  : EffectSet := { elems := [.except_], nodup := by decide }
def state_set   : EffectSet := { elems := [.stateRead, .stateWrite], nodup := by decide }
def network_set : EffectSet := { elems := [.network], nodup := by decide }
def storage_set : EffectSet := { elems := [.storage], nodup := by decide }
def universal   : EffectSet :=
  { elems := [.pure,.stateRead,.stateWrite,.io,.async_,.except_,.network,.storage], nodup := by decide }
def doMonadEffects : EffectSet := { elems := [.stateRead,.stateWrite,.io,.except_], nodup := by decide }

def combine (s t : EffectSet) : EffectSet :=
  { elems := unionElems s.elems t.elems, nodup := unionElems_nodup s.elems t.elems t.nodup }

def mem    (e : EffectKind) (s : EffectSet) : Bool := s.elems.contains e
def subset (s t : EffectSet) : Bool := s.elems.all (fun e => t.elems.contains e)
def subsumes (s t : EffectSet) : Bool := subset s t
def handle (s : EffectSet) (e : EffectKind) : EffectSet :=
  { elems := s.elems.erase e, nodup := s.nodup.erase e }

theorem pure_le (s : EffectSet) : subset empty s = true := by simp [subset, empty]
theorem io_in_doMonadEffects     : mem .io      doMonadEffects = true := by decide
theorem except_in_doMonadEffects : mem .except_ doMonadEffects = true := by decide
theorem handle_subset (s : EffectSet) (e : EffectKind) :
    (s.handle e).elems.Sublist s.elems := @List.erase_sublist _ _ e s.elems
theorem combine_pure_left (s : EffectSet) : (combine empty s).elems = s.elems := by
  simp [combine, unionElems, empty]
private theorem mem_unionElems_of_mem_acc (e : EffectKind) :
    ∀ (l acc : List EffectKind), e ∈ acc → e ∈ unionElems l acc := by
  intro l; induction l with
  | nil => intro acc ha; exact ha
  | cons hd tl ih =>
    intro acc ha
    simp only [unionElems]
    apply ih
    simp only [insertEff]
    split
    · exact ha
    · exact List.mem_cons_of_mem _ ha

private theorem mem_insertEff_self (e : EffectKind) (acc : List EffectKind) : e ∈ insertEff e acc := by
  simp only [insertEff]
  split
  · exact List.contains_iff_mem.mp ‹_›
  · exact List.mem_cons_self

private theorem mem_unionElems_of_mem_left (e : EffectKind) :
    ∀ (l acc : List EffectKind), e ∈ l → e ∈ unionElems l acc := by
  intro l; induction l with
  | nil => intro acc ha; exact absurd ha List.not_mem_nil
  | cons hd tl ih =>
    intro acc ha
    simp only [List.mem_cons] at ha
    simp only [unionElems]
    cases ha with
    | inl h =>
      subst h
      exact mem_unionElems_of_mem_acc e tl _ (mem_insertEff_self e acc)
    | inr h => exact ih _ h

theorem le_combine_left (s t : EffectSet) : subset s (combine s t) = true := by
  simp only [subset, combine, List.all_eq_true]
  intro e he
  simp only [List.contains_iff_mem] at *
  exact mem_unionElems_of_mem_left e s.elems t.elems he

theorem subset_refl (s : EffectSet) : subset s s = true := by
  simp [subset, List.all_eq_true, List.contains_iff_mem]

theorem subset_trans (s t u : EffectSet) (hst : subset s t = true) (htu : subset t u = true) :
    subset s u = true := by
  simp [subset, List.all_eq_true, List.contains_iff_mem] at *
  intro e he; exact htu e (hst e he)

theorem mem_universal (e : EffectKind) : mem e universal = true := by
  cases e <;> decide

theorem handle_reduces (s : EffectSet) (e : EffectKind) :
    (s.handle e).elems.length ≤ s.elems.length := by
  simp [handle]; exact List.length_erase_le

theorem combine_comm_subset (s t : EffectSet) : subset s (combine t s) = true := by
  simp only [subset, combine, List.all_eq_true]
  intro e he
  simp only [List.contains_iff_mem] at *
  exact mem_unionElems_of_mem_acc e t.elems s.elems he

theorem state_set_involves_state : ∀ e ∈ state_set.elems, e.involves_state = true := by
  decide

theorem doMonadEffects_subset_universal : subset doMonadEffects universal = true := by decide

theorem empty_subset_everything (s : EffectSet) : subset empty s = true := pure_le s

end EffectSet
end TSLean.Effects
