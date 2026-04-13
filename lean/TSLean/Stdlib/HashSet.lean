-- TSLean.Stdlib.HashSet
namespace TSLean.Stdlib.HashSet

structure TSHashSet (α : Type) [DecidableEq α] where
  elems : List α
  nodup : elems.Nodup
  deriving Repr

namespace TSHashSet

variable {α β : Type} [BEq α] [LawfulBEq α] [DecidableEq α] [DecidableEq β]

def empty : TSHashSet α := { elems := [], nodup := List.nodup_nil }
def singleton (x : α) : TSHashSet α := { elems := [x], nodup := by simp }
def contains (s : TSHashSet α) (x : α) : Bool := s.elems.contains x

private theorem insert_nodup (s : TSHashSet α) (x : α) (h : ¬s.contains x = true) :
    (x :: s.elems).Nodup := by
  refine List.nodup_cons.mpr ⟨?_, s.nodup⟩
  intro hmem; exact h (by simp [contains, hmem])

def insert (s : TSHashSet α) (x : α) : TSHashSet α :=
  if h : s.contains x then s
  else { elems := x :: s.elems, nodup := insert_nodup s x h }

def erase (s : TSHashSet α) (x : α) : TSHashSet α :=
  { elems := s.elems.erase x, nodup := s.nodup.erase x }

def size (s : TSHashSet α) : Nat := s.elems.length
def union (s t : TSHashSet α) : TSHashSet α := t.elems.foldl (fun acc x => acc.insert x) s
def inter (s t : TSHashSet α) : TSHashSet α :=
  { elems := s.elems.filter (t.contains ·), nodup := s.nodup.filter _ }
def diff (s t : TSHashSet α) : TSHashSet α :=
  { elems := s.elems.filter (fun x => !t.contains x), nodup := s.nodup.filter _ }
def toList (s : TSHashSet α) : List α := s.elems
def fromList (l : List α) : TSHashSet α := l.foldl (fun acc x => acc.insert x) empty
def map (s : TSHashSet α) (f : α → β) : TSHashSet β := fromList (s.elems.map f)

theorem contains_empty (x : α) : (empty : TSHashSet α).contains x = false := by simp [empty, contains]
theorem size_empty : (empty : TSHashSet α).size = 0 := by simp [empty, size]
theorem size_singleton (x : α) : (singleton x).size = 1 := by simp [singleton, size]
theorem nodup_elems (s : TSHashSet α) : s.elems.Nodup := s.nodup

theorem contains_singleton_same (x : α) : (singleton x).contains x = true := by
  simp [singleton, contains, List.contains_iff_mem]

theorem contains_singleton_diff (x y : α) (h : x ≠ y) : (singleton y).contains x = false := by
  simp [singleton, contains, List.contains_iff_mem, h]

theorem contains_insert_same (s : TSHashSet α) (x : α) : (s.insert x).contains x = true := by
  simp only [insert]; split
  · exact ‹_›
  · simp [contains, List.contains_iff_mem]

theorem insert_idempotent (s : TSHashSet α) (x : α) :
    (s.insert x).insert x = s.insert x := by
  have h : (s.insert x).contains x = true := contains_insert_same s x
  show (if h : (s.insert x).contains x then s.insert x else _) = s.insert x
  exact dif_pos h

theorem erase_not_contains (s : TSHashSet α) (x : α) :
    (s.erase x).contains x = false := by
  simp only [erase, contains]
  rw [Bool.eq_false_iff]
  intro h
  rw [List.contains_iff_mem] at h
  exact List.Nodup.not_mem_erase s.nodup h

-- ¬s.contains x has type ¬(s.contains x = true) since contains returns Bool
-- which is definitionally ¬True or ¬False. The `insert` uses `if h : s.contains x`
-- treating Bool as Prop. So h : ¬s.contains x = true means s.contains x = false.
theorem size_insert_new (s : TSHashSet α) (x : α) (h : ¬s.contains x) :
    (s.insert x).size = s.size + 1 := by
  unfold insert size; rw [dif_neg h]; simp

theorem size_insert_existing (s : TSHashSet α) (x : α) (h : s.contains x = true) :
    (s.insert x).size = s.size := by
  unfold insert size; rw [dif_pos h]

theorem inter_contains_iff (s t : TSHashSet α) (x : α) :
    (s.inter t).contains x = true ↔ s.contains x = true ∧ t.contains x = true := by
  simp [inter, contains, List.contains_iff_mem, List.mem_filter, Bool.and_eq_true]

theorem diff_not_contains (s t : TSHashSet α) (x : α) (h : t.contains x = true) :
    (s.diff t).contains x = false := by
  simp only [diff, contains]
  rw [Bool.eq_false_iff]
  intro hmem
  rw [List.contains_iff_mem, List.mem_filter] at hmem
  -- hmem.2 : ¬(t.contains x) means !t.contains x = true
  -- Together with h : t.contains x = true, this is False
  -- hmem.2 : !t.elems.contains x = true
  -- h : t.contains x = true = t.elems.contains x = true
  simp only [contains] at h
  rw [h] at hmem; simp at hmem

theorem empty_inter (t : TSHashSet α) : (empty : TSHashSet α).inter t = empty := by
  simp only [inter, empty]; rfl

-- Helper: if x is in s, it remains in s.insert y for any y
private theorem contains_after_insert (s : TSHashSet α) (x y : α)
    (h : s.contains x = true) : (s.insert y).contains x = true := by
  simp only [insert]
  split
  · exact h
  · simp only [contains, List.contains_cons, Bool.or_eq_true]
    exact Or.inr h

-- Helper: if x is in acc, x is in (foldl ... acc) for any list l
private theorem foldl_preserves_contains (l : List α) (acc : TSHashSet α) (x : α)
    (h : acc.contains x = true) :
    (l.foldl (fun a y => a.insert y) acc).contains x = true := by
  induction l generalizing acc with
  | nil => exact h
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    exact ih _ (contains_after_insert acc x hd h)

-- Helper: for any acc, x is in (foldl (x::l) ... acc)
private theorem foldl_contains_member (l : List α) (acc : TSHashSet α) (x : α) (h : x ∈ l) :
    (l.foldl (fun a y => a.insert y) acc).contains x = true := by
  induction l generalizing acc with
  | nil => exact absurd h List.not_mem_nil
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | ht
    · exact foldl_preserves_contains tl _ x (contains_insert_same acc x)
    · exact ih _ ht

theorem fromList_contains (l : List α) (x : α) (h : x ∈ l) :
    (fromList l).contains x = true :=
  foldl_contains_member l empty x h

-- Contains is monotone under insert (public wrapper for private helper)
theorem contains_insert_preserved (s : TSHashSet α) (x y : α)
    (h : s.contains x = true) : (s.insert y).contains x = true :=
  contains_after_insert s x y h

-- Erase removes the element (uniqueness of keys ensures this)
theorem not_contains_after_erase (s : TSHashSet α) (x : α) :
    (s.erase x).contains x = false := by
  rw [← Bool.not_eq_true]
  simp only [erase, contains, List.contains_iff_mem]
  exact @List.Nodup.not_mem_erase _ _ _ _ x s.nodup

-- union contains everything from both sets
theorem union_contains_left (s t : TSHashSet α) (x : α)
    (h : s.contains x = true) : (union s t).contains x = true :=
  foldl_preserves_contains t.elems s x h

theorem union_contains_right (s t : TSHashSet α) (x : α)
    (h : t.contains x = true) : (union s t).contains x = true := by
  simp only [contains, List.contains_iff_mem] at h
  exact foldl_contains_member t.elems s x h

-- size is always ≥ 0 (trivially true for Nat)
theorem size_nonneg (s : TSHashSet α) : s.size ≥ 0 := Nat.zero_le _

-- Insert at most increases size by 1
theorem size_insert_le (s : TSHashSet α) (x : α) :
    (s.insert x).size ≤ s.size + 1 := by
  simp only [insert, size]
  split
  · omega
  · simp only [List.length_cons]; omega

-- erase decreases size by at most 1
theorem size_erase_le (s : TSHashSet α) (x : α) :
    (s.erase x).size ≤ s.size := by
  simp only [erase, size]
  exact List.length_erase_le

-- fromList contains all elements
theorem fromList_contains_all (l : List α) :
    ∀ x ∈ l, (fromList l).contains x = true :=
  fun x h => fromList_contains l x h

-- empty doesn't contain anything
theorem not_contains_empty (x : α) : (empty : TSHashSet α).contains x = false := by
  simp [empty, contains]

end TSHashSet
end TSLean.Stdlib.HashSet
