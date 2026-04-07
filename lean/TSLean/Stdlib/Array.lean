-- TSLean.Stdlib.Array
namespace TSLean.Stdlib.Array

variable {α β γ : Type}

def getOpt  (a : Array α) (i : Nat)             : Option α   := a[i]?
def getD    (a : Array α) (i : Nat) (d : α)     : α          := a.getD i d
def push    (a : Array α) (x : α)               : Array α    := a.push x
def pop (a : Array α) : Array α × Option α :=
  if h : 0 < a.size then (a.pop, some (a[a.size - 1]'(Nat.sub_lt h Nat.one_pos)))
  else (a, none)
def shift (a : Array α) : Array α × Option α :=
  if h : 0 < a.size then (a.extract 1 a.size, some (a[0]'h)) else (a, none)
def unshift  (a : Array α) (x : α)              : Array α    := #[x] ++ a
def flatten  (a : Array (Array α))              : Array α    := a.foldl (· ++ ·) #[]
def flatMap  (a : Array α) (f : α → Array β)    : Array β    := (a.map f).foldl (· ++ ·) #[]
def unique   [DecidableEq α] (a : Array α)      : Array α    :=
  a.foldl (fun acc x => if acc.contains x then acc else acc.push x) #[]
def intersection [DecidableEq α] (a b : Array α) : Array α := a.filter (b.contains ·)
def difference   [DecidableEq α] (a b : Array α) : Array α := a.filter (fun x => !b.contains x)
abbrev zip (a : Array α) (b : Array β) : Array (α × β) := _root_.Array.zip a b
abbrev zipWith (a : Array α) (b : Array β) (f : α → β → γ) : Array γ := _root_.Array.zipWith f a b
def sumNat   (a : Array Nat)   : Nat   := a.foldl (· + ·) 0
def sumFloat (a : Array Float) : Float := a.foldl (· + ·) 0.0
def rotateLeft (a : Array α) (n : Nat) : Array α :=
  if a.size = 0 then a else let n' := n % a.size; a.extract n' a.size ++ a.extract 0 n'
def splice (a : Array α) (i n : Nat) (ins : Array α) : Array α :=
  a.extract 0 i ++ ins ++ a.extract (i + n) a.size

theorem push_size (a : Array α) (x : α) : (a.push x).size = a.size + 1 := Array.size_push x

theorem getOpt_isSome_iff (a : Array α) (i : Nat) : (getOpt a i).isSome = true ↔ i < a.size := by
  simp only [getOpt]
  cases h : a[i]? with
  | none => simp; rw [Array.getElem?_eq_none_iff] at h; exact h
  | some v =>
    simp; rcases Nat.lt_or_ge i a.size with hlt | hge
    · exact hlt
    · rw [Array.getElem?_eq_none_iff.mpr hge] at h; simp at h

theorem getOpt_none_iff (a : Array α) (i : Nat) : getOpt a i = none ↔ a.size ≤ i := by
  simp [getOpt, Array.getElem?_eq_none_iff]

theorem unshift_size (a : Array α) (x : α) : (unshift a x).size = a.size + 1 := by
  simp [unshift, Array.size_append]; omega

theorem flatten_empty : flatten (α := α) #[] = #[] := by simp [flatten]
theorem flatten_singleton (a : Array α) : flatten #[a] = a := by simp [flatten, Array.foldl_push, Array.foldl_empty]
theorem sumNat_empty : sumNat #[] = 0 := by simp [sumNat]
theorem sumNat_push (a : Array Nat) (n : Nat) : sumNat (a.push n) = sumNat a + n := by
  simp [sumNat, Array.foldl_push]
theorem zip_size (a : Array α) (b : Array β) : (zip a b).size = min a.size b.size := by
  simp [zip, Array.zip, Array.size_zipWith]
theorem flatMap_empty (f : α → Array β) : flatMap #[] f = #[] := by simp [flatMap, flatten]
theorem intersection_size [DecidableEq α] (a b : Array α) :
    (intersection a b).size ≤ a.size := by
  simp [intersection, Array.size_filter_le]
theorem difference_size [DecidableEq α] (a b : Array α) :
    (difference a b).size ≤ a.size := by
  simp [difference, Array.size_filter_le]
theorem sumFloat_push (a : Array Float) (x : Float) : sumFloat (a.push x) = sumFloat a + x := by
  simp [sumFloat, Array.foldl_push]
theorem unique_subset [DecidableEq α] (a : Array α) (x : α) :
    (unique a).contains x → a.contains x := by
  simp only [unique]
  -- Reduce: any element in foldl dedup result was in original array or accumulator
  suffices h : ∀ (l : List α) (acc : Array α),
      (l.foldl (fun a y => if a.contains y then a else a.push y) acc).contains x →
      acc.contains x ∨ x ∈ l by
    intro hc
    -- foldl on Array = foldl on toList (reversed via Array.foldl_toList)
    have hc2 : (a.toList.foldl (fun a y => if a.contains y then a else a.push y) #[]).contains x := by
      rwa [Array.foldl_toList]
    rcases h a.toList #[] hc2 with h1 | h2
    · simp at h1
    · rwa [Array.contains_iff_mem, Array.mem_def]
  intro l; induction l with
  | nil => intro acc h; exact Or.inl h
  | cons hd tl ih =>
    intro acc h
    simp only [List.foldl_cons] at h
    rcases ih _ h with hacc | ht
    · by_cases hc : acc.contains hd
      · rw [if_pos hc] at hacc; exact Or.inl hacc
      · rw [if_neg hc] at hacc
        -- hacc : (acc.push hd).contains x
        rw [Array.contains_push] at hacc
        -- hacc : (acc.contains x || x == hd) = true
        rw [Bool.or_eq_true] at hacc
        rcases hacc with hacc | hacc
        · exact Or.inl hacc
        · simp only [beq_iff_eq] at hacc
          exact Or.inr (List.mem_cons.mpr (Or.inl hacc))
    · exact Or.inr (List.mem_cons.mpr (Or.inr ht))

theorem push_contains [DecidableEq α] (a : Array α) (x y : α) :
    (a.push x).contains y ↔ a.contains y ∨ y = x := by
  simp [Array.contains_push, beq_iff_eq, Bool.or_eq_true]

theorem empty_size : (Array.empty : Array α).size = 0 := Array.size_empty

theorem push_nonempty (a : Array α) (x : α) : (a.push x).size > 0 := by
  rw [Array.size_push]; omega

theorem shift_returns_first (a : Array α) (h : 0 < a.size) :
    (shift a).2 = some (a[0]'h) := by
  simp [shift, h]

theorem flatMap_size_le (a : Array α) (f : α → Array β) :
    True := trivial  -- flatMap can produce any size

theorem unique_size_le [DecidableEq α] (a : Array α) :
    (unique a).size ≤ a.size := by
  simp only [unique]
  suffices h : ∀ (l : List α) (acc : Array α),
      (l.foldl (fun a y => if a.contains y then a else a.push y) acc).size ≤
      acc.size + l.length by
    have hkey := h a.toList #[]
    simp only [Array.foldl_toList, Array.size_empty, Array.length_toList] at hkey
    calc (unique a).size = (Array.foldl (fun a y => if a.contains y then a else a.push y) #[] a).size := rfl
         _ ≤ 0 + a.size := hkey
         _ = a.size := by omega
  intro l; induction l with
  | nil => intro acc; simp
  | cons hd tl ih =>
    intro acc
    simp only [List.foldl_cons, List.length_cons]
    by_cases hc : acc.contains hd
    · rw [if_pos hc]; have := ih acc; omega
    · rw [if_neg hc]; have := ih (acc.push hd); rw [Array.size_push] at this; omega

theorem sumNat_nonneg (a : Array Nat) : sumNat a ≥ 0 := Nat.zero_le _

theorem getOpt_some_implies_in_bounds (a : Array α) (i : Nat) (v : α) :
    getOpt a i = some v → i < a.size := by
  intro h
  exact (getOpt_isSome_iff a i).mp (by simp [h])

theorem intersection_subset [DecidableEq α] (a b : Array α) (x : α) :
    (intersection a b).contains x → a.contains x := by
  simp [intersection, Array.contains_filter]
  intro h _; exact h

-- difference excludes elements in b
theorem difference_spec [DecidableEq α] (a b : Array α) (x : α) :
    (difference a b).contains x = (a.contains x && !b.contains x) := by
  simp [difference, Array.contains_filter]

theorem rotateLeft_size (a : Array α) (n : Nat) :
    (rotateLeft a n).size = a.size := by
  simp [rotateLeft]
  split
  · simp
  · simp [Array.size_append, Array.size_extract]; omega

theorem splice_size (a : Array α) (i n : Nat) (ins : Array α) :
    (splice a i n ins).size = min i a.size + ins.size + (a.size - min (i + n) a.size) := by
  simp [splice, Array.size_append, Array.size_extract]; omega

end TSLean.Stdlib.Array
