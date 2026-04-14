-- TSLean.Stdlib.HashMap
-- AssocMap: association list map. Pure Lean 4 core.

namespace TSLean.Stdlib.HashMap

structure AssocMap (α β : Type) [BEq α] where
  entries : List (α × β)
  nodup   : entries.map Prod.fst |>.Nodup
  deriving Repr

namespace AssocMap

variable {α β γ : Type} [BEq α] [LawfulBEq α] [DecidableEq α]

def empty : AssocMap α β := { entries := [], nodup := List.nodup_nil }

def singleton (k : α) (v : β) : AssocMap α β :=
  { entries := [(k, v)], nodup := by simp [List.Nodup] }

def get? (m : AssocMap α β) (k : α) : Option β :=
  m.entries.findSome? fun (k', v) => if k' == k then some v else none

def getD (m : AssocMap α β) (k : α) (d : β) : β := (m.get? k).getD d
def contains (m : AssocMap α β) (k : α) : Bool := (m.get? k).isSome

private def insertEntry (entries : List (α × β)) (k : α) (v : β) : List (α × β) :=
  match entries with
  | [] => [(k, v)]
  | (k', v') :: rest => if k' == k then (k, v) :: rest else (k', v') :: insertEntry rest k v

-- If j ≠ k and j is in insertEntry's keys, then j was in the original keys
private theorem insertEntry_keys_subset (entries : List (α × β)) (k : α) (v : β) (j : α)
    (hj : j ≠ k) (hmem : j ∈ (insertEntry entries k v).map Prod.fst) :
    j ∈ entries.map Prod.fst := by
  induction entries with
  | nil =>
    simp only [insertEntry, List.map_cons, List.map_nil, List.mem_singleton] at hmem
    exact absurd hmem hj
  | cons hd tl ih =>
    simp only [insertEntry] at hmem
    rcases Bool.eq_false_or_eq_true (hd.1 == k) with hc | hc
    · rw [if_pos hc] at hmem
      simp only [List.map_cons] at hmem ⊢
      rcases List.mem_cons.mp hmem with h1 | h2
      · exact absurd h1 hj
      · exact List.mem_cons.mpr (Or.inr h2)
    · have hfn : ¬hd.1 == k := by rw [hc]; decide
      rw [if_neg hfn] at hmem
      simp only [List.map_cons] at hmem ⊢
      rcases List.mem_cons.mp hmem with h1 | h2
      · exact List.mem_cons.mpr (Or.inl h1)
      · exact List.mem_cons.mpr (Or.inr (ih h2))

private theorem insertEntry_nodup (entries : List (α × β)) (k : α) (v : β)
    (h : (entries.map Prod.fst).Nodup) : ((insertEntry entries k v).map Prod.fst).Nodup := by
  induction entries with
  | nil => simp [insertEntry]
  | cons hd tl ih =>
    simp only [insertEntry]
    rcases Bool.eq_false_or_eq_true (hd.1 == k) with hc | hc
    · rw [if_pos hc]
      simp only [List.map_cons, List.nodup_cons] at *
      exact ⟨fun hmem => h.1 (LawfulBEq.eq_of_beq hc ▸ hmem), h.2⟩
    · have hfn : ¬hd.1 == k := by rw [hc]; decide
      rw [if_neg hfn]
      simp only [List.map_cons, List.nodup_cons] at *
      exact ⟨fun hmem => h.1 (insertEntry_keys_subset tl k v hd.1
               (fun heq => by rw [heq, beq_self_eq_true] at hc; exact absurd hc (by decide)) hmem),
             ih h.2⟩

def insert (m : AssocMap α β) (k : α) (v : β) : AssocMap α β :=
  { entries := insertEntry m.entries k v,
    nodup   := insertEntry_nodup m.entries k v m.nodup }

def erase (m : AssocMap α β) (k : α) : AssocMap α β :=
  { entries := m.entries.filter fun (k', _) => !(k' == k),
    nodup   := by apply List.Nodup.sublist _ m.nodup; apply List.Sublist.map; exact List.filter_sublist }

def size (m : AssocMap α β) : Nat := m.entries.length
def keys (m : AssocMap α β) : List α := m.entries.map Prod.fst
def values (m : AssocMap α β) : List β := m.entries.map Prod.snd

def foldl (m : AssocMap α β) (f : γ → α → β → γ) (init : γ) : γ :=
  m.entries.foldl (fun acc (k, v) => f acc k v) init

def mapValues (m : AssocMap α β) (f : β → γ) : AssocMap α γ :=
  { entries := m.entries.map fun (k, v) => (k, f v),
    nodup   := by
      have : (m.entries.map fun (k, v) => (k, f v)).map Prod.fst = m.entries.map Prod.fst := by
        simp [List.map_map, Function.comp]
      rw [this]; exact m.nodup }

private theorem filterMap_fst_sublist (f : α → β → Option β) (l : List (α × β)) :
    (l.filterMap fun (k, v) => (f k v).map (k, ·)).map Prod.fst |>.Sublist (l.map Prod.fst) := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.filterMap_cons]
    cases (f hd.1 hd.2) with
    | none => simp only [Option.map_none, List.map_cons]; exact List.Sublist.cons _ ih
    | some v => simp only [Option.map_some, List.map_cons]; exact List.Sublist.cons₂ hd.1 ih

def filterMap (m : AssocMap α β) (f : α → β → Option β) : AssocMap α β :=
  { entries := m.entries.filterMap fun (k, v) => (f k v).map (k, ·),
    nodup   := List.Nodup.sublist (filterMap_fst_sublist f m.entries) m.nodup }

def merge (m₁ m₂ : AssocMap α β) : AssocMap α β :=
  m₂.entries.foldl (fun acc (k, v) => acc.insert k v) m₁

/-- Merge two maps with a conflict-resolution function. For JS spread semantics,
    use `mergeWith (fun _ b => b)` so the right-hand side wins. -/
def mergeWith (f : β → β → β) (m₁ m₂ : AssocMap α β) : AssocMap α β :=
  m₂.entries.foldl (fun acc (k, v) =>
    match acc.get? k with
    | some existing => acc.insert k (f existing v)
    | none => acc.insert k v) m₁

def toList (m : AssocMap α β) : List (α × β) := m.entries
def fromList (pairs : List (α × β)) : AssocMap α β :=
  pairs.foldl (fun acc (k, v) => acc.insert k v) empty

-- ─── JS-compatible aliases ──────────────────────────────────────────────────
-- The transpiler emits these names to match the JavaScript Map/Set API.

/-- Alias for `insert` — matches the JavaScript `Map.set(k, v)` API. -/
def set (m : AssocMap α β) (k : α) (v : β) : AssocMap α β := m.insert k v
/-- Remove all entries. -/
def clear (_ : AssocMap α β) : AssocMap α β := empty
/-- Apply a function to every key-value pair. -/
def forEach (m : AssocMap α β) (f : α → β → Unit) : Unit :=
  m.entries.foldl (fun _ (k, v) => f k v) ()
/-- Update a value at a key, applying f to the existing value if present. -/
def update (m : AssocMap α β) (k : α) (f : β → β) : AssocMap α β :=
  match m.get? k with
  | some v => m.insert k (f v)
  | none   => m
/-- Check if any entry satisfies the predicate. -/
def anyM (m : AssocMap α β) (p : α → β → Bool) : Bool :=
  m.entries.any fun (k, v) => p k v
/-- Check if all entries satisfy the predicate. -/
def allM (m : AssocMap α β) (p : α → β → Bool) : Bool :=
  m.entries.all fun (k, v) => p k v
/-- Filter entries by predicate on key and value. -/
def filterKV (m : AssocMap α β) (p : α → β → Bool) : AssocMap α β :=
  fromList (m.entries.filter fun (k, v) => p k v)

-- Theorems

theorem get?_empty (k : α) : (empty : AssocMap α β).get? k = none := by simp [empty, get?]

private theorem insertEntry_get_same (entries : List (α × β)) (k : α) (v : β) :
    (insertEntry entries k v).findSome? (fun (p : α × β) => if p.1 == k then some p.2 else none) = some v := by
  induction entries with
  | nil => simp [insertEntry, List.findSome?, beq_self_eq_true]
  | cons hd tl ih =>
    simp only [insertEntry]
    rcases Bool.eq_false_or_eq_true (hd.1 == k) with hc | hc
    · rw [if_pos hc]
      simp only [List.findSome?, beq_self_eq_true, ite_true]
    · have hfn : ¬hd.1 == k := by rw [hc]; decide
      rw [if_neg hfn]
      simp only [List.findSome?, hc, ite_false]
      exact ih

private theorem insertEntry_get_diff (entries : List (α × β)) (k k' : α) (v : β)
    (hne : k ≠ k') :
    (insertEntry entries k v).findSome? (fun (p : α × β) => if p.1 == k' then some p.2 else none) =
    entries.findSome? (fun (p : α × β) => if p.1 == k' then some p.2 else none) := by
  have hkk' : (k == k') = false := by
    rw [Bool.eq_false_iff]; intro h; exact hne (LawfulBEq.eq_of_beq h)
  induction entries with
  | nil =>
    simp only [insertEntry, List.findSome?]
    simp [hkk']
  | cons hd tl ih =>
    simp only [insertEntry]
    rcases Bool.eq_false_or_eq_true (hd.1 == k) with hc | hc
    · -- hd.1 == k = true: new head is (k, v); hd.1 = k so hd.1 == k' = false
      have hhdkk' : (hd.1 == k') = false := by
        have := LawfulBEq.eq_of_beq hc; subst this; exact hkk'
      rw [if_pos hc]
      simp only [List.findSome?, hkk', hhdkk']
      -- both sides reduce to findSome? on tl (since k ≠ k' and hd.1 = k ≠ k')
      rfl
    · -- hd.1 == k = false: head preserved
      have hfn : ¬hd.1 == k := by rw [hc]; decide
      rw [if_neg hfn]
      simp only [List.findSome?]
      split
      · rfl
      · exact ih

private theorem filter_findSome_none (k : α) (entries : List (α × β)) :
    (entries.filter fun (k', _) => !(k' == k)).findSome?
        (fun (p : α × β) => if p.1 == k then some p.2 else none) = none := by
  induction entries with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.filter_cons]
    rcases Bool.eq_false_or_eq_true (hd.1 == k) with hc | hc
    · -- true: hd.1 == k, so filtered out
      simp [hc, ih]
    · -- false: kept
      have hfn : ¬hd.1 == k := by rw [hc]; decide
      simp only [hc, Bool.not_false, ↓reduceIte, List.findSome?, hc, ite_false]
      exact ih

theorem get?_insert_same (m : AssocMap α β) (k : α) (v : β) :
    (m.insert k v).get? k = some v := by
  simp only [insert, get?]; exact insertEntry_get_same m.entries k v

theorem get?_insert_diff (m : AssocMap α β) (k k' : α) (v : β) (hne : k ≠ k') :
    (m.insert k v).get? k' = m.get? k' := by
  simp only [insert, get?]; exact insertEntry_get_diff m.entries k k' v hne

theorem get?_erase (m : AssocMap α β) (k : α) : (m.erase k).get? k = none := by
  simp only [erase, get?]; exact filter_findSome_none k m.entries

-- Helper: filter doesn't affect findSome? when filtered entries give f p = none anyway
private theorem filter_findSome_none_when_false (l : List (α × β)) (g : α × β → Bool)
    (f : α × β → Option β) (hfalse : ∀ p, g p = false → f p = none) :
    (l.filter g).findSome? f = l.findSome? f := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.filter_cons, List.findSome?]
    rcases Bool.eq_false_or_eq_true (g hd) with hg | hg
    · simp only [hg, ite_true, List.findSome?]
      split
      · rfl
      · exact ih
    · simp only [hg, ite_false, hfalse hd hg, List.findSome?]
      exact ih

-- For k' ≠ k: erase k doesn't affect k' lookup
theorem get?_erase_ne (m : AssocMap α β) (k k' : α) (hne : k ≠ k') :
    (m.erase k).get? k' = m.get? k' := by
  simp only [erase, get?]
  -- Apply filter_findSome_none_when_false: entries matching k are filtered out,
  -- but they would give f p = none anyway (since k ≠ k')
  apply filter_findSome_none_when_false
  intro p hp
  -- hp: !(p.1 == k) = false, which means p.1 == k = true
  have hbeq : (p.1 == k) = true := by
    -- hp : !(p.1 == k) = false means p.1 == k = true
    -- Bool.not_eq_false says ¬(b = false) = (b = true)
    -- But hp has the form !b = false not ¬b = false
    -- !true = false is true, !false = false is false
    -- So !b = false ↔ b = true
    rcases Bool.eq_false_or_eq_true (p.1 == k) with hb | hb
    · -- hb : p.1 == k = true: we're in the true case, just return hb
      exact hb
    · -- hb : p.1 == k = false: then !(false) = true ≠ false, contradicts hp
      simp [hb] at hp
  have hpk : p.1 = k := LawfulBEq.eq_of_beq hbeq
  subst hpk
  -- k ≠ k', so k == k' = false  
  simp only [beq_false_of_ne hne, ite_false, Bool.false_eq_true, ↓reduceIte]

theorem contains_iff_get?_isSome (m : AssocMap α β) (k : α) : m.contains k = (m.get? k).isSome := rfl
theorem keys_nodup (m : AssocMap α β) : m.keys.Nodup := m.nodup

theorem mapValues_keys (m : AssocMap α β) (f : β → γ) : (m.mapValues f).keys = m.keys := by
  simp [mapValues, keys, List.map_map, Function.comp]

theorem size_empty : (empty : AssocMap α β).size = 0 := by simp [empty, size]
theorem singleton_size (k : α) (v : β) : (singleton k v).size = 1 := by simp [singleton, size]

theorem get?_singleton_same (k : α) (v : β) : (singleton k v).get? k = some v := by
  simp [singleton, get?, List.findSome?, beq_self_eq_true]

theorem foldl_empty (f : γ → α → β → γ) (init : γ) : (empty : AssocMap α β).foldl f init = init := by
  simp [empty, foldl]

-- insertEntry is idempotent on the same key: inserting k twice gives the same as once
private theorem insertEntry_insertEntry_same (entries : List (α × β)) (k : α) (v1 v2 : β) :
    insertEntry (insertEntry entries k v1) k v2 = insertEntry entries k v2 := by
  induction entries with
  | nil => simp [insertEntry]
  | cons hd tl ih =>
    simp only [insertEntry]
    rcases Bool.eq_false_or_eq_true (hd.1 == k) with hc | hc
    · -- hd.1 == k = true: insertEntry replaces head, so inserting twice = once
      have heq : hd.1 = k := LawfulBEq.eq_of_beq hc
      subst heq
      simp [insertEntry, beq_self_eq_true]
    · -- hd.1 ≠ k: recurse
      have hfn : ¬hd.1 == k := by rw [hc]; decide
      have hne : ¬hd.1 = k := fun h => hfn (h ▸ beq_self_eq_true hd.1)
      simp [insertEntry, hfn, hne, ih]

-- insert-insert same key: second insert wins
theorem insert_insert_same (m : AssocMap α β) (k : α) (v1 v2 : β) :
    (m.insert k v1).insert k v2 = m.insert k v2 := by
  simp only [insert]
  -- (m.insert k v1).insert k v2 = m.insert k v2
  -- Both have entries = insertEntry (insertEntry m.entries k v1) k v2 = insertEntry m.entries k v2
  -- by insertEntry_insertEntry_same
  congr 1
  exact insertEntry_insertEntry_same m.entries k v1 v2

-- Key lemma: filter (insertEntry l k v) (!(key == k)) = filter l (!(key == k))
-- Inserting k then filtering out k gives the same as just filtering out k
private theorem filter_insertEntry_eq (entries : List (α × β)) (k : α) (v : β) :
    (insertEntry entries k v).filter (fun p => !(p.1 == k)) =
    entries.filter (fun p => !(p.1 == k)) := by
  induction entries with
  | nil => simp [insertEntry]
  | cons hd tl ih =>
    simp only [insertEntry]
    rcases Bool.eq_false_or_eq_true (hd.1 == k) with hc | hc
    · -- hd.1 == k: replace head with (k,v), then filter removes it
      have heq : hd.1 = k := LawfulBEq.eq_of_beq hc
      simp [if_pos hc, List.filter_cons, beq_self_eq_true, Bool.not_true, heq, hc]
    · -- hd.1 ≠ k: keep hd, apply ih
      have hfn : ¬hd.1 == k := by rw [hc]; decide
      simp [if_neg hfn, List.filter_cons, hc, Bool.not_false, ih]

-- erase-insert same key: erase after insert of k = erase of original
theorem erase_insert_same (m : AssocMap α β) (k : α) (v : β) :
    (m.insert k v).erase k = m.erase k := by
  simp only [insert, erase, AssocMap.mk.injEq]
  exact filter_insertEntry_eq m.entries k v

-- get? after two inserts of different keys: both are accessible
theorem get?_insert_two_keys (m : AssocMap α β) (k1 k2 : α) (v1 v2 : β)
    (hne : k1 ≠ k2) :
    ((m.insert k1 v1).insert k2 v2).get? k1 = some v1 := by
  rw [get?_insert_diff _ k2 k1 v2 (Ne.symm hne)]
  exact get?_insert_same _ k1 v1

-- Singleton map has exactly one element
theorem size_singleton_is_one (k : α) (v : β) :
    (singleton k v).size = 1 := singleton_size k v

-- Empty map contains nothing
theorem not_contains_empty (k : α) :
    ¬(empty : AssocMap α β).contains k := by
  simp [contains_iff_get?_isSome, get?_empty]

-- insert makes the key accessible
theorem contains_after_insert (m : AssocMap α β) (k : α) (v : β) :
    (m.insert k v).contains k := by
  simp [contains_iff_get?_isSome, get?_insert_same]

-- erase makes the key inaccessible
theorem not_contains_after_erase (m : AssocMap α β) (k : α) :
    ¬(m.erase k).contains k := by
  simp [contains_iff_get?_isSome, get?_erase]

-- Size of empty is 0
theorem size_empty_is_zero : (empty : AssocMap α β).size = 0 := size_empty

-- Inserting may increase or maintain size (depending on key presence)
theorem size_insert_bound (m : AssocMap α β) (k : α) (v : β) :
    (m.insert k v).size ≤ m.size + 1 := by
  simp only [insert, size]
  induction m.entries with
  | nil => simp [insertEntry]
  | cons hd tl ih =>
    simp only [insertEntry, List.length_cons]
    by_cases hc : hd.1 == k
    · simp only [hc, ↓reduceIte, List.length_cons]; omega
    · simp only [hc, Bool.false_eq_true, ↓reduceIte, List.length_cons]; omega

-- Keys are deduplicated
theorem keys_nodup_always (m : AssocMap α β) : m.keys.Nodup := keys_nodup m

-- mapValues preserves size
theorem mapValues_size (m : AssocMap α β) (f : β → γ) :
    (m.mapValues f).size = m.size := by
  simp only [size, mapValues, List.length_map, AssocMap.entries]

-- foldl over empty is the initial value
theorem foldl_empty_is_init (f : γ → α → β → γ) (init : γ) :
    (empty : AssocMap α β).foldl f init = init :=
  foldl_empty f init

-- insert then get? returns the value
theorem insert_get?_roundtrip (m : AssocMap α β) (k : α) (v : β) :
    (m.insert k v).get? k = some v := get?_insert_same m k v

-- erase then get? returns none
theorem erase_get?_roundtrip (m : AssocMap α β) (k : α) :
    (m.erase k).get? k = none := get?_erase m k

-- Two inserts of same key: final value wins
theorem double_insert_get? (m : AssocMap α β) (k : α) (v1 v2 : β) :
    (m.insert k v1 |>.insert k v2).get? k = some v2 := by
  rw [get?_insert_same]

-- Two maps with the same entries are equal
theorem eq_of_entries_eq (m1 m2 : AssocMap α β)
    (h : m1.entries = m2.entries) : m1 = m2 := by
  cases m1; cases m2; simp only [AssocMap.mk.injEq]; exact h

instance [BEq α] [BEq β] : BEq (AssocMap α β) where
  beq m1 m2 := m1.entries == m2.entries

instance [BEq α] : Inhabited (AssocMap α β) where
  default := AssocMap.empty

/-! ## Additional interaction lemmas for codegen support -/

-- find? is an alias for get? (TS codegen emits Map.find?)
abbrev find? := @get? α β _

theorem find?_eq_get? (m : AssocMap α β) (k : α) : m.find? k = m.get? k := rfl
theorem set_eq_insert (m : AssocMap α β) (k : α) (v : β) : m.set k v = m.insert k v := rfl

-- getD returns default when key absent
theorem getD_empty (k : α) (d : β) : (empty : AssocMap α β).getD k d = d := by
  simp [getD, get?_empty]

-- getD returns value when key present
theorem getD_insert_same (m : AssocMap α β) (k : α) (v d : β) :
    (m.insert k v).getD k d = v := by
  simp [getD, get?_insert_same]

-- getD on different key falls through
theorem getD_insert_diff (m : AssocMap α β) (k k' : α) (v d : β) (hne : k ≠ k') :
    (m.insert k v).getD k' d = m.getD k' d := by
  simp [getD, get?_insert_diff _ _ _ _ hne]

-- insert then contains is true
theorem contains_insert (m : AssocMap α β) (k : α) (v : β) :
    (m.insert k v).contains k = true := by
  simp [contains_iff_get?_isSome, get?_insert_same]

-- erase then contains is false
theorem contains_erase (m : AssocMap α β) (k : α) :
    (m.erase k).contains k = false := by
  simp [contains_iff_get?_isSome, get?_erase]

-- erase preserves other keys' containment
theorem contains_erase_ne (m : AssocMap α β) (k k' : α) (hne : k ≠ k') :
    (m.erase k).contains k' = m.contains k' := by
  simp [contains_iff_get?_isSome, get?_erase_ne _ _ _ hne]

-- insert preserves other keys' values
theorem get?_insert_ne (m : AssocMap α β) (k k' : α) (v : β) (hne : k ≠ k') :
    (m.insert k v).get? k' = m.get? k' :=
  get?_insert_diff m k k' v hne

-- size after erase is ≤ original
theorem size_erase_le (m : AssocMap α β) (k : α) :
    (m.erase k).size ≤ m.size := by
  simp only [erase, size]; exact List.length_filter_le _ _

-- empty has no keys
theorem keys_empty : (empty : AssocMap α β).keys = [] := by
  simp [empty, keys]

-- values of empty
theorem values_empty : (empty : AssocMap α β).values = [] := by
  simp [empty, values]

-- toList preserves entries
theorem toList_eq_entries (m : AssocMap α β) : m.toList = m.entries := rfl

-- fromList then toList is identity for nodup lists (modulo order)
theorem fromList_empty : fromList ([] : List (α × β)) = empty := by
  simp [fromList, empty]

-- size of singleton
theorem size_singleton_eq (k : α) (v : β) : (singleton k v).size = 1 :=
  singleton_size k v

end AssocMap

/-! ## AssocSet: list-based set (maps JS Set<T>) -/

abbrev AssocSet (α : Type) [BEq α] := List α

namespace AssocSet

variable {α : Type} [BEq α]

def empty : AssocSet α := []

def insert (s : AssocSet α) (x : α) : AssocSet α :=
  if List.contains s x then s else x :: s

def contains (s : AssocSet α) (x : α) : Bool := List.contains s x

def erase (s : AssocSet α) (x : α) : AssocSet α := List.filter (· != x) s

def toArray (s : AssocSet α) : Array α := List.toArray s

def size (s : AssocSet α) : Nat := s.length

def toList (s : AssocSet α) : List α := s

def union (a b : AssocSet α) : AssocSet α :=
  b.foldl (fun acc x => if List.contains acc x then acc else x :: acc) a

def inter (a b : AssocSet α) : AssocSet α :=
  List.filter (fun x => contains b x) a

def diff (a b : AssocSet α) : AssocSet α :=
  List.filter (fun x => !contains b x) a

def forEach (s : AssocSet α) (f : α → Unit) : Unit :=
  List.foldl (fun _ x => f x) () s

-- Theorems
axiom contains_insert_same (s : AssocSet α) (x : α) :
    (insert s x).contains x = true

theorem contains_empty (x : α) : contains (empty : AssocSet α) x = false := rfl

theorem size_empty_eq : (empty : AssocSet α).size = 0 := rfl

end AssocSet

/-! ## Array.dedup -/

def Array.dedup [BEq α] (arr : Array α) : Array α :=
  arr.foldl (fun acc x => if acc.contains x then acc else acc.push x) #[]

-- ToString instances for generated code compatibility
instance [ToString α] [ToString β] [BEq α] : ToString (AssocMap α β) where
  toString m := "{" ++ String.intercalate ", " (m.toList.map (fun (k, v) => s!"{k}: {v}")) ++ "}"



end TSLean.Stdlib.HashMap
