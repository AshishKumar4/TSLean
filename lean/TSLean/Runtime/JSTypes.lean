-- TSLean.Runtime.JSTypes
-- Additional JavaScript/TypeScript built-in types needed for self-hosting.
-- Models Map, Set, RegExp, JSON, Date, console, Error at the level needed
-- for the transpiled self-hosting code to type-check.

namespace TSLean.JSTypes

-- ─── Map<K, V> ─────────────────────────────────────────────────────────────────
-- Models the JavaScript Map with key-value pairs stored as a list.

structure JSMap (K V : Type) [BEq K] where
  entries : List (K × V) := []
  deriving Repr, Inhabited

namespace JSMap

variable {K V : Type} [BEq K]

def empty : JSMap K V := {}

def get (m : JSMap K V) (k : K) : Option V :=
  m.entries.find? (fun (k', _) => k' == k) |>.map Prod.snd

def set (m : JSMap K V) (k : K) (v : V) : JSMap K V :=
  { entries := m.entries.filter (fun (k', _) => !(k' == k)) ++ [(k, v)] }

def has (m : JSMap K V) (k : K) : Bool :=
  m.entries.any (fun (k', _) => k' == k)

def delete (m : JSMap K V) (k : K) : JSMap K V :=
  { entries := m.entries.filter (fun (k', _) => !(k' == k)) }

def size (m : JSMap K V) : Nat := m.entries.length

def keys (m : JSMap K V) : List K := m.entries.map Prod.fst

def values (m : JSMap K V) : List V := m.entries.map Prod.snd

def forEach (m : JSMap K V) (f : K → V → Unit) : Unit :=
  m.entries.foldl (fun _ (k, v) => f k v) ()

def clear (_ : JSMap K V) : JSMap K V := {}

-- ─── Map theorems ──────────────────────────────────────────────────────────────

theorem get_set_same [DecidableEq K] (m : JSMap K V) (k : K) (v : V) :
    (m.set k v).get k = some v := by
  simp [get, set, List.find?]
  sorry

theorem get_empty (k : K) : (JSMap.empty : JSMap K V).get k = none := by
  simp [empty, get, List.find?]

theorem size_empty : (JSMap.empty : JSMap K V).size = 0 := by
  simp [empty, size]

theorem has_set_same [DecidableEq K] (m : JSMap K V) (k : K) (v : V) :
    (m.set k v).has k = true := by
  simp [has, set]
  sorry

end JSMap

-- ─── Set<T> ────────────────────────────────────────────────────────────────────

structure JSSet (T : Type) [BEq T] where
  elems : List T := []
  deriving Repr, Inhabited

namespace JSSet

variable {T : Type} [BEq T]

def empty : JSSet T := {}

def add (s : JSSet T) (x : T) : JSSet T :=
  if s.elems.any (· == x) then s
  else { elems := x :: s.elems }

def has (s : JSSet T) (x : T) : Bool :=
  s.elems.any (· == x)

def delete (s : JSSet T) (x : T) : JSSet T :=
  { elems := s.elems.filter (· != x) }

def size (s : JSSet T) : Nat := s.elems.length

def toArray (s : JSSet T) : Array T := s.elems.toArray

def forEach (s : JSSet T) (f : T → Unit) : Unit :=
  s.elems.foldl (fun _ x => f x) ()

def clear (_ : JSSet T) : JSSet T := {}

-- ─── Set theorems ──────────────────────────────────────────────────────────────

theorem has_add_same (s : JSSet T) (x : T) : (s.add x).has x = true := by
  simp [has, add]
  sorry

theorem has_empty (x : T) : (JSSet.empty : JSSet T).has x = false := by
  simp [empty, has]

theorem size_empty : (JSSet.empty : JSSet T).size = 0 := by
  simp [empty, size]

end JSSet

-- ─── RegExp ────────────────────────────────────────────────────────────────────
-- Simplified regular expression stub — enough for the transpiled code to type-check.

structure RegExp where
  source : String
  flags  : String := ""
  deriving Repr, BEq, Inhabited

namespace RegExp

def test (_ : RegExp) (_ : String) : Bool := true  -- stub

def exec (_ : RegExp) (_ : String) : Option (Array String) := none  -- stub

end RegExp

-- ─── JSON ──────────────────────────────────────────────────────────────────────

namespace JSON
  def stringify (_ : String) : String := "{}"   -- stub
  def parse (_ : String) : String := ""         -- stub
end JSON

-- ─── Date ──────────────────────────────────────────────────────────────────────

namespace Date
  def now : IO Nat := pure 0  -- stub: returns Unix timestamp in ms
end Date

-- ─── console ───────────────────────────────────────────────────────────────────

namespace console
  def log (_ : String) : IO Unit := pure ()
  def error (_ : String) : IO Unit := pure ()
  def warn (_ : String) : IO Unit := pure ()
end console

-- ─── Error ─────────────────────────────────────────────────────────────────────

structure JSError where
  message : String
  name    : String := "Error"
  stack   : Option String := none
  deriving Repr, BEq, Inhabited

-- ─── process ───────────────────────────────────────────────────────────────────

namespace process
  def argv : Array String := #[]
  def exit (_ : Nat) : IO Unit := pure ()
  namespace env
    def get (_ : String) : Option String := none
  end env
end process

end TSLean.JSTypes
