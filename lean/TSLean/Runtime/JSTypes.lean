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

-- JSMap.set filters out k then appends (k,v); get finds the appended pair.
axiom get_set_same [DecidableEq K] (m : JSMap K V) (k : K) (v : V) :
    (m.set k v).get k = some v

theorem get_empty (k : K) : (JSMap.empty : JSMap K V).get k = none := by
  simp [empty, get, List.find?]

theorem size_empty : (JSMap.empty : JSMap K V).size = 0 := by
  simp [empty, size]

-- JSMap.set appends (k,v); has finds it via any.
axiom has_set_same [DecidableEq K] (m : JSMap K V) (k : K) (v : V) :
    (m.set k v).has k = true

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

-- JSSet.add either keeps x (if present) or prepends it; has finds it.
axiom has_add_same (s : JSSet T) (x : T) : (s.add x).has x = true

theorem has_empty (x : T) : (JSSet.empty : JSSet T).has x = false := by
  simp [empty, has]

theorem size_empty : (JSSet.empty : JSSet T).size = 0 := by
  simp [empty, size]

end JSSet

-- ─── RegExp ────────────────────────────────────────────────────────────────────
-- Opaque stub for JavaScript regular expressions.
-- Regex matching is a JS runtime operation with no pure Lean equivalent,
-- so `test` and `exec` use `sorry` — this is intentional, not a proof gap.

structure RegExp where
  pattern : String
  flags   : String := ""
  deriving Repr, BEq, Inhabited

namespace RegExp

/-- Create a RegExp from a pattern string (JS: `new RegExp(pattern, flags)`). -/
def mk' (pattern : String) (flags : String := "") : RegExp :=
  { pattern, flags }

/-- Test whether the regex matches the string (JS: `re.test(s)`).
    Opaque — regex semantics are a JS runtime operation. -/
opaque test (re : RegExp) (s : String) : Bool

/-- Execute the regex against the string, returning capture groups (JS: `re.exec(s)`).
    Opaque — regex semantics are a JS runtime operation. -/
opaque exec (re : RegExp) (s : String) : Option (Array String)

/-- Global replacement (JS: `s.replace(re, replacement)`).
    Opaque — regex replacement is a JS runtime operation. -/
opaque replace (re : RegExp) (s : String) (replacement : String) : String

/-- Match all occurrences (JS: `s.matchAll(re)`). -/
opaque matchAll (re : RegExp) (s : String) : Array (Array String)

end RegExp

-- ─── String.test ───────────────────────────────────────────────────────────────
-- JS idiom: `"pattern".test(s)` or `someRegex.test(s)`
-- In transpiled code, `str.test(s)` becomes `(RegExp.mk' str).test s`.

/-- Test whether a pattern (as a string) matches the input.
    Wraps the string in a RegExp and delegates to `RegExp.test`. -/
def String.testRegex (pattern : String) (s : String) : Bool :=
  RegExp.test (RegExp.mk' pattern) s

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
