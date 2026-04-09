-- TSLean.Runtime.Basic
-- Core type definitions for the TypeScript → Lean 4 runtime

namespace TSLean

inductive TSValue where
  | tsNull    : TSValue
  | tsUndef   : TSValue
  | tsBool    : Bool → TSValue
  | tsNum     : Float → TSValue
  | tsStr     : String → TSValue
  | tsArray   : Array TSValue → TSValue
  | tsObject  : List (String × TSValue) → TSValue
  deriving Repr

inductive TSError where
  | typeError     : String → TSError
  | rangeError    : String → TSError
  | referenceError: String → TSError
  | syntaxError   : String → TSError
  | networkError  : String → TSError
  | timeoutError  : String → TSError
  | customError   : String → String → TSError
  deriving Repr, BEq

def TSError.message : TSError → String
  | typeError m      => "TypeError: " ++ m
  | rangeError m     => "RangeError: " ++ m
  | referenceError m => "ReferenceError: " ++ m
  | syntaxError m    => "SyntaxError: " ++ m
  | networkError m   => "NetworkError: " ++ m
  | timeoutError m   => "TimeoutError: " ++ m
  | customError n m  => n ++ ": " ++ m

def TSError.name : TSError → String
  | typeError _      => "TypeError"
  | rangeError _     => "RangeError"
  | referenceError _ => "ReferenceError"
  | syntaxError _    => "SyntaxError"
  | networkError _   => "NetworkError"
  | timeoutError _   => "TimeoutError"
  | customError n _  => n

abbrev TSUnit   := Unit
abbrev TSOption := Option
abbrev TSResult := Except TSError

theorem TSError.message_nonempty (e : TSError) : e.message.length > 0 := by
  cases e <;> simp only [TSError.message, String.length_append] <;>
  (first
    | (have : ("TypeError: " : String).length = 11 := rfl; omega)
    | (have : ("RangeError: " : String).length = 12 := rfl; omega)
    | (have : ("ReferenceError: " : String).length = 16 := rfl; omega)
    | (have : ("SyntaxError: " : String).length = 13 := rfl; omega)
    | (have : ("NetworkError: " : String).length = 14 := rfl; omega)
    | (have : ("TimeoutError: " : String).length = 14 := rfl; omega)
    | (have : (": " : String).length = 2 := rfl; omega))

-- For customError, the name is user-supplied and may be empty, so we restrict to builtin errors.
theorem TSError.name_nonempty_builtin (e : TSError) (h : ∀ n m, e ≠ TSError.customError n m) :
    e.name.length > 0 := by
  cases e with
  | typeError _ => simp only [TSError.name]; native_decide
  | rangeError _ => simp only [TSError.name]; native_decide
  | referenceError _ => simp only [TSError.name]; native_decide
  | syntaxError _ => simp only [TSError.name]; native_decide
  | networkError _ => simp only [TSError.name]; native_decide
  | timeoutError _ => simp only [TSError.name]; native_decide
  | customError n m => exact absurd rfl (h n m)

theorem TSValue.tsStr_injective : Function.Injective TSValue.tsStr :=
  fun a b h => TSValue.tsStr.inj h

theorem TSValue.null_ne_undef : TSValue.tsNull ≠ TSValue.tsUndef := by intro h; cases h

theorem TSResult.bind_assoc {α β γ : Type} (r : TSResult α) (f : α → TSResult β) (g : β → TSResult γ) :
    (r >>= f) >>= g = r >>= fun x => f x >>= g := by cases r <;> simp [bind, Except.bind]

theorem TSResult.pure_bind {α β : Type} (a : α) (f : α → TSResult β) :
    (pure a : TSResult α) >>= f = f a := by simp [bind, Except.bind, pure, Except.pure]

theorem TSResult.bind_pure {α : Type} (r : TSResult α) :
    r >>= (pure : α → TSResult α) = r := by cases r <;> simp [bind, Except.bind, pure, Except.pure]

/-! ## Serialization -/

/-- Serialize any value with a ToString instance to a String (models JSON.stringify). -/
def serialize [ToString α] (x : α) : String := toString x

/-- Deserialize a String. The default implementation is the identity (lossless for strings).
    Specific types can override via the Serializable class. -/
def deserialize (s : String) : Option String := some s

/-- Try to deserialize to a Nat. -/
def deserializeNat (s : String) : Option Nat := s.toNat?

/-- Try to deserialize to an Int. -/
def deserializeInt (s : String) : Option Int := s.toInt?

/-! ## Float comparison -/

instance : Ord Float where
  compare a b :=
    if a < b then .lt
    else if a > b then .gt
    else .eq

def Float.blt (a b : Float) : Bool := a < b
def Float.ble (a b : Float) : Bool := a <= b
def Float.bge (a b : Float) : Bool := a >= b
def Float.bgt (a b : Float) : Bool := a > b

/-- Clamp a Float to a range. -/
def Float.clamp (x lo hi : Float) : Float :=
  if x < lo then lo else if x > hi then hi else x

/-! ## ExceptT / error handling helpers -/

/-- Convenience: construct a TSError and throw it. -/
def throwError [MonadExcept TSError m] (msg : String) : m α :=
  throw (TSError.typeError msg)

/-- Convenience: try an action, catch TSError, return default. -/
def tryCatchDefault [Monad m] [MonadExcept TSError m] (action : m α) (default : α) : m α :=
  tryCatch action (fun _ => pure default)

-- String helpers matching JS APIs (for transpiler codegen)
def String.includes (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- Get a character by index, returning a default if out of bounds. -/
def String.getD' (s : String) (i : Nat) (default : Char := '\x00') : Char :=
  if i < s.length then String.Pos.Raw.get s ⟨i⟩ else default

/-- Get a character by index, panicking if out of bounds. -/
def String.get!' (s : String) (i : Nat) : Char :=
  String.getD' s i '\x00'

/-- Set a character at index (returns new string). -/
def String.set!' (s : String) (i : Nat) (c : Char) : String :=
  if i >= s.length then s
  else
    let before := String.Pos.Raw.extract s ⟨0⟩ ⟨i⟩
    let after := String.Pos.Raw.extract s ⟨i + 1⟩ ⟨s.length⟩
    before ++ String.singleton c ++ after

/-! ## TSValue — dynamic type for any/unknown ─────────────────────────────── -/

/-- Opaque representation of a dynamically-typed TypeScript value.
    Used when the transpiler cannot resolve a static type (TS `any`/`unknown`).
    Backed by `String` — values are serialised as JSON strings at the boundary. -/
abbrev TSAny := String

instance : Inhabited TSAny := ⟨""⟩
instance : BEq TSAny := inferInstance
instance : Repr TSAny := inferInstance
instance : ToString TSAny := inferInstance

/-- Legacy alias — the codegen now emits `TSAny` for `any`/`unknown`. -/
abbrev Any := TSAny

instance : Inhabited TSValue := ⟨TSValue.tsNull⟩
instance : BEq TSValue where
  beq a b := match a, b with
    | .tsNull, .tsNull | .tsUndef, .tsUndef => true
    | .tsBool a, .tsBool b => a == b
    | .tsNum a, .tsNum b => a == b
    | .tsStr a, .tsStr b => a == b
    | _, _ => false
instance : ToString TSValue where
  toString v := match v with
    | .tsNull => "null"
    | .tsUndef => "undefined"
    | .tsBool b => toString b
    | .tsNum n => toString n
    | .tsStr s => s!"\"{s}\""
    | .tsArray _ => "[...]"
    | .tsObject _ => "{...}"

/-- Runtime type check (stub — always returns "object"). -/
def typeOf {α : Type} (_ : α) : String := "object"

end TSLean
