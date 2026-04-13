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

end TSLean
