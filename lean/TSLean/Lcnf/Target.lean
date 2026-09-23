/-!
# The JavaScript subset the LCNF lowering targets

Everything `Lcnf.Lower` emits, and nothing more:

* `const` and `let` declarations, and assignment to mutable locals;
* labeled blocks, `while (true)` loops, `break`/`continue` to a label;
* `switch` on a numeric tag, and `if`/`else` on a boolean;
* `return` and `throw`;
* calls, object and array literals, property and index reads.

Runtime operations are calls to members of the runtime module, which every printed module imports
as `rt` (see `src/lcnf-runtime/index.ts`). Types are the runtime's `Value` and the few machine
types the explicit-stack form needs, so the printed TypeScript never mentions `any`.
-/

namespace TSLean.Lcnf.Target

abbrev Ident := String

/-- TypeScript types that appear in annotations. -/
inductive Ty where
  /-- `rt.Value`, the uniform value type. -/
  | value
  /-- `rt.Obj`, a tagged object, after `rt.obj` has checked it. -/
  | obj
  /-- `number`: a dispatch tag. -/
  | number
  /-- `number | undefined`: a popped continuation tag, `undefined` when the stack is empty. -/
  | numberOrNone
  /-- `rt.Value[]`: the saved-variable stack of the explicit-stack form. -/
  | values
  /-- `number[]`: the continuation stack of the explicit-stack form. -/
  | numbers
  deriving Inhabited, Repr, BEq, DecidableEq

inductive Expr where
  | var (x : Ident)
  /-- A member of the runtime module: `rt.name`. -/
  | rt (name : Ident)
  /-- A `bigint` literal, `123n`. -/
  | bigint (n : Nat)
  /-- A `number` literal. -/
  | num (n : Nat)
  | bool (b : Bool)
  | str (s : String)
  | undef
  | call (f : Expr) (args : List Expr)
  /-- A method call `e.name(args)`. -/
  | method (e : Expr) (name : Ident) (args : List Expr)
  | obj (fields : List (Ident × Expr))
  | arr (elems : List Expr)
  | prop (e : Expr) (name : Ident)
  | index (e : Expr) (i : Nat)
  /-- `a === b`. -/
  | strictEq (a b : Expr)
  deriving Inhabited, Repr, BEq

inductive Stmt where
  | const (x : Ident) (ty : Ty) (e : Expr)
  | «let» (x : Ident) (ty : Ty) (e : Expr)
  | assign (x : Ident) (e : Expr)
  | expr (e : Expr)
  /-- `label: { body }` -/
  | block (label : Ident) (body : List Stmt)
  /-- `label: while (true) { body }` -/
  | loop (label : Ident) (body : List Stmt)
  | «break» (label : Ident)
  | «continue» (label : Ident)
  /-- `switch (e) { case n: { … } … default: { … } }`; every case ends in a jump. -/
  | switch (e : Expr) (cases : List (Nat × List Stmt)) (dflt : List Stmt)
  | ite (c : Expr) (thn els : List Stmt)
  | ret (e : Expr)
  | throw (e : Expr)
  deriving Inhabited, Repr, BEq

structure Fn where
  name : Ident
  params : List (Ident × Ty)
  ret : Ty
  body : List Stmt
  deriving Inhabited, Repr, BEq

/-- One printed module: the whole closure of the compiled roots. -/
structure Program where
  /-- Module specifier of the runtime, imported as `rt`. -/
  runtime : String
  fns : List Fn
  deriving Inhabited, Repr, BEq

end TSLean.Lcnf.Target
