import TSLean.Lcnf.Driver

/-! Non-tail recursion at sizes plain JS recursion survives (under 7,368 frames), to measure the
explicit stack against plain recursion (`scripts/lcnf-plant.mjs no-explicit-stack`). -/

def double : List Nat → List Nat
  | [] => []
  | x :: xs => (2 * x) :: double xs

def countdown : Nat → List Nat
  | 0 => [0]
  | n + 1 => (n + 1) :: countdown n

inductive Tree where
  | leaf
  | node (l : Tree) (v : Nat) (r : Tree)

def Tree.size : Tree → Nat
  | .leaf => 0
  | .node l _ r => l.size + 1 + r.size

open Lean TSLean.Lcnf.Driver

partial def treeSem : Tree → V
  | .leaf => .ctor ``Tree.leaf #[]
  | .node l v r => .ctor ``Tree.node #[treeSem l, toSem v, treeSem r]

instance : ToSem Tree := ⟨treeSem⟩

def leftDeep (n : Nat) : Tree := (List.range n).foldl (fun t i => .node t i .leaf) .leaf
def balanced : Nat → Tree
  | 0 => .leaf
  | d + 1 => .node (balanced d) d (balanced d)

def case1 {α β} [ToSem α] [ToSem β] (label : String) (root : Name) (f : α → β) (a : α) : Case :=
  { label, root, args := #[toSem a], expect := toSem (f a), sem := false }

#eval show CoreM Unit from do
  runSuite "Bench" #[``double, ``countdown, ``Tree.size]
    #[case1 "double/5000" ``double double (gen 1 5000 1000),
      case1 "countdown/5000" ``countdown countdown 5000,
      case1 "Tree.size/leftDeep5000" ``Tree.size Tree.size (leftDeep 5000),
      case1 "Tree.size/balanced16" ``Tree.size Tree.size (balanced 16)]
