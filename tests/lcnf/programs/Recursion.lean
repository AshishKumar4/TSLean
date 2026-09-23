import TSLean.Lcnf.Driver

/-! The recursion shapes of `/tmp/lcnf-advisory/p6_recursion.lean` and p6c's `loopJoin`, at the
sizes that broke the naive lowering. -/

def double : List Nat → List Nat
  | [] => []
  | x :: xs => (2 * x) :: double xs

mutual
def isEven : Nat → Bool
  | 0 => true
  | n + 1 => isOdd n
def isOdd : Nat → Bool
  | 0 => false
  | n + 1 => isEven n
end

inductive Tree where
  | leaf
  | node (l : Tree) (v : Nat) (r : Tree)

def Tree.size : Tree → Nat
  | .leaf => 0
  | .node l _ r => l.size + 1 + r.size

def sumTo (acc : Nat) : Nat → Nat
  | 0 => acc
  | n + 1 => sumTo (acc + n + 1) n

def loopJoin (xs : List Nat) : Nat × Nat := Id.run do
  let mut s := 0
  let mut c := 0
  for x in xs do
    if x > 3 then s := s + x else s := s * 2
    c := c + 1
  return (s, c)

open Lean TSLean.Lcnf.Driver

partial def treeSem : Tree → V
  | .leaf => .ctor ``Tree.leaf #[]
  | .node l v r => .ctor ``Tree.node #[treeSem l, toSem v, treeSem r]

instance : ToSem Tree := ⟨treeSem⟩

def leftDeep (n : Nat) : Tree := (List.range n).foldl (fun t i => .node t i .leaf) .leaf
def rightDeep (n : Nat) : Tree := (List.range n).foldl (fun t i => .node .leaf i t) .leaf
def balanced : Nat → Tree
  | 0 => .leaf
  | d + 1 => .node (balanced d) d (balanced d)

def case1 {α β} [ToSem α] [ToSem β] (label : String) (root : Name) (f : α → β) (a : α)
    (sem := true) : Case :=
  { label, root, args := #[toSem a], expect := toSem (f a), sem }

#eval show CoreM Unit from do
  let small := [0, 1, 5, 100]
  runSuite "Recursion" #[``double, ``isEven, ``isOdd, ``Tree.size, ``sumTo, ``loopJoin] <|
    (small.map fun n => case1 s!"double/gen{n}" ``double double (gen n n (2 ^ 80))).toArray ++
    #[case1 "double/10000" ``double double (gen 7 10000 1000),
      case1 "double/1000000" ``double double (gen 8 1000000 1000) (sem := false)] ++
    ([0, 1, 7, 1000].map fun n => case1 s!"isEven/{n}" ``isEven isEven n).toArray ++
    #[case1 "isOdd/999" ``isOdd isOdd 999,
      case1 "isEven/1000000" ``isEven isEven 1000000 (sem := false),
      case1 "isOdd/1000001" ``isOdd isOdd 1000001 (sem := false)] ++
    #[case1 "Tree.size/leaf" ``Tree.size Tree.size .leaf,
      case1 "Tree.size/balanced10" ``Tree.size Tree.size (balanced 10),
      case1 "Tree.size/leftDeep1000" ``Tree.size Tree.size (leftDeep 1000),
      case1 "Tree.size/leftDeep100000" ``Tree.size Tree.size (leftDeep 100000) (sem := false),
      case1 "Tree.size/rightDeep100000" ``Tree.size Tree.size (rightDeep 100000) (sem := false),
      case1 "Tree.size/balanced18" ``Tree.size Tree.size (balanced 18) (sem := false)] ++
    #[{ label := "sumTo/0/0", root := ``sumTo, args := #[toSem 0, toSem 0], expect := toSem (sumTo 0 0) },
      { label := "sumTo/5/100", root := ``sumTo, args := #[toSem 5, toSem 100], expect := toSem (sumTo 5 100) },
      { label := "sumTo/0/1000000", root := ``sumTo, args := #[toSem 0, toSem 1000000],
        expect := toSem (sumTo 0 1000000), sem := false }] ++
    (small.map fun n => case1 s!"loopJoin/gen{n}" ``loopJoin loopJoin (gen (n + 3) n 8)).toArray ++
    #[case1 "loopJoin/100000" ``loopJoin loopJoin (gen 9 100000 8) (sem := false)]
