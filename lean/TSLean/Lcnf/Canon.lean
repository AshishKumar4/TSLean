module

public import Lean
public import TSLean.Lcnf.Extract

/-!
# Canonical auxiliary names and closure digests

Lean's auxiliary names are deterministic but not local (p2). Specialization reuses a cached
specialization under the name of whichever declaration created it first, so adding an unrelated
`other` renames `total`'s `List.foldl._at_.total.spec_0` to `List.foldl._at_.other.spec_0`, and
`import Lean` makes user code call `…_at_.Lean.Server.Test.Cancel.mkTestTask.spec_1._redArg`.

**Choice: content addressing.** Each auxiliary declaration (a name with an internal component:
`_at_`, `spec_N`, `_redArg`, `_closed_N`, `_private` mangling) is renamed to
`<origin>._lcnf_<h>`, where `<origin>` is the readable declaration it derives from and `<h>` is the
SHA-256 of its alpha-normalized signature and body, with the auxiliaries it references already
replaced by their canonical names (a Merkle hash over the reference graph).

A root-relative ordinal was the alternative. It was rejected for three reasons:
* An ordinal is not a function of content. A shared specialization reached from two roots gets
  two names, or a package-level ordinal shifts whenever a root is added.
* An ordinal depends on discovery order, which is the walk's implementation detail rather than the
  code's meaning.
* Content addressing deduplicates identical code for free and gives each auxiliary a name that is
  stable across programs, toolchain runs and packages.

The one cost is recursion. An auxiliary cannot hash a reference to itself before its own hash
exists, so hashing proceeds by strongly connected component of the aux→aux reference graph, in
dependency order. Inside a component, references to members become positional placeholders. Members
are ordered by a shape hash that treats every in-component reference alike. A tie between two
members of one multi-member component falls back to the raw name. That is the one non-local input,
and it is reachable only by two mutually recursive auxiliaries whose shapes are identical.

Alpha normalization renumbers every `FVarId` to `_lcnf.fv.<k>` in binding order and erases binder
names. `FVarId`s come from a per-session name generator, and binder names are not part of meaning.
-/

open Lean Compiler LCNF

namespace TSLean.Lcnf.Canon

@[expose] public section

/-! ## SHA-256 -/

def sha256K : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

@[inline] def rotr (x : UInt32) (n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

def sha256Block (h : Array UInt32) (msg : ByteArray) (off : Nat) : Array UInt32 := Id.run do
  let mut w : Array UInt32 := Array.mkEmpty 64
  for i in [0:16] do
    let b (j : Nat) : UInt32 := (msg.get! (off + 4 * i + j)).toUInt32
    w := w.push ((b 0 <<< 24) ||| (b 1 <<< 16) ||| (b 2 <<< 8) ||| b 3)
  for i in [16:64] do
    let s0 := rotr w[i-15]! 7 ^^^ rotr w[i-15]! 18 ^^^ (w[i-15]! >>> 3)
    let s1 := rotr w[i-2]! 17 ^^^ rotr w[i-2]! 19 ^^^ (w[i-2]! >>> 10)
    w := w.push (w[i-16]! + s0 + w[i-7]! + s1)
  let mut a := h[0]!; let mut b := h[1]!; let mut c := h[2]!; let mut d := h[3]!
  let mut e := h[4]!; let mut f := h[5]!; let mut g := h[6]!; let mut hh := h[7]!
  for i in [0:64] do
    let s1 := rotr e 6 ^^^ rotr e 11 ^^^ rotr e 25
    let ch := (e &&& f) ^^^ ((~~~e) &&& g)
    let t1 := hh + s1 + ch + sha256K[i]! + w[i]!
    let s0 := rotr a 2 ^^^ rotr a 13 ^^^ rotr a 22
    let maj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
    let t2 := s0 + maj
    hh := g; g := f; f := e; e := d + t1; d := c; c := b; b := a; a := t1 + t2
  return #[h[0]! + a, h[1]! + b, h[2]! + c, h[3]! + d, h[4]! + e, h[5]! + f, h[6]! + g, h[7]! + hh]

def hexDigit (n : UInt32) : Char := "0123456789abcdef".toList[n.toNat]!

/-- SHA-256 of a byte string, as 64 lowercase hex digits. -/
def sha256 (input : ByteArray) : String := Id.run do
  let bitLen := input.size * 8
  let mut msg := input.push 0x80
  while msg.size % 64 != 56 do msg := msg.push 0
  for i in [0:8] do msg := msg.push (bitLen >>> (8 * (7 - i))).toUInt8
  let mut h : Array UInt32 := #[0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
                                0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]
  let mut off := 0
  while off < msg.size do
    h := sha256Block h msg off
    off := off + 64
  let mut out := ""
  for x in h do
    for i in [0:8] do out := out.push (hexDigit ((x >>> (4 * (7 - i).toUInt32)) &&& 0xf))
  return out

def sha256Str (s : String) : String := sha256 s.toUTF8

/-! ## Names -/

/-- An auxiliary declaration: a name with an internal component (`_at_`, `spec_N`, `_redArg`,
`_closed_N`, `_private`, …). Canonicalization renames exactly these. -/
def isAux (n : Name) : Bool := n.isInternal

/-- The readable part of an auxiliary name: its `Extract.origin`, cut at the first internal
component. -/
def readableBase (n : Name) : Name :=
  let cs := (Extract.origin n).components
  let kept := cs.takeWhile (fun c => !c.isInternal)
  let base := kept.foldl (fun acc c => acc ++ c) .anonymous
  if base.isAnonymous then `_lcnf_aux else base

/-! ## Alpha normalization and renaming -/

structure NormState where
  fvars : Std.HashMap FVarId FVarId := {}
  next : Nat := 0

abbrev NormM := StateM NormState

def bindFVar (id : FVarId) : NormM FVarId := do
  let s ← get
  let id' : FVarId := ⟨.num `_lcnf.fv s.next⟩
  set { s with fvars := s.fvars.insert id id', next := s.next + 1 }
  return id'

def useFVar (id : FVarId) : NormM FVarId := do
  return (← get).fvars.getD id id

structure Renaming where
  const : Name → Name
  eraseBinders : Bool

def normExpr (r : Renaming) (e : Expr) : NormM Expr := do
  let fv := (← get).fvars
  return e.replace fun
    | .fvar id => some (.fvar (fv.getD id id))
    | .const n us => some (.const (r.const n) us)
    | _ => none

def normBinder (r : Renaming) (n : Name) : Name := if r.eraseBinders then .anonymous else n

def normArg (r : Renaming) : Arg .pure → NormM (Arg .pure)
  | .erased => pure .erased
  | .fvar id => return .fvar (← useFVar id)
  | .type e _ => return .type (← normExpr r e)

def normParam (r : Renaming) (p : Param .pure) : NormM (Param .pure) := do
  let ty ← normExpr r p.type
  return { p with fvarId := ← bindFVar p.fvarId, binderName := normBinder r p.binderName, type := ty }

def normLetValue (r : Renaming) : LetValue .pure → NormM (LetValue .pure)
  | .lit v => pure (.lit v)
  | .erased => pure .erased
  | .proj t i s _ => return .proj t i (← useFVar s)
  | .const n us as _ => return .const (r.const n) us (← as.mapM (normArg r))
  | .fvar f as => return .fvar (← useFVar f) (← as.mapM (normArg r))

mutual
partial def normCode (r : Renaming) : Code .pure → NormM (Code .pure)
  | .let d k => do
    let ty ← normExpr r d.type
    let v ← normLetValue r d.value
    let id ← bindFVar d.fvarId
    return .let { fvarId := id, binderName := normBinder r d.binderName, type := ty, value := v }
      (← normCode r k)
  | .fun d k _ => do let d' ← normFunDecl r d; return .fun d' (← normCode r k)
  | .jp d k => do let d' ← normFunDecl r d; return .jp d' (← normCode r k)
  | .jmp j as => return .jmp (← useFVar j) (← as.mapM (normArg r))
  | .cases c => do
    let ty ← normExpr r c.resultType
    let discr ← useFVar c.discr
    let alts ← c.alts.mapM fun
      | .alt ctor ps k _ => do
        let ps' ← ps.mapM (normParam r)
        return .alt ctor ps' (← normCode r k)
      | .default k => return .default (← normCode r k)
    return .cases ⟨c.typeName, ty, discr, alts⟩
  | .return x => return .return (← useFVar x)
  | .unreach t => return .unreach (← normExpr r t)

partial def normFunDecl (r : Renaming) (d : FunDecl .pure) : NormM (FunDecl .pure) := do
  let id ← bindFVar d.fvarId
  let ps ← d.params.mapM (normParam r)
  let ty ← normExpr r d.type
  return .mk id (normBinder r d.binderName) ps ty (← normCode r d.value)
end

/-- Rename constants through `r` and renumber free variables in binding order. -/
def normDecl (r : Renaming) (d : Decl .pure) : Decl .pure :=
  (go).run' {}
where
  go : NormM (Decl .pure) := do
    let ty ← normExpr r d.type
    let ps ← d.params.mapM (normParam r)
    let v ← match d.value with
      | .code c => pure (DeclValue.code (← normCode r c))
      | .extern e => pure (.extern e)
    return { d with name := r.const d.name, type := ty, params := ps, value := v }

def declBytes (d : Decl .pure) : Except String String :=
  return (← Serialize.serializeDecl d).compress

/-! ## Strongly connected components (Tarjan) -/

structure TarjanState where
  index : Std.HashMap Name Nat := {}
  low : Std.HashMap Name Nat := {}
  onStack : NameSet := {}
  stack : Array Name := #[]
  next : Nat := 0
  sccs : Array (Array Name) := #[]

/-- Tarjan's algorithm. Components come out in reverse topological order: a component is emitted
only after every component it reaches. -/
partial def tarjan (nodes : Array Name) (succ : Name → Array Name) : Array (Array Name) :=
  (nodes.forM visitIfNew |>.run {}).2.sccs
where
  visitIfNew (v : Name) : StateM TarjanState Unit := do
    unless (← get).index.contains v do visit v
  visit (v : Name) : StateM TarjanState Unit := do
    modify fun s => { s with index := s.index.insert v s.next, low := s.low.insert v s.next,
                             next := s.next + 1, stack := s.stack.push v,
                             onStack := s.onStack.insert v }
    for w in succ v do
      if !(← get).index.contains w then
        visit w
        modify fun s => { s with low := s.low.insert v (min s.low[v]! s.low[w]!) }
      else if (← get).onStack.contains w then
        modify fun s => { s with low := s.low.insert v (min s.low[v]! s.index[w]!) }
    let s ← get
    if s.low[v]! == s.index[v]! then
      let mut comp := #[]
      let mut st := s.stack
      let mut on := s.onStack
      repeat
        let w := st.back!
        st := st.pop
        on := on.erase w
        comp := comp.push w
        if w == v then break
      set { s with stack := st, onStack := on, sccs := s.sccs.push comp }

/-! ## Canonicalization -/

structure Result where
  /-- Canonical declarations: auxiliaries renamed, free variables renumbered, binder names kept;
  identical auxiliaries deduplicated. Order follows the closure's. -/
  decls : Array (Decl .pure)
  /-- Raw auxiliary name ↦ canonical name. -/
  renames : Array (Name × Name)
  /-- Per root: SHA-256 over its reachable canonical closure. -/
  rootDigests : Array (Name × String)

def leafLines (c : Extract.Closure) : Std.HashMap Name String := Id.run do
  let mut m : Std.HashMap Name String := {}
  for l in c.externs do
    m := m.insert l.name s!"extern {l.name} {(Serialize.encExternAttrData l.data).compress}"
  for l in c.opaqueExterns do
    m := m.insert l.name s!"opaque-extern {l.name} {(Serialize.encExternAttrData l.data).compress}"
  for l in c.ctors do
    m := m.insert l.name s!"ctor {l.name} {l.induct} {l.cidx} {l.numParams} {l.numFields}"
  return m

/-- SHA-256 over the declarations reachable from `root` (each as alpha-normalized, binder-erased
JSON, sorted by name) and the leaves they reference. With `decls` raw, this is the raw digest,
which moves whenever Lean's auxiliary names move; with `decls` canonical, it is the canonical one. -/
def rootDigest (leaves : Std.HashMap Name String) (decls : Array (Decl .pure)) (root : Name) :
    Except String String := do
  let byName : Std.HashMap Name (Decl .pure) := decls.foldl (fun m d => m.insert d.name d) {}
  let mut seen : NameSet := {}
  let mut todo := #[root]
  let mut lines : Array String := #[]
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    match byName[n]? with
    | some d =>
      let id : Renaming := { const := id, eraseBinders := true }
      lines := lines.push s!"decl {n} {← declBytes (normDecl id d)}"
      if let .code c := d.value then todo := todo ++ Extract.refs c #[]
    | none =>
      match leaves[n]? with
      | some l => lines := lines.push l
      | none => lines := lines.push s!"refused {n}"
  return sha256Str ("\n".intercalate (lines.qsort (· < ·)).toList)

def canonicalize (c : Extract.Closure) : Except String Result := do
  let rootSet : NameSet := c.roots.foldl (·.insert ·) {}
  let byName : Std.HashMap Name (Decl .pure) := c.decls.foldl (fun m d => m.insert d.name d) {}
  let auxs := c.decls.filterMap fun d => if isAux d.name && !rootSet.contains d.name then some d.name else none
  let auxSet : NameSet := auxs.foldl (·.insert ·) {}
  let succ (n : Name) : Array Name :=
    match byName[n]? with
    | some { value := .code body, .. } => (Extract.refs body #[]).filter auxSet.contains
    | _ => #[]
  let mut canon : NameMap Name := {}
  let mut owner : Std.HashMap Name String := {}  -- canonical name ↦ content bytes
  for scc in tarjan auxs succ do
    let inScc : NameSet := scc.foldl (·.insert ·) {}
    let outside (n : Name) : Name := (canon.find? n).getD n
    -- Shape: every in-component reference is the same placeholder.
    let shapeR : Renaming :=
      { const := fun n => if inScc.contains n then `_lcnf.scc else outside n, eraseBinders := true }
    let mut shaped : Array (String × Name) := #[]
    for m in scc do
      shaped := shaped.push (sha256Str (← declBytes (normDecl shapeR byName[m]!)), m)
    let ordered := (shaped.qsort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2.toString < b.2.toString)).map (·.2)
    let pos : NameMap Nat := ordered.zipIdx.foldl (fun m (n, i) => m.insert n i) {}
    let posR : Renaming :=
      { const := fun n => match pos.find? n with | some i => .num `_lcnf.scc i | none => outside n,
        eraseBinders := true }
    let mut body := ""
    for m in ordered do body := body ++ (← declBytes (normDecl posR byName[m]!)) ++ "\n"
    let h := (sha256Str body).take 16
    for (m, i) in ordered.zipIdx do
      let suffix := if ordered.size == 1 then s!"_lcnf_{h}" else s!"_lcnf_{h}_{i}"
      let cn := readableBase m ++ Name.mkSimple suffix
      let content := s!"{body}#{i}"
      if let some prev := owner[cn]? then
        if prev != content then throw s!"lcnf.canon.collision: {cn} names two different declarations"
      owner := owner.insert cn content
      canon := canon.insert m cn
  let rename (n : Name) : Name := (canon.find? n).getD n
  let r : Renaming := { const := rename, eraseBinders := false }
  let mut decls : Array (Decl .pure) := #[]
  let mut emitted : NameSet := {}
  for d in c.decls do
    let d' := normDecl r d
    unless emitted.contains d'.name do
      emitted := emitted.insert d'.name
      decls := decls.push d'
  let leaves := leafLines c
  let digests ← c.roots.mapM fun root => return (root, ← rootDigest leaves decls root)
  return { decls, renames := auxs.map fun n => (n, rename n), rootDigests := digests }

/-- The raw digest of each root: the same digest over Lean's own names, before canonicalization.
A control: it moves when an unrelated declaration renames a specialization. -/
def rawDigests (c : Extract.Closure) : Except String (Array (Name × String)) :=
  let leaves := leafLines c
  c.roots.mapM fun root => return (root, ← rootDigest leaves c.decls root)

end

end TSLean.Lcnf.Canon
