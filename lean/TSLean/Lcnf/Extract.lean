module

public import Lean
public import TSLean.Lcnf.Serialize

/-!
# The mono-LCNF closure walk

`closure roots` walks the transitive `.const` references of the roots' mono-phase LCNF bodies and
classifies everything it reaches. It never substitutes: every form it does not carry is a named
`Refusal`, and a closure with any refusal is not compilable.

Classification of a reached constant `n`, in this order:

1. `@[extern]` attribute present (`getExternAttrData?`, never `DeclValue.extern`):
   * an `opaque` attribute entry is refused (`extern-opaque`);
   * the constant is an `opaque`/`axiom` with no reference body: an `opaqueExtern` leaf, `effectful`
     when its type mentions a world token. An effectful one is refused (`effectful-extern`); a pure
     one is refused with `requires-primitive-table-entry`, because admission is decided by the
     primitive table (M3) alone;
   * otherwise an `extern` leaf, which has a reference body.
2. A mono declaration with code: walked. Its body is checked for world-token types and for the forms
   never observed in mono (`proj`, `fun`, `erased` lets, `fvar` aliases, over-application, partial
   constructor application).
3. A mono declaration whose value is `extern [opaque]` without the attribute: the body was hidden by
   the olean level (p8). Refused (`extern-opaque`). The walk also asserts the private level up
   front, so this is a second line.
4. No mono declaration: a constructor is a `ctor` leaf; anything else is refused (`no-mono-decl`).

`@[implemented_by]` is not a stopping point: callers' mono bodies already name the implementation,
and the walk follows it. Each pair whose implementation is reached is recorded (the reverse map is
built from the attribute's own state).
-/

open Lean Compiler LCNF

@[expose] public section

namespace TSLean.Lcnf.Extract

/-- A leaf whose `@[extern]` constant has a reference body (a `def`). -/
structure ExternLeaf where
  name : Name
  data : ExternAttrData
  arity : Nat
  deriving BEq

/-- A leaf whose `@[extern]` constant is `opaque` (or an axiom): no reference body exists. -/
structure OpaqueExternLeaf where
  name : Name
  data : ExternAttrData
  arity : Nat
  /-- The mono signature or the kernel type mentions `lcVoid`, `EST.Out` or `IO.RealWorld`. -/
  effectful : Bool
  deriving BEq

structure CtorLeaf where
  name : Name
  induct : Name
  cidx : Nat
  numParams : Nat
  numFields : Nat
  deriving BEq

/-- An `@[implemented_by impl] ref` pair whose implementation the closure reaches. `via` is the
first reached declaration that is `impl` or one of its auxiliaries/specializations. -/
structure ImplementedByPair where
  ref : Name
  impl : Name
  via : Name
  deriving BEq

inductive Refusal where
  /-- An `extern [opaque]` value: either the attribute says so or the olean level hid the body. -/
  | externOpaque (name : Name)
  /-- An opaque extern whose type mentions a world token. Effects are data at the root. -/
  | effectfulExtern (name : Name)
  /-- A pure opaque extern. Only the primitive table (M3) may admit it. -/
  | requiresPrimitiveTableEntry (name : Name)
  /-- A code declaration whose types mention a world token. -/
  | worldToken (decl : Name) (token : Name)
  /-- A form never observed in mono, so no lowering exists for it. -/
  | unobservedForm (decl : Name) (form : String) (detail : String)
  /-- A referenced constant with neither a mono declaration nor a constructor. -/
  | noMonoDecl (name : Name) (kind : String)
  deriving BEq

def Refusal.code : Refusal → String
  | .externOpaque .. => "lcnf.extract.extern-opaque"
  | .effectfulExtern .. => "lcnf.extract.effectful-extern"
  | .requiresPrimitiveTableEntry .. => "lcnf.extract.requires-primitive-table-entry"
  | .worldToken .. => "lcnf.extract.world-token"
  | .unobservedForm .. => "lcnf.extract.unobserved-form"
  | .noMonoDecl .. => "lcnf.extract.no-mono-decl"

def Refusal.message : Refusal → String
  | r@(.externOpaque n) =>
    s!"{r.code}: {n} is `extern [opaque]`; its mono body is not available at this olean level"
  | r@(.effectfulExtern n) =>
    s!"{r.code}: {n} is an opaque extern over a world token; effects are data at the root"
  | r@(.requiresPrimitiveTableEntry n) =>
    s!"{r.code}: {n} is a pure opaque extern and requires a primitive-table entry"
  | r@(.worldToken d t) => s!"{r.code}: {d} mentions the world token {t}; effects are data at the root"
  | r@(.unobservedForm d f x) => s!"{r.code}: {d} contains `{f}` ({x}), a form never observed in mono"
  | r@(.noMonoDecl n k) => s!"{r.code}: {n} ({k}) has no mono declaration and is not a constructor"

instance : ToString Refusal := ⟨Refusal.message⟩

structure Closure where
  roots : Array Name
  /-- Code declarations in breadth-first discovery order from the roots. -/
  decls : Array (Decl .pure)
  externs : Array ExternLeaf
  opaqueExterns : Array OpaqueExternLeaf
  ctors : Array CtorLeaf
  implementedBy : Array ImplementedByPair
  /-- Code declarations with `safe = false` (`partial` or `unsafe`). -/
  unsafeDecls : Array Name
  refusals : Array Refusal

def Closure.admitted (c : Closure) : Bool := c.refusals.isEmpty

def externStr (d : ExternAttrData) : String :=
  " ".intercalate <| d.entries.map fun
    | .adhoc b => s!"adhoc {b}"
    | .inline b p => s!"inline {b} {p}"
    | .standard b f => s!"standard {b} {f}"
    | .opaque => "opaque"

/-- A deterministic text rendering of everything but the code bodies, for goldens. `rename` maps
code declaration names (identity for raw names, the canonical map for canonical ones). -/
def Closure.render (c : Closure) (rename : Name → Name := id) : String :=
  let block (title : String) (xs : Array String) : List String :=
    s!"{title} ({xs.size}):" :: xs.toList.map ("  " ++ ·)
  "\n".intercalate <|
    [s!"roots: {", ".intercalate (c.roots.map toString).toList}"] ++
    block "code decls" (c.decls.map (toString <| rename ·.name)) ++
    block "externs" (c.externs.map fun l => s!"{l.name}/{l.arity} [{externStr l.data}]") ++
    block "opaque externs" (c.opaqueExterns.map fun l =>
      s!"{l.name}/{l.arity} [{externStr l.data}] {if l.effectful then "effectful" else "pure"}") ++
    block "ctors" (c.ctors.map fun l => s!"{l.name} ({l.induct} #{l.cidx}, {l.numParams}+{l.numFields})") ++
    block "implemented_by" (c.implementedBy.map fun p => s!"{p.ref} -> {p.impl} via {rename p.via}") ++
    block "safe=false" (c.unsafeDecls.map (toString <| rename ·)) ++
    block "refusals" (c.refusals.map (·.message))

/-! ## The olean level -/

/-- A non-transparent stdlib declaration whose mono body is `extern [opaque]` at the exported
level and code at the private level (p8). -/
def levelSentinel : Name := ``Nat.toDigits

/-- Fail unless the environment exposes mono bodies at the private olean level. From a `module`
file, imported non-transparent mono bodies read as `extern [opaque]` (p8), and a closure walked
there would bottom out in refusals, or worse, look smaller than it is. -/
def assertPrivateLevel : CoreM Unit := do
  let env ← getEnv
  if env.header.isModule then
    throwError "lcnf.extract.olean-level: the environment is at the exported olean level (a `module` driver, or `importModules` below `.private`), so imported mono bodies read as `extern [opaque]`; run the extractor from a non-module file"
  match ← getDeclAt? levelSentinel .mono with
  | some { value := .code _, .. } => pure ()
  | some _ =>
    throwError "lcnf.extract.olean-level: the mono body of {levelSentinel} reads as `extern [opaque]`; the environment is at the exported level"
  | none =>
    throwError "lcnf.extract.olean-level: {levelSentinel} has no mono declaration; the environment does not expose the stdlib's mono bodies"

/-! ## Names -/

/-- Strip a `_private.<Module>.<n>.` prefix. -/
def unprivate (n : Name) : Name := (privateToUserName? n).getD n

/-- The declaration a name was derived from: private prefix removed, and everything from the first
`_at_` (specialization site) on removed. -/
def origin (n : Name) : Name :=
  let cs := (unprivate n).components
  let kept := cs.takeWhile (· != `_at_)
  kept.foldl (fun acc c => acc ++ c) .anonymous

/-- `@[implemented_by]` reverse map: implementation (unprivated) ↦ references. Built from the
attribute's state: every imported module's entries plus the current module's. -/
def implementedByReverse : CoreM (NameMap (Array Name)) := do
  let env ← getEnv
  let ext := implementedByAttr.ext
  let mut m : NameMap (Array Name) := {}
  for i in [0:env.header.moduleNames.size] do
    for (ref, impl) in ext.getModuleEntries env i do
      m := m.insert (unprivate impl) ((m.getD (unprivate impl) #[]).push ref)
  for (ref, impl) in (ext.getState env).2 do
    m := m.insert (unprivate impl) ((m.getD (unprivate impl) #[]).push ref)
  return m

/-! ## Bodies -/

def worldTokens : Array Name := #[``lcVoid, ``EST.Out, ``IO.RealWorld]

def worldTokenIn? (e : Expr) : Option Name :=
  worldTokens.find? fun t => (e.find? fun s => s.isConstOf t).isSome

/-- The constant references of a body, in first-occurrence order. -/
partial def refs (c : Code .pure) (acc : Array Name) : Array Name :=
  match c with
  | .let d k =>
    let acc := match d.value with
      | .const n _ _ _ => if acc.contains n then acc else acc.push n
      | _ => acc
    refs k acc
  | .fun d k _ | .jp d k => refs k (refs d.value acc)
  | .cases cs => cs.alts.foldl (fun acc alt => refs alt.getCode acc) acc
  | .jmp .. | .return _ | .unreach _ => acc

/-- The arity of a constant as mono applies it: its mono parameter count, or parameters plus
fields for a constructor. -/
def arity? (n : Name) : CoreM (Option Nat) := do
  if let some d ← getDeclAt? n .mono then return some d.params.size
  match (← getEnv).find? n with
  | some (.ctorInfo ci) => return some (ci.numParams + ci.numFields)
  | _ => return none

/-- Refusals for the forms never observed in mono. -/
partial def checkForms (decl : Name) (c : Code .pure) : StateT (Array Refusal) CoreM Unit := do
  let refuse (f x : String) : StateT (Array Refusal) CoreM Unit :=
    modify (·.push (.unobservedForm decl f x))
  match c with
  | .let d k =>
    match d.value with
    | .proj t i _ _ => refuse "proj" s!"{t}.{i}"
    | .erased => refuse "erased" s!"let {d.binderName}"
    | .fvar _ as => if as.isEmpty then refuse "fvar-alias" s!"let {d.binderName}"
    | .const n _ as _ =>
      match ← arity? n with
      | some a =>
        if as.size > a then refuse "over-application" s!"{n} takes {a}, applied to {as.size}"
        else if as.size < a && ((← getEnv).find? n matches some (.ctorInfo _)) then
          refuse "partial-ctor" s!"{n} takes {a}, applied to {as.size}"
      | none => pure ()  -- reported as `no-mono-decl` when the walk reaches `n`
    | .lit _ => pure ()
    checkForms decl k
  | .fun fd k _ => refuse "fun" s!"local function {fd.binderName}"; checkForms decl fd.value; checkForms decl k
  | .jp fd k => checkForms decl fd.value; checkForms decl k
  | .cases cs => for alt in cs.alts do checkForms decl alt.getCode
  | .jmp .. | .return _ | .unreach _ => pure ()

def constKind (n : Name) : CoreM String := do
  return match (← getEnv).find? n with
  | none => "unknown constant"
  | some (.inductInfo _) => "inductive"
  | some (.recInfo _) => "recursor"
  | some (.axiomInfo _) => "axiom"
  | some (.opaqueInfo _) => "opaque"
  | some (.quotInfo _) => "quot"
  | some (.defnInfo _) => "def"
  | some (.thmInfo _) => "theorem"
  | some (.ctorInfo _) => "constructor"

/-! ## The walk -/

/-- The mono closure of `roots`. Asserts the private olean level first. -/
def closure (roots : Array Name) : CoreM Closure := do
  assertPrivateLevel
  let env ← getEnv
  let reverse ← implementedByReverse
  let mut queue := roots
  let mut head := 0
  let mut seen : NameSet := roots.foldl (·.insert ·) {}
  let mut out : Closure :=
    { roots := roots, decls := #[], externs := #[], opaqueExterns := #[], ctors := #[], implementedBy := #[],
      unsafeDecls := #[], refusals := #[] }
  let mut pairsSeen : NameSet := {}
  while h : head < queue.size do
    let n := queue[head]
    head := head + 1
    let mut next : Array Name := #[]
    -- A reached `@[implemented_by]` reference: record the pair and follow the implementation.
    if let some impl := getImplementedBy? env n then
      unless pairsSeen.contains n do
        pairsSeen := pairsSeen.insert n
        out := { out with implementedBy := out.implementedBy.push ({ ref := n, impl := impl, via := n } : ImplementedByPair) }
      next := next.push impl
    if let some data := getExternAttrData? env n then
      let ar := (← arity? n).getD 0
      if data.entries.contains .opaque then
        out := { out with refusals := out.refusals.push (.externOpaque n) }
      else
        match env.find? n with
        | some (.opaqueInfo _) | some (.axiomInfo _) =>
          let kernelTy := (env.find? n).map (·.type)
          let monoTys := match ← getDeclAt? n .mono with
            | some d => d.params.foldl (fun acc p => acc.push p.type) #[d.type]
            | none => #[]
          let effectful := (monoTys ++ kernelTy.toArray).any (worldTokenIn? · |>.isSome)
          let leaf : OpaqueExternLeaf := { name := n, data := data, arity := ar, effectful := effectful }
          let r : Refusal := if effectful then .effectfulExtern n else .requiresPrimitiveTableEntry n
          out := { out with opaqueExterns := out.opaqueExterns.push leaf, refusals := out.refusals.push r }
        | _ => out := { out with externs := out.externs.push ({ name := n, data := data, arity := ar } : ExternLeaf) }
    else
      match ← getDeclAt? n .mono with
      | some d =>
        match d.value with
        | .code body =>
          out := { out with decls := out.decls.push d }
          unless d.safe do out := { out with unsafeDecls := out.unsafeDecls.push n }
          -- Pairs reached through an implementation or one of its auxiliaries.
          let o := origin n
          let mut p := o
          while !p.isAnonymous do
            for ref in reverse.getD p #[] do
              unless pairsSeen.contains ref do
                pairsSeen := pairsSeen.insert ref
                let pair : ImplementedByPair :=
                  { ref := ref, impl := (getImplementedBy? env ref).getD p, via := n }
                out := { out with implementedBy := out.implementedBy.push pair }
            p := p.getPrefix
          -- World tokens anywhere in the declaration's types.
          let tokens := (Serialize.declExprs d).filterMap worldTokenIn?
          for t in worldTokens do
            if tokens.contains t then out := { out with refusals := out.refusals.push (.worldToken n t) }
          let ((), rs) ← (checkForms n body).run #[]
          out := { out with refusals := out.refusals ++ rs }
          next := next ++ refs body #[]
        | .extern _ => out := { out with refusals := out.refusals.push (.externOpaque n) }
      | none =>
        match env.find? n with
        | some (.ctorInfo ci) =>
          let leaf : CtorLeaf := { name := n, induct := ci.induct, cidx := ci.cidx,
                                   numParams := ci.numParams, numFields := ci.numFields }
          out := { out with ctors := out.ctors.push leaf }
        | _ =>
          -- An `@[implemented_by]` reference has no mono decl of its own; its pair is recorded.
          if (getImplementedBy? env n).isNone then
            out := { out with refusals := out.refusals.push (.noMonoDecl n (← constKind n)) }
    for r in next do
      unless seen.contains r do
        seen := seen.insert r
        queue := queue.push r
  return out

end TSLean.Lcnf.Extract

end
