import TSLean.Lcnf.Extract
import TSLean.Lcnf.Canon
import TSLean.Lcnf.Semantics
import TSLean.Lcnf.Lower
import TSLean.Lcnf.Print

/-!
# Driver and differential-test harness for the LCNF → TypeScript lowering

`compile roots runtime` runs the whole pipeline on exactly what M1 extracts:
`Extract.closure` → refusals checked → `Canon.canonicalize` → `Lower.gatherInfo` → `Lower.lower` →
`Print.program`.

`runSuite` is the harness. For each test case it holds the arguments and Lean's own `#eval` result
as `Semantics.V` values. It

* runs the LCNF big-step semantics on the canonical declarations and checks it against `#eval`;
* writes the printed module and a manifest of cases whose arguments and expected results are
  rendered in the *R format*, a prefix token stream of the JS representation:
  `n<digits>` a `Nat` (`bigint`), `t`/`f` a `Bool`, `e<i>` an enumeration tag, `o<tag>.<k>` an
  object followed by its `k` relevant fields, `u` an erased value, `c` a closure.

`tests/lcnf/runner.ts` decodes the arguments, runs the printed module under Node and compares its
rendering with the expected tokens. The format is flat, so neither side recurses on the depth of a
value. Not a `module`: the extractor asserts the private olean level.
-/

open Lean Compiler LCNF

namespace TSLean.Lcnf.Driver

abbrev V := Semantics.V

structure Compiled where
  closure : Extract.Closure
  /-- Canonical declarations, in the closure's order (roots first). -/
  decls : Array (Decl .pure)
  info : Lower.Info
  program : Target.Program
  text : String

/-- Extract, canonicalize, lower and print the closure of `roots`. A refusal at any stage throws. -/
def compile (roots : Array Name) (runtime : String) : CoreM Compiled := do
  let c ← Extract.closure roots
  unless c.refusals.isEmpty do
    throwError m!"refused:\n{"\n".intercalate (c.refusals.map toString).toList}"
  let r ← match Canon.canonicalize c with
    | .ok r => pure r
    | .error e => throwError e
  let info ← match ← Lower.gatherInfo r.decls with
    | .ok i => pure i
    | .error e => throwError m!"lcnf.lower: {e}"
  let program ← match Lower.lower info runtime r.decls with
    | .ok p => pure p
    | .error e => throwError m!"lcnf.lower: {e}"
  return { closure := c, decls := r.decls, info, program, text := Print.program program }

/-- The semantics' view of the compiled closure: code declarations, constructor leaves and the
primitives of the slice. -/
def semProgram (c : Compiled) : Semantics.Program := Id.run do
  let mut consts : Std.HashMap Name Semantics.Const := {}
  for d in c.decls do
    if let .code body := d.value then consts := consts.insert d.name (.code d.params body)
  for l in c.closure.ctors do consts := consts.insert l.name (.ctor l.numParams l.numFields)
  for l in c.closure.externs do
    if let some a := Semantics.primArity l.name then consts := consts.insert l.name (.prim a)
  return { consts }

/-! ## Lean values as semantics values -/

class ToSem (α : Type) where
  toSem : α → V

export ToSem (toSem)

instance : ToSem Nat := ⟨.nat⟩
instance : ToSem Bool := ⟨Semantics.boolV⟩
instance [ToSem α] : ToSem (List α) :=
  ⟨fun xs => xs.foldr (fun x acc => .ctor ``List.cons #[toSem x, acc]) (.ctor ``List.nil #[])⟩
instance [ToSem α] : ToSem (Option α) :=
  ⟨fun | none => .ctor ``Option.none #[] | some a => .ctor ``Option.some #[toSem a]⟩
instance [ToSem α] [ToSem β] : ToSem (α × β) := ⟨fun (a, b) => .ctor ``Prod.mk #[toSem a, toSem b]⟩

/-! ## Generated inputs -/

/-- `n` pseudo-random naturals below `bound`, from a 64-bit linear congruential generator. -/
def gen (seed n bound : Nat) : List Nat := Id.run do
  let mut x := seed
  let mut out : Array Nat := #[]
  for _ in [0:n] do
    x := (6364136223846793005 * x + 1442695040888963407) % 2 ^ 64
    out := out.push (x % bound)
  return out.toList

/-! ## The R format -/

/-- Render a value as the JS representation's token stream. Iterative: values may be 10⁶ deep. -/
partial def render (info : Lower.Info) (v : V) : CoreM String := do
  let mut cache := info.ctors
  let mut out := ""
  let mut todo : List V := [v]
  repeat
    match todo with
    | [] => break
    | v :: rest =>
      todo := rest
      out := if out.isEmpty then out else out.push ' '
      match v with
      | .nat n => out := out ++ "n" ++ toString n
      | .str _ => throwError "render: strings are outside the slice"
      | .erased => out := out.push 'u'
      | .clo .. => out := out.push 'c'
      | .ctor n fs =>
        let c ← match cache[n]? with
          | some c => pure c
          | none =>
            let some (.ctorInfo ci) := (← getEnv).find? n | throwError "render: {n} is not a constructor"
            match ← Lower.ctorRep n ci with
            | .ok c => cache := cache.insert n c; pure c
            | .error e => throwError e
        match c.rep with
        | .bool => out := out.push (if c.cidx == 1 then 't' else 'f')
        | .enum => out := out ++ "e" ++ toString c.cidx
        | .obj =>
          let kept := (fs.zip c.relevant).filterMap fun (f, r) => if r then some f else none
          out := out ++ "o" ++ toString c.cidx ++ "." ++ toString kept.size
          todo := kept.toList ++ todo
  return out

/-! ## Suites -/

structure Case where
  label : String
  root : Name
  args : Array V
  /-- Lean's own `#eval` of the root on the arguments. -/
  expect : V
  /-- Also run the LCNF semantics on this case. -/
  sem : Bool := true

def fuel : Nat := 10 ^ 12

/-- Compile `roots`, check the semantics against `#eval` on every case, and write
`$LCNF_OUT/<name>.ts` and `$LCNF_OUT/<name>.json` for `tests/lcnf/runner.ts`. The module imports
the runtime from `$LCNF_RUNTIME`. -/
def runSuite (name : String) (roots : Array Name) (cases : Array Case) : CoreM Unit := do
  let some out ← IO.getEnv "LCNF_OUT" | throwError "LCNF_OUT is not set"
  let some runtime ← IO.getEnv "LCNF_RUNTIME" | throwError "LCNF_RUNTIME is not set"
  let comp ← compile roots runtime
  let (fns, _) := Lower.publicNames comp.decls
  IO.println s!"[{name}] closure: {comp.decls.size} code decls, {comp.closure.externs.size} externs, {comp.closure.ctors.size} ctors, {comp.closure.implementedBy.size} implemented_by pairs, {comp.closure.unsafeDecls.size} unsafe decls; {comp.program.fns.length} JS functions"
  IO.FS.writeFile (System.FilePath.mk out / s!"{name}.ts") comp.text
  let P := semProgram comp
  let mut rows : Array Json := #[]
  let mut failed : Array String := #[]
  for c in cases do
    let some (fn, _) := fns[c.root]? | throwError "{c.label}: root {c.root} was not compiled"
    let expect ← render comp.info c.expect
    if c.sem then
      let t0 ← IO.monoMsNow
      let got ← match Semantics.run P fuel c.root c.args with
        | .ok v => render comp.info v
        | .error .exhausted => pure "<exhausted>"
        | .error (.fault m) => pure s!"<fault {m}>"
      let ms := (← IO.monoMsNow) - t0
      if got == expect then IO.println s!"[{name}] sem {c.label}: agrees with #eval ({ms} ms)"
      else
        failed := failed.push c.label
        IO.println s!"[{name}] sem {c.label}: DISAGREES with #eval: got {got.take 200}, expected {expect.take 200}"
    let args ← c.args.mapM (render comp.info)
    rows := rows.push (Json.mkObj [("label", c.label), ("fn", fn), ("args", toJson args),
                                   ("expect", expect)])
  let manifest := Json.mkObj [("module", s!"{name}.ts"), ("cases", Json.arr rows)]
  IO.FS.writeFile (System.FilePath.mk out / s!"{name}.json") manifest.compress
  unless failed.isEmpty do throwError "[{name}] semantics disagrees with #eval on {failed}"

end TSLean.Lcnf.Driver
