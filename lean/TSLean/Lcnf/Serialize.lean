module

public import Lean

/-!
# JSON ⇄ `LCNF.Code`

The IR of the LCNF pipeline is Lean's own mono-phase `Lean.Compiler.LCNF.Decl .pure`. This module
is its wire format: a faithful JSON encoding of every pure `Code`, `LetValue`, `Arg`, `Param`,
`Alt`, `FunDecl`, `Cases`, `Decl` and the `Expr`/`Level` types they carry.

The encoder is faithful rather than selective. It encodes forms the extractor refuses (`proj`,
`fun`, `erased`), because refusal is the extractor's decision and not the wire format's. It
refuses only what has no meaning outside one elaboration session: metavariables and `mdata`.

`roundTrip` checks `deserialize (serialize d) == d` with Lean's own `BEq (Decl .pure)` and checks that
re-serializing the decoded value yields the same bytes. When that check passes on every declaration
of a closure, the serializer is out of that closure's trusted base.
-/

open Lean Compiler LCNF

@[expose] public section

namespace TSLean.Lcnf.Serialize

/-- The format tag of an IR document. Bump it whenever the encoding changes. -/
def formatName : String := "tslean-lcnf-ir"
def formatVersion : Nat := 1

abbrev DecodeM := Except String

def jnat (n : Nat) : Json := .num (JsonNumber.fromNat n)
def tagged (tag : String) (xs : List Json) : Json := .arr (#[.str tag] ++ xs.toArray)

/-! ## Encoding -/

def encName : Name → Json
  | n => .arr (go n #[]).reverse
where
  go : Name → Array Json → Array Json
    | .anonymous, acc => acc
    | .str p s, acc => go p (acc.push (.str s))
    | .num p k, acc => go p (acc.push (jnat k))

def encLevel : Level → Except String Json
  | .zero => pure (tagged "zero" [])
  | .succ l => return tagged "succ" [← encLevel l]
  | .max a b => return tagged "max" [← encLevel a, ← encLevel b]
  | .imax a b => return tagged "imax" [← encLevel a, ← encLevel b]
  | .param n => pure (tagged "param" [encName n])
  | .mvar _ => throw "lcnf.serialize.level-mvar: a universe metavariable has no meaning outside its session"

def encBinderInfo : BinderInfo → Json
  | .default => .str "default"
  | .implicit => .str "implicit"
  | .strictImplicit => .str "strictImplicit"
  | .instImplicit => .str "instImplicit"

def encLiteral : Literal → Json
  | .natVal n => tagged "natLit" [jnat n]
  | .strVal s => tagged "strLit" [.str s]

def encExpr : Expr → Except String Json
  | .bvar i => pure (tagged "bvar" [jnat i])
  | .fvar id => pure (tagged "fvar" [encName id.name])
  | .mvar _ => throw "lcnf.serialize.expr-mvar: a metavariable has no meaning outside its session"
  | .sort l => return tagged "sort" [← encLevel l]
  | .const n us => return tagged "const" [encName n, .arr (← us.toArray.mapM encLevel)]
  | .app f a => return tagged "app" [← encExpr f, ← encExpr a]
  | .lam n t b bi => return tagged "lam" [encName n, ← encExpr t, ← encExpr b, encBinderInfo bi]
  | .forallE n t b bi => return tagged "pi" [encName n, ← encExpr t, ← encExpr b, encBinderInfo bi]
  | .letE n t v b nd => return tagged "let" [encName n, ← encExpr t, ← encExpr v, ← encExpr b, .bool nd]
  | .lit l => pure (encLiteral l)
  | .mdata _ _ => throw "lcnf.serialize.expr-mdata: metadata is not part of the IR"
  | .proj s i e => return tagged "proj" [encName s, jnat i, ← encExpr e]

def encLitValue : LitValue → Json
  | .nat v => tagged "nat" [jnat v]
  | .str v => tagged "str" [.str v]
  | .uint8 v => tagged "uint8" [jnat v.toNat]
  | .uint16 v => tagged "uint16" [jnat v.toNat]
  | .uint32 v => tagged "uint32" [jnat v.toNat]
  | .uint64 v => tagged "uint64" [jnat v.toNat]
  | .usize v => tagged "usize" [jnat v.toNat]

def encFVar (id : FVarId) : Json := encName id.name

def encArg : Arg .pure → Except String Json
  | .erased => pure (tagged "erased" [])
  | .fvar id => pure (tagged "fvar" [encFVar id])
  | .type e _ => return tagged "type" [← encExpr e]

def encArgs (as : Array (Arg .pure)) : Except String Json := return .arr (← as.mapM encArg)

def encLetValue : LetValue .pure → Except String Json
  | .lit v => pure (tagged "lit" [encLitValue v])
  | .erased => pure (tagged "erased" [])
  | .proj t i s _ => pure (tagged "proj" [encName t, jnat i, encFVar s])
  | .const n us as _ => return tagged "const" [encName n, .arr (← us.toArray.mapM encLevel), ← encArgs as]
  | .fvar f as => return tagged "fvarApp" [encFVar f, ← encArgs as]
  -- The remaining constructors carry `pu = .impure` and cannot inhabit `LetValue .pure`.

def encParam (p : Param .pure) : Except String Json :=
  return .arr #[encFVar p.fvarId, encName p.binderName, ← encExpr p.type, .bool p.borrow]

def encParams (ps : Array (Param .pure)) : Except String Json := return .arr (← ps.mapM encParam)

def encLetDecl (d : LetDecl .pure) : Except String Json :=
  return .arr #[encFVar d.fvarId, encName d.binderName, ← encExpr d.type, ← encLetValue d.value]

mutual
partial def encCode : Code .pure → Except String Json
  | .let d k => return tagged "let" [← encLetDecl d, ← encCode k]
  | .fun d k _ => return tagged "fun" [← encFunDecl d, ← encCode k]
  | .jp d k => return tagged "jp" [← encFunDecl d, ← encCode k]
  | .jmp j as => return tagged "jmp" [encFVar j, ← encArgs as]
  | .cases c => do
    let alts ← c.alts.mapM encAlt
    return tagged "cases" [encName c.typeName, ← encExpr c.resultType, encFVar c.discr, .arr alts]
  | .return x => pure (tagged "return" [encFVar x])
  | .unreach t => return tagged "unreach" [← encExpr t]

partial def encFunDecl (d : FunDecl .pure) : Except String Json :=
  return .arr #[encFVar d.fvarId, encName d.binderName, ← encParams d.params, ← encExpr d.type,
    ← encCode d.value]

partial def encAlt : Alt .pure → Except String Json
  | .alt c ps k _ => return tagged "alt" [encName c, ← encParams ps, ← encCode k]
  | .default k => return tagged "default" [← encCode k]
end

def encExternEntry : ExternEntry → Json
  | .adhoc b => tagged "adhoc" [encName b]
  | .inline b p => tagged "inline" [encName b, .str p]
  | .standard b f => tagged "standard" [encName b, .str f]
  | .opaque => tagged "opaque" []

def encExternAttrData (d : ExternAttrData) : Json := .arr (d.entries.toArray.map encExternEntry)

def encInline : Option InlineAttributeKind → Json
  | none => .null
  | some .inline => .str "inline"
  | some .noinline => .str "noinline"
  | some .macroInline => .str "macroInline"
  | some .inlineIfReduce => .str "inlineIfReduce"
  | some .alwaysInline => .str "alwaysInline"

def encDeclValue : DeclValue .pure → Except String Json
  | .code c => return tagged "code" [← encCode c]
  | .extern e => pure (tagged "extern" [encExternAttrData e])

/-- Encode one mono declaration. -/
def serializeDecl (d : Decl .pure) : Except String Json :=
  return Json.mkObj [
    ("name", encName d.name),
    ("levelParams", .arr (d.levelParams.toArray.map encName)),
    ("type", ← encExpr d.type),
    ("params", ← encParams d.params),
    ("safe", .bool d.safe),
    ("recursive", .bool d.recursive),
    ("inline", encInline d.inlineAttr?),
    ("value", ← encDeclValue d.value)]

/-! ## Decoding -/

def arr (j : Json) (what : String) : DecodeM (Array Json) :=
  match j with
  | .arr xs => pure xs
  | _ => throw s!"lcnf.deserialize: expected an array for {what}, got {j.compress}"

def nat (j : Json) (what : String) : DecodeM Nat :=
  match j.getNat? with
  | .ok n => pure n
  | .error _ => throw s!"lcnf.deserialize: expected a natural number for {what}, got {j.compress}"

def str (j : Json) (what : String) : DecodeM String :=
  match j with
  | .str s => pure s
  | _ => throw s!"lcnf.deserialize: expected a string for {what}, got {j.compress}"

def bool (j : Json) (what : String) : DecodeM Bool :=
  match j with
  | .bool b => pure b
  | _ => throw s!"lcnf.deserialize: expected a boolean for {what}, got {j.compress}"

/-- Split a tagged array `[tag, x₁, …, xₙ]`. -/
def untag (j : Json) (what : String) : DecodeM (String × Array Json) := do
  let xs ← arr j what
  let some t := xs[0]? | throw s!"lcnf.deserialize: empty tagged array for {what}"
  return (← str t s!"{what} tag", xs.extract 1 xs.size)

def badShape (what tag : String) (xs : Array Json) : DecodeM α :=
  throw s!"lcnf.deserialize: unknown {what} form `{tag}` with {xs.size} fields"

def decName (j : Json) : DecodeM Name := do
  let mut n := Name.anonymous
  for c in ← arr j "name" do
    match c with
    | .str s => n := .str n s
    | _ => n := .num n (← nat c "name component")
  return n

partial def decLevel (j : Json) : DecodeM Level := do
  match ← untag j "level" with
  | ("zero", #[]) => pure .zero
  | ("succ", #[l]) => return .succ (← decLevel l)
  | ("max", #[a, b]) => return .max (← decLevel a) (← decLevel b)
  | ("imax", #[a, b]) => return .imax (← decLevel a) (← decLevel b)
  | ("param", #[n]) => return .param (← decName n)
  | (t, xs) => badShape "level" t xs

def decBinderInfo (j : Json) : DecodeM BinderInfo := do
  match ← str j "binder info" with
  | "default" => pure .default
  | "implicit" => pure .implicit
  | "strictImplicit" => pure .strictImplicit
  | "instImplicit" => pure .instImplicit
  | s => throw s!"lcnf.deserialize: unknown binder info `{s}`"

partial def decExpr (j : Json) : DecodeM Expr := do
  match ← untag j "expr" with
  | ("bvar", #[i]) => return .bvar (← nat i "bvar")
  | ("fvar", #[n]) => return .fvar ⟨← decName n⟩
  | ("sort", #[l]) => return .sort (← decLevel l)
  | ("const", #[n, us]) => return .const (← decName n) (← (← arr us "levels").mapM decLevel).toList
  | ("app", #[f, a]) => return .app (← decExpr f) (← decExpr a)
  | ("lam", #[n, t, b, bi]) =>
    return .lam (← decName n) (← decExpr t) (← decExpr b) (← decBinderInfo bi)
  | ("pi", #[n, t, b, bi]) =>
    return .forallE (← decName n) (← decExpr t) (← decExpr b) (← decBinderInfo bi)
  | ("let", #[n, t, v, b, nd]) =>
    return .letE (← decName n) (← decExpr t) (← decExpr v) (← decExpr b) (← bool nd "letE nondep")
  | ("natLit", #[n]) => return .lit (.natVal (← nat n "nat literal"))
  | ("strLit", #[s]) => return .lit (.strVal (← str s "string literal"))
  | ("proj", #[s, i, e]) => return .proj (← decName s) (← nat i "proj index") (← decExpr e)
  | (t, xs) => badShape "expr" t xs

def boundedNat (j : Json) (what : String) (bound : Nat) : DecodeM Nat := do
  let n ← nat j what
  unless n < bound do throw s!"lcnf.deserialize: {what} literal {n} is out of range"
  return n

def decLitValue (j : Json) : DecodeM LitValue := do
  match ← untag j "literal" with
  | ("nat", #[n]) => return .nat (← nat n "nat")
  | ("str", #[s]) => return .str (← str s "str")
  | ("uint8", #[n]) => return .uint8 (← boundedNat n "uint8" UInt8.size).toUInt8
  | ("uint16", #[n]) => return .uint16 (← boundedNat n "uint16" UInt16.size).toUInt16
  | ("uint32", #[n]) => return .uint32 (← boundedNat n "uint32" UInt32.size).toUInt32
  | ("uint64", #[n]) => return .uint64 (← boundedNat n "uint64" UInt64.size).toUInt64
  | ("usize", #[n]) => return .usize (← boundedNat n "usize" UInt64.size).toUInt64
  | (t, xs) => badShape "literal" t xs

def decFVar (j : Json) : DecodeM FVarId := return ⟨← decName j⟩

def decArg (j : Json) : DecodeM (Arg .pure) := do
  match ← untag j "arg" with
  | ("erased", #[]) => pure .erased
  | ("fvar", #[f]) => return .fvar (← decFVar f)
  | ("type", #[e]) => return .type (← decExpr e)
  | (t, xs) => badShape "arg" t xs

def decArgs (j : Json) : DecodeM (Array (Arg .pure)) := do (← arr j "args").mapM decArg

def decLetValue (j : Json) : DecodeM (LetValue .pure) := do
  match ← untag j "let value" with
  | ("lit", #[v]) => return .lit (← decLitValue v)
  | ("erased", #[]) => pure .erased
  | ("proj", #[t, i, s]) => return .proj (← decName t) (← nat i "proj index") (← decFVar s)
  | ("const", #[n, us, as]) =>
    return .const (← decName n) (← (← arr us "levels").mapM decLevel).toList (← decArgs as)
  | ("fvarApp", #[f, as]) => return .fvar (← decFVar f) (← decArgs as)
  | (t, xs) => badShape "let value" t xs

def decParam (j : Json) : DecodeM (Param .pure) := do
  match ← arr j "param" with
  | #[f, n, t, b] =>
    return { fvarId := ← decFVar f, binderName := ← decName n, type := ← decExpr t,
             borrow := ← bool b "borrow" }
  | xs => throw s!"lcnf.deserialize: a param has 4 fields, got {xs.size}"

def decParams (j : Json) : DecodeM (Array (Param .pure)) := do (← arr j "params").mapM decParam

def decLetDecl (j : Json) : DecodeM (LetDecl .pure) := do
  match ← arr j "let decl" with
  | #[f, n, t, v] =>
    return { fvarId := ← decFVar f, binderName := ← decName n, type := ← decExpr t,
             value := ← decLetValue v }
  | xs => throw s!"lcnf.deserialize: a let decl has 4 fields, got {xs.size}"

mutual
partial def decCode (j : Json) : DecodeM (Code .pure) := do
  match ← untag j "code" with
  | ("let", #[d, k]) => return .let (← decLetDecl d) (← decCode k)
  | ("fun", #[d, k]) => return .fun (← decFunDecl d) (← decCode k)
  | ("jp", #[d, k]) => return .jp (← decFunDecl d) (← decCode k)
  | ("jmp", #[f, as]) => return .jmp (← decFVar f) (← decArgs as)
  | ("cases", #[t, r, d, alts]) =>
    return .cases ⟨← decName t, ← decExpr r, ← decFVar d, ← (← arr alts "alts").mapM decAlt⟩
  | ("return", #[x]) => return .return (← decFVar x)
  | ("unreach", #[t]) => return .unreach (← decExpr t)
  | (t, xs) => badShape "code" t xs

partial def decFunDecl (j : Json) : DecodeM (FunDecl .pure) := do
  match ← arr j "fun decl" with
  | #[f, n, ps, t, v] =>
    return .mk (← decFVar f) (← decName n) (← decParams ps) (← decExpr t) (← decCode v)
  | xs => throw s!"lcnf.deserialize: a fun decl has 5 fields, got {xs.size}"

partial def decAlt (j : Json) : DecodeM (Alt .pure) := do
  match ← untag j "alt" with
  | ("alt", #[c, ps, k]) => return .alt (← decName c) (← decParams ps) (← decCode k)
  | ("default", #[k]) => return .default (← decCode k)
  | (t, xs) => badShape "alt" t xs
end

def decExternEntry (j : Json) : DecodeM ExternEntry := do
  match ← untag j "extern entry" with
  | ("adhoc", #[b]) => return .adhoc (← decName b)
  | ("inline", #[b, p]) => return .inline (← decName b) (← str p "inline pattern")
  | ("standard", #[b, f]) => return .standard (← decName b) (← str f "extern function")
  | ("opaque", #[]) => pure .opaque
  | (t, xs) => badShape "extern entry" t xs

def decExternAttrData (j : Json) : DecodeM ExternAttrData := do
  return { entries := (← (← arr j "extern entries").mapM decExternEntry).toList }

def decInline (j : Json) : DecodeM (Option InlineAttributeKind) := do
  match j with
  | .null => pure none
  | .str "inline" => pure (some .inline)
  | .str "noinline" => pure (some .noinline)
  | .str "macroInline" => pure (some .macroInline)
  | .str "inlineIfReduce" => pure (some .inlineIfReduce)
  | .str "alwaysInline" => pure (some .alwaysInline)
  | _ => throw s!"lcnf.deserialize: unknown inline attribute {j.compress}"

def decDeclValue (j : Json) : DecodeM (DeclValue .pure) := do
  match ← untag j "decl value" with
  | ("code", #[c]) => return .code (← decCode c)
  | ("extern", #[e]) => return .extern (← decExternAttrData e)
  | (t, xs) => badShape "decl value" t xs

def field (j : Json) (k : String) : DecodeM Json :=
  match j.getObjVal? k with
  | .ok v => pure v
  | .error _ => throw s!"lcnf.deserialize: declaration is missing field `{k}`"

/-- Decode one mono declaration. -/
def deserializeDecl (j : Json) : DecodeM (Decl .pure) := do
  let keys := match j with
    | .obj kvs => kvs.toArray.map (fun (kv : String × Json) => kv.1)
    | _ => #[]
  let expected := #["inline", "levelParams", "name", "params", "recursive", "safe", "type", "value"]
  unless keys.qsort (· < ·) == expected do
    throw s!"lcnf.deserialize: declaration fields are {keys}, expected exactly {expected}"
  return {
    name := ← decName (← field j "name")
    levelParams := (← (← arr (← field j "levelParams") "level params").mapM decName).toList
    type := ← decExpr (← field j "type")
    params := ← decParams (← field j "params")
    safe := ← bool (← field j "safe") "safe"
    recursive := ← bool (← field j "recursive") "recursive"
    inlineAttr? := ← decInline (← field j "inline")
    value := ← decDeclValue (← field j "value") }

/-! ## The round-trip check -/

/-- Every `Expr` a declaration carries, in a fixed traversal order. `BEq Expr` is alpha
equivalence and ignores binder names and annotations, so the round-trip check also compares these
pairwise with `Expr.equal`, which does not. -/
partial def declExprs (d : Decl .pure) : Array Expr :=
  let acc := d.params.foldl (fun acc p => acc.push p.type) #[d.type]
  match d.value with
  | .code c => code c acc
  | .extern _ => acc
where
  args (as : Array (Arg .pure)) (acc : Array Expr) : Array Expr :=
    as.foldl (fun acc a => match a with | .type e _ => acc.push e | _ => acc) acc
  params (ps : Array (Param .pure)) (acc : Array Expr) : Array Expr :=
    ps.foldl (fun acc p => acc.push p.type) acc
  code (c : Code .pure) (acc : Array Expr) : Array Expr :=
    match c with
    | .let d k =>
      let acc := acc.push d.type
      let acc := match d.value with
        | .const _ _ as _ | .fvar _ as => args as acc
        | _ => acc
      code k acc
    | .fun d k _ | .jp d k => code k (code d.value ((params d.params acc).push d.type))
    | .jmp _ as => args as acc
    | .cases cs =>
      cs.alts.foldl (init := acc.push cs.resultType) fun acc alt =>
        match alt with
        | .alt _ ps k _ => code k (params ps acc)
        | .default k => code k acc
    | .return _ => acc
    | .unreach t => acc.push t

/-! ## Documents -/

/-- A versioned IR document: the roots and the ordered declarations of one closure. -/
def serializeDocument (roots : Array Name) (decls : Array (Decl .pure)) : Except String Json :=
  return Json.mkObj [
    ("format", .str formatName),
    ("version", jnat formatVersion),
    ("roots", .arr (roots.map encName)),
    ("decls", .arr (← decls.mapM serializeDecl))]

def deserializeDocument (j : Json) : DecodeM (Array Name × Array (Decl .pure)) := do
  let fmt ← str (← field j "format") "format"
  let ver ← nat (← field j "version") "version"
  unless fmt == formatName && ver == formatVersion do
    throw s!"lcnf.deserialize.version: document is `{fmt}` v{ver}; this reader accepts `{formatName}` v{formatVersion}"
  let roots ← (← arr (← field j "roots") "roots").mapM decName
  let decls ← (← arr (← field j "decls") "decls").mapM deserializeDecl
  return (roots, decls)

/-- `deserialize (serialize d) == d`, with Lean's own `BEq (Decl .pure)` plus `Expr.equal` on every
carried `Expr`, and the decoded value re-serializes to the same bytes. Returns the compressed JSON
on success. -/
def roundTrip (d : Decl .pure) : Except String String := do
  let j ← serializeDecl d
  let bytes := j.compress
  let parsed ← Json.parse bytes
  let d' ← deserializeDecl parsed
  unless d' == d do
    throw s!"lcnf.roundtrip.mismatch: {d.name} does not survive JSON ⇄ LCNF.Code"
  let es := declExprs d
  let es' := declExprs d'
  unless es.size == es'.size && (es.zip es').all (fun (a, b) => a.equal b) do
    throw s!"lcnf.roundtrip.expr: {d.name} loses binder names or annotations in JSON ⇄ LCNF.Code"
  let bytes' := (← serializeDecl d').compress
  unless bytes' == bytes do
    throw s!"lcnf.roundtrip.bytes: {d.name} re-serializes to different bytes"
  return bytes

end TSLean.Lcnf.Serialize

end
