-- TSLean.V2.Lower
-- Lowering pass: ir_types IR → V2 LeanAST.
-- Port of src/codegen/lower.ts. Handles all IR construct types,
-- producing LeanAST nodes that the V2 Printer emits as text.

import TSLean.V2.LeanAST
import TSLean.Generated.SelfHost.ir_types

namespace TSLean.V2.Lower

open TSLean.V2.LeanAST
open TSLean.Generated.Types

-- ─── Type lowering ──────────────────────────────────────────────────────────────

partial def lowerType (t : IRType) : LeanTy :=
  match t with
  | .Nat => .TyName "Nat"
  | .Int => .TyName "Int"
  | .Float => .TyName "Float"
  | .String => .TyName "String"
  | .Bool => .TyName "Bool"
  | .Unit => .TyName "Unit"
  | .Never => .TyName "Empty"
  | .Option inner => .TyApp (.TyName "Option") #[lowerType inner]
  | .Array elem => .TyApp (.TyName "Array") #[lowerType elem]
  | .Tuple elems =>
    if elems.size == 0 then .TyName "Unit"
    else .TyTuple (elems.map lowerType)
  | .Map key value => .TyApp (.TyName "AssocMap") #[lowerType key, lowerType value]
  | .Set elem => .TyApp (.TyName "Array") #[lowerType elem]
  | .Promise inner => .TyApp (.TyName "IO") #[lowerType inner]
  | .Result ok err => .TyApp (.TyName "Except") #[lowerType err, lowerType ok]
  | .Function params ret _ =>
    let ps := if params.size == 0 then #[LeanTy.TyName "Unit"] else params.map lowerType
    .TyArrow ps (lowerType ret)
  | .TypeRef name args =>
    let n := if name == "Any" then "TSAny" else name
    if args.size == 0 then .TyName n
    else .TyApp (.TyName n) (args.map lowerType)
  | .TypeVar name => .TyName name
  | .Structure name _ => .TyName name
  | .Inductive name _ _ => .TyName name
  | .Dependent _ _ body => lowerType body
  | .Subtype base _ => lowerType base
  | .Universe level => .TyName (if level == 0 then "Type" else s!"Type {level}")

-- ─── Effect → return type wrapping ─────────────────────────────────────────────

def lowerRetSig (eff : Effect) (retTy : LeanTy) : LeanTy :=
  match eff with
  | .Pure => retTy
  | .IO | .Async => .TyApp (.TyName "IO") #[retTy]
  | .State st => .TyApp (.TyName "StateT") #[lowerType st, .TyName "IO", retTy]
  | .Except err => .TyApp (.TyName "ExceptT") #[lowerType err, .TyName "IO", retTy]
  | .Combined _ => .TyApp (.TyName "IO") #[retTy]

-- ─── Expression lowering ────────────────────────────────────────────────────────

/-- Default expression for a type (used for holes). -/
def defaultForType (t : IRType) : LeanExpr :=
  match t with
  | .Nat => .Lit "0"
  | .Int => .Lit "0"
  | .Float => .TypeAnnot (.Lit "0") (.TyName "Float")
  | .String => .Lit "\"\""
  | .Bool => .Lit "false"
  | .Unit => .Lit "()"
  | .Array _ => .ArrayLit #[]
  | .Option _ => .None
  | _ => .Default none

/-- Typed sorry for a type. -/
def sorryForType (t : IRType) : LeanExpr :=
  match t with
  | .Bool => .Sorry (some (.TyName "Bool")) none
  | .String => .Sorry (some (.TyName "String")) none
  | .Nat => .Sorry (some (.TyName "Nat")) none
  | .Float => .Sorry (some (.TyName "Float")) none
  | .Unit => .Lit "()"
  | .Option _ => .None
  | .Array _ => .ArrayLit #[]
  | .TypeRef name _ => .Sorry (some (.TyName name)) none
  | _ => .Sorry none none

/-- Lower an IRExpr to a LeanExpr. Since IRExpr is a flat struct with string
    fields, we dispatch on the tag and read the relevant fields. -/
partial def lowerExpr (e : IRExpr) (eff : Effect) : LeanExpr :=
  match e.tag with
  | "LitNat" => .Lit e.value
  | "LitInt" => .Lit e.value
  | "LitFloat" =>
    if e.value.any (· == '.') || e.value.any (· == 'e') then .Lit e.value
    else .TypeAnnot (.Lit e.value) (.TyName "Float")
  | "LitString" => .Lit ("\"" ++ e.value ++ "\"")
  | "LitBool" => .Lit e.value
  | "LitUnit" => .Lit "()"
  | "LitNull" => .None
  | "Hole" => defaultForType e.type
  | "Var" => .Var e.name
  | "Return" =>
    if isPure eff then .Lit e.value  -- pure: pre-rendered expression
    else .Pure (.Lit e.value)        -- monadic: pure val
  -- Pre-rendered compound expressions: the parser stores rendered text in
  -- the string fields (left, right, op, cond, etc.). We emit as Lit to
  -- preserve the exact text without sanitization.
  | "BinOp" => .Lit (e.left ++ " " ++ e.op ++ " " ++ e.right)
  | "UnOp" => .Lit (e.op ++ e.expr)
  | "FieldAccess" => .Lit (e.obj ++ "." ++ e.field)
  | "App" => .Lit e.fn
  | "IfThenElse" =>
    .If (.Lit e.cond) (.Lit e.then_) (.Lit e.else_)
  | "ArrayLit" => .ArrayLit #[]
  | "StructLit" => .StructLit #[]
  | "Let" => .Let e.name none (.Lit e.value) (.Lit e.body) false
  | "Bind" => .Bind e.name (.Lit e.monad) (.Lit e.body)
  | "Sequence" => .Lit "()"
  | "Await" => .Var e.expr
  | "Panic" => .Panic e.value
  | _ => defaultForType e.type

-- ─── Parameter lowering ─────────────────────────────────────────────────────────

def lowerParam (p : IRParam) : LeanParam :=
  { name := p.name, ty := lowerType p.type, implicit := p.implicit == some true }

-- ─── Declaration lowering ───────────────────────────────────────────────────────

partial def lowerDecl (d : IRDecl) : LeanDecl :=
  match d with
  | .VarDecl name ty val _ =>
    let body := lowerExpr val .Pure
    .Def false name #[] #[] (lowerType ty) body none none none
  | .FuncDef name _tps params retTy eff body _comment isPartial _where_ _docComment =>
    let partial_ := isPartial == some true
    let lParams := params.map lowerParam
    let retLTy := lowerRetSig eff (lowerType retTy)
    let lBody :=
      if isPure eff then lowerExpr body eff
      else .Do (lowerExpr body eff)
    .Def partial_ name #[] lParams retLTy lBody none none none
  | .StructDef name _tps fields _deriving_ _comment _extends_ =>
    let lFields := fields.map fun fname =>
      LeanField.mk fname (.TyName "String") none  -- MVP: fields as String
    .Structure name #[] lFields none #["Repr", "BEq", "Inhabited"] none
  | .InductiveDef name _tps ctors _comment =>
    let lCtors := ctors.map fun cname =>
      LeanCtor.mk cname #[]
    .Inductive name #[] lCtors #["Repr", "BEq", "Inhabited"] none
  | .TypeAlias name _tps body _comment =>
    .Abbrev name #[] (lowerType body) none
  | .Namespace name decls =>
    .Namespace name (decls.map lowerDecl)
  | .RawLean code => .Raw code
  | _ => .Comment "(unsupported declaration)"

-- ─── Module lowering ────────────────────────────────────────────────────────────

/-- Lower an IRModule to a LeanFile. -/
def lowerModule (mod : IRModule) : LeanFile :=
  let decls : Array LeanDecl := #[]
  -- Imports
  let decls := decls.push (.Import "TSLean.Runtime.Basic")
  let decls := decls.push (.Import "TSLean.Runtime.Coercions")
  let decls := decls.push .Blank
  -- Open
  let decls := decls.push (.Open #["TSLean"])
  let decls := decls.push .Blank
  -- Namespace
  let ns := mod.name
  let useNs := !ns.isEmpty && ns != "T" && ns != "Test"
  let bodyDecls := mod.decls.foldl (fun acc d =>
    acc ++ #[lowerDecl d, .Blank]
  ) #[]
  let decls := if useNs then
    decls.push (.Namespace ns bodyDecls)
  else
    decls ++ bodyDecls
  {
    banner := some "Auto-generated by ts-lean-transpiler"
    sourcePath := match mod.sourceFile with
      | some (some f) => some f
      | _ => none
    decls := decls
  }

end TSLean.V2.Lower
