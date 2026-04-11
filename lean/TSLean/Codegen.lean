-- TSLean.Codegen
-- Lean-native code generator: IRModule → Lean 4 source text.
-- Simplified implementation for the MVP — handles basic constructs:
-- VarDecl, FuncDef, StructDef, InductiveDef, TypeAlias.

import TSLean.Generated.SelfHost.ir_types

namespace TSLean.Codegen

open TSLean.Generated.Types

-- ─── Type emission ──────────────────────────────────────────────────────────────

/-- Convert an IRType to its Lean 4 string representation. -/
partial def irTypeToLean (t : IRType) (parens : Bool := false) : String :=
  let s := match t with
    | .Nat => "Nat"
    | .Int => "Int"
    | .Float => "Float"
    | .String => "String"
    | .Bool => "Bool"
    | .Unit => "Unit"
    | .Never => "Empty"
    | .Option inner => "Option " ++ irTypeToLean inner true
    | .Array elem => "Array " ++ irTypeToLean elem true
    | .Tuple elems =>
      if elems.size == 0 then "Unit"
      else "(" ++ String.intercalate " × " (elems.toList.map (irTypeToLean · false)) ++ ")"
    | .Function params ret _ =>
      let pStr := if params.size == 0 then "Unit"
        else String.intercalate " → " (params.toList.map (irTypeToLean · true))
      pStr ++ " → " ++ irTypeToLean ret false
    | .Map key value => "AssocMap " ++ irTypeToLean key true ++ " " ++ irTypeToLean value true
    | .Set elem => "Array " ++ irTypeToLean elem true
    | .Promise inner => "IO " ++ irTypeToLean inner true
    | .Result ok err => "Except " ++ irTypeToLean err true ++ " " ++ irTypeToLean ok true
    | .TypeRef name args =>
      if args.size == 0 then name
      else "(" ++ name ++ " " ++ String.intercalate " " (args.toList.map (irTypeToLean · true)) ++ ")"
    | .TypeVar name => name
    | .Structure name _ => name
    | .Inductive name _ _ => name
    | .Dependent _ _ body => irTypeToLean body false
    | .Subtype base _ => irTypeToLean base false
    | .Universe level => if level == 0 then "Type" else s!"Type {level}"
  if parens && (s.any (· == ' ') || s.any (· == '→')) then "(" ++ s ++ ")" else s

-- ─── Expression emission ────────────────────────────────────────────────────────

/-- Convert an IRExpr to its Lean 4 string representation. -/
partial def exprToLean (e : IRExpr) (indent : String := "  ") : String :=
  match e.tag with
  | "LitNat" => e.value
  | "LitInt" => e.value
  | "LitFloat" =>
    if e.value.contains '.' || e.value.contains 'e' then e.value
    else "(" ++ e.value ++ " : Float)"
  | "LitString" => "\"" ++ e.value ++ "\""
  | "LitBool" => e.value
  | "LitUnit" => "()"
  | "LitNull" => "none"
  | "Var" => sanitize e.name
  | "Hole" => defaultForType e.type
  | "Return" => e.value
  | "BinOp" =>
    -- op field already contains the rendered symbol (+, -, ==, etc.)
    e.left ++ " " ++ e.op ++ " " ++ e.right
  | "UnOp" =>
    if e.op == "Not" then "!" ++ e.expr
    else if e.op == "Neg" then "-" ++ e.expr
    else "~~~" ++ e.expr
  | "FieldAccess" => e.obj ++ "." ++ sanitize e.field
  | "App" => e.fn ++ " " ++ e.args
  | "IfThenElse" =>
    indent ++ "if " ++ e.cond ++ " then\n" ++
    indent ++ "    " ++ e.then_ ++ "\n" ++
    indent ++ "  else\n" ++
    indent ++ "    " ++ e.else_
  | "ArrayLit" => "#[]"
  | "StructLit" => "{ }"
  | "Let" => indent ++ "let " ++ sanitize e.name ++ " := " ++ e.value ++ "\n" ++ indent ++ e.body
  | "Sequence" => "()"
  | "Await" => e.expr
  | _ => defaultForType e.type
where
  sanitize (name : String) : String :=
    let kws := #["def","fun","let","in","if","then","else","match","with","do",
      "return","where","have","show","from","by","class","instance","structure",
      "inductive","namespace","end","open","import","theorem"]
    if kws.any (· == name) then "«" ++ name ++ "»" else name
  defaultForType (t : IRType) : String := match t with
    | .Nat => "0" | .Int => "0" | .Float => "(0 : Float)"
    | .String => "\"\"" | .Bool => "false" | .Unit => "()"
    | .Array _ => "#[]" | .Option _ => "none"
    | _ => "default"
  mapBinOp (op : String) (ty : IRType) : String := match op with
    | "Add" => if ty == .String then "++" else "+"
    | "Sub" => "-" | "Mul" => "*" | "Div" => "/" | "Mod" => "%"
    | "Eq" => "==" | "Ne" => "!=" | "Lt" => "<" | "Le" => "<="
    | "Gt" => ">" | "Ge" => ">=" | "And" => "&&" | "Or" => "||"
    | "Concat" => "++" | _ => "+"

-- ─── Declaration emission ───────────────────────────────────────────────────────

/-- Convert an IRDecl to Lean 4 source text. -/
partial def declToLean (d : IRDecl) : String :=
  match d with
  | .VarDecl name ty val _ =>
    let tyStr := irTypeToLean ty
    let valStr := exprToLean val
    s!"def {sanitize name} : {tyStr} := {valStr}"
  | .FuncDef name _ params retTy _ body _ isPartial _ _ =>
    let kw := if isPartial == some true then "partial def" else "def"
    let paramStr := String.intercalate " " (params.toList.map fun p =>
      s!"({sanitize p.name} : {irTypeToLean p.type})")
    let retStr := irTypeToLean retTy
    let bodyStr := exprToLean body
    s!"{kw} {sanitize name} {paramStr} : {retStr} :=\n  {bodyStr}"
  | .StructDef name _ fields _ _ _ =>
    let fieldStr := String.intercalate "\n" (fields.toList.map fun f =>
      s!"  {sanitize f} : String")  -- MVP: all fields typed as String
    s!"structure {name} where\n  mk ::\n{fieldStr}\n  deriving Repr, BEq, Inhabited"
  | .InductiveDef name _ ctors _ =>
    let ctorStr := String.intercalate "\n" (ctors.toList.map fun c =>
      s!"  | {sanitize c}")
    s!"inductive {name} where\n{ctorStr}\n  deriving Repr, BEq, Inhabited"
  | .TypeAlias name _ body _ =>
    s!"abbrev {name} := {irTypeToLean body}"
  | .Namespace name decls =>
    let inner := String.intercalate "\n\n" (decls.toList.map declToLean)
    s!"namespace {name}\n\n{inner}\n\nend {name}"
  | .RawLean code => code
  | _ => s!"-- (unsupported declaration)"
where
  sanitize (name : String) : String :=
    let kws := #["def","fun","let","in","if","then","else","match","with","do",
      "return","where","have","show","from","by","class","instance","structure",
      "inductive","namespace","end","open","import","theorem"]
    if kws.any (· == name) then "«" ++ name ++ "»" else name

-- ─── Module emission ────────────────────────────────────────────────────────────

/-- Generate a complete Lean 4 file from an IRModule. -/
def generateLean (mod : IRModule) : String :=
  let banner := "-- Auto-generated by TSLean (Lean-native transpiler)\n"
  let source := match mod.sourceFile with
    | some (some f) => s!"-- Source: {f}\n"
    | _ => ""
  let imports := "import TSLean.Runtime.Basic\nimport TSLean.Runtime.Coercions\n"
  let openNs := "\nopen TSLean\n"
  let nsName := mod.name
  let declsStr := String.intercalate "\n\n" (mod.decls.toList.map declToLean)
  let body := if nsName.isEmpty then declsStr
    else s!"\nnamespace {nsName}\n\n{declsStr}\n\nend {nsName}"
  banner ++ source ++ "\n" ++ imports ++ openNs ++ body ++ "\n"

end TSLean.Codegen
