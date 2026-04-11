-- TSLean.V2.FromJSON
-- Direct JSON AST → V2 LeanAST lowering.
-- Bypasses the flat ir_types IR to preserve full type/field information
-- from the JSON AST. Produces LeanAST nodes that the V2 Printer emits
-- as text identical to the TS pipeline's output.

import Lean.Data.Json
import TSLean.JsonAST
import TSLean.V2.LeanAST

namespace TSLean.V2.FromJSON

open Lean
open TSLean.JsonAST
open TSLean.V2.LeanAST

-- ─── Helpers ────────────────────────────────────────────────────────────────────

private def DEFAULT_DERIVING : Array String := #["Repr", "BEq", "Inhabited"]

/-- Convert a file path to a module name. -/
private def fileToModuleName (filePath : String) : String :=
  let parts := filePath.splitOn "/"
  let base := (parts.getLast?.getD "unknown").replace ".ts" "" |>.replace ".tsx" ""
  -- CamelCase: capitalize first letter, remove hyphens
  let segments := base.splitOn "-"
  let capitalized := segments.map fun s =>
    if s.isEmpty then s
    else s.set ⟨0⟩ (s.get ⟨0⟩ |>.toUpper)
  let name := String.join capitalized
  s!"TSLean.Generated.{name}"

-- ─── Type mapping ───────────────────────────────────────────────────────────────

/-- Map resolved type flags from JSON to a LeanTy. -/
private def mapTypeFromFlags (flags : Nat) (name : String) : LeanTy :=
  if flags &&& TF_StringLiteral != 0 then .TyName "String"
  else if flags &&& TF_NumberLiteral != 0 then .TyName "Float"
  else if flags &&& TF_BooleanLiteral != 0 then .TyName "Bool"
  else if flags &&& TF_String != 0 then .TyName "String"
  else if flags &&& TF_Number != 0 then .TyName "Float"
  else if flags &&& TF_Boolean != 0 then .TyName "Bool"
  else if flags &&& TF_Void != 0 then .TyName "Unit"
  else if flags &&& TF_Undefined != 0 then .TyApp (.TyName "Option") #[.TyName "Unit"]
  else if flags &&& TF_Null != 0 then .TyApp (.TyName "Option") #[.TyName "Unit"]
  else if flags &&& TF_Never != 0 then .TyName "Empty"
  else if flags &&& TF_BigInt != 0 then .TyName "Int"
  else if flags &&& TF_Any != 0 || flags &&& TF_Unknown != 0 then .TyName "TSAny"
  else if name == "number" then .TyName "Float"
  else if name == "string" then .TyName "String"
  else if name == "boolean" then .TyName "Bool"
  else if name == "void" then .TyName "Unit"
  else if name == "never" then .TyName "Empty"
  else if name.isEmpty then .TyName "Unit"
  else .TyName name

/-- Map a resolved type JSON to a LeanTy. -/
private def mapResolvedType (j : Json) : LeanTy :=
  match resolvedType j with
  | some rt => mapTypeFromFlags (typeFlags rt) (typeName rt)
  | none => .TyName "Unit"

/-- Map a type annotation node to LeanTy. -/
private partial def mapTypeNode (j : Json) : LeanTy :=
  let kind := nodeKind j
  if kind == "NumberKeyword" then .TyName "Float"
  else if kind == "StringKeyword" then .TyName "String"
  else if kind == "BooleanKeyword" then .TyName "Bool"
  else if kind == "VoidKeyword" then .TyName "Unit"
  else if kind == "NeverKeyword" then .TyName "Empty"
  else if kind == "AnyKeyword" then .TyName "TSAny"
  else if kind == "UndefinedKeyword" then .TyApp (.TyName "Option") #[.TyName "Unit"]
  else if kind == "ArrayType" then
    let elem := (fieldNode j "elementType").map mapTypeNode |>.getD (.TyName "Unit")
    .TyApp (.TyName "Array") #[elem]
  else if kind == "TypeReference" then
    let name := (fieldNode j "typeName").bind (fun tn => fieldNode tn "text" |>.bind getStr)
      |>.getD ((fieldNode j "name").bind (fun n => getStr n) |>.getD (nodeText j))
    if name.isEmpty then mapResolvedType j else .TyName name
  else if kind == "UnionType" then
    let types := fieldArr j "types"
    let nonUndef := types.filter (fun t =>
      nodeKind t != "UndefinedKeyword" && nodeKind t != "NullKeyword" &&
      nodeKind t != "LiteralType")
    if nonUndef.size == 1 && nonUndef.size < types.size then
      .TyApp (.TyName "Option") #[mapTypeNode (nonUndef.getD 0 default)]
    else mapResolvedType j
  else if kind == "FunctionType" then
    let params := (fieldArr j "parameters").map fun p =>
      (fieldNode p "type").map mapTypeNode |>.getD (.TyName "Unit")
    let ret := (fieldNode j "type").map mapTypeNode |>.getD (.TyName "Unit")
    .TyArrow params ret
  else if kind == "TupleType" then
    let elems := (fieldArr j "elements").map mapTypeNode
    if elems.size == 0 then .TyName "Unit"
    else .TyTuple elems
  else if kind == "ParenthesizedType" then
    (fieldNode j "type").map mapTypeNode |>.getD (.TyName "Unit")
  else if kind == "LiteralType" then mapResolvedType j
  else mapResolvedType j

-- ─── Expression lowering ────────────────────────────────────────────────────────

/-- Render a JSON expression node to Lean text directly. -/
private partial def renderExpr (j : Json) : String :=
  let kind := nodeKind j
  if kind == "NumericLiteral" then nodeText j
  else if kind == "StringLiteral" then "\"" ++ nodeText j ++ "\""
  else if kind == "TrueKeyword" then "true"
  else if kind == "FalseKeyword" then "false"
  else if kind == "NullKeyword" || kind == "UndefinedKeyword" then "none"
  else if kind == "Identifier" then nodeText j
  else if kind == "ThisKeyword" then "self"
  else if kind == "BinaryExpression" then
    let left := (fieldNode j "left").map renderExpr |>.getD "default"
    let right := (fieldNode j "right").map renderExpr |>.getD "default"
    let opKind := (fieldNode j "operatorToken").map nodeKind |>.getD ""
    let op := mapBinOpSymbol opKind
    left ++ " " ++ op ++ " " ++ right
  else if kind == "PropertyAccessExpression" then
    let obj := (fieldNode j "expression").map renderExpr |>.getD "default"
    let field := (fieldNode j "name").map nodeText |>.getD ""
    obj ++ "." ++ field
  else if kind == "CallExpression" then
    let fn := (fieldNode j "expression").map renderExpr |>.getD "default"
    let args := (fieldArr j "arguments").map renderExpr
    if args.size == 0 then fn
    else fn ++ " " ++ String.intercalate " " args.toList
  else if kind == "ReturnStatement" then
    (fieldNode j "expression").map renderExpr |>.getD "()"
  else if kind == "PrefixUnaryExpression" then
    let operand := (fieldNode j "operand").map renderExpr |>.getD "default"
    let opCode := fieldNat j "operator"
    let op := if opCode == 53 then "!" else if opCode == 40 then "-" else "!"
    op ++ operand
  else if kind == "ParenthesizedExpression" then
    "(" ++ ((fieldNode j "expression").map renderExpr |>.getD "default") ++ ")"
  else if kind == "ConditionalExpression" then
    let cond := (fieldNode j "expression").map renderExpr |>.getD "default"
    let t := (fieldNode j "whenTrue").map renderExpr |>.getD "default"
    let f := (fieldNode j "whenFalse").map renderExpr |>.getD "default"
    s!"if {cond} then {t} else {f}"
  else if kind == "TemplateExpression" then
    let headText := (fieldNode j "head").map nodeText |>.getD ""
    let spans := fieldArr j "templateSpans"
    let parts := spans.foldl (fun acc span =>
      let expr := (fieldNode span "expression").map renderExpr |>.getD ""
      let lit := (fieldNode span "literal").map nodeText |>.getD ""
      acc ++ "{" ++ expr ++ "}" ++ lit
    ) headText
    "s!\"" ++ parts ++ "\""
  else if kind == "NoSubstitutionTemplateLiteral" then
    "\"" ++ nodeText j ++ "\""
  else if kind == "ArrayLiteralExpression" then
    let elems := (fieldArr j "elements").map renderExpr
    "#[" ++ String.intercalate ", " elems.toList ++ "]"
  else if kind == "AwaitExpression" then
    (fieldNode j "expression").map renderExpr |>.getD "default"
  else "default"
where
  mapBinOpSymbol (kind : String) : String := match kind with
    | "PlusToken" => "+"
    | "MinusToken" => "-"
    | "AsteriskToken" => "*"
    | "SlashToken" => "/"
    | "PercentToken" => "%"
    | "EqualsEqualsToken" | "EqualsEqualsEqualsToken" => "=="
    | "ExclamationEqualsToken" | "ExclamationEqualsEqualsToken" => "!="
    | "LessThanToken" => "<"
    | "LessThanEqualsToken" => "<="
    | "GreaterThanToken" => ">"
    | "GreaterThanEqualsToken" => ">="
    | "AmpersandAmpersandToken" => "&&"
    | "BarBarToken" => "||"
    | "BarBarEqualsToken" => "||="
    | _ => "+"

/-- Lower a JSON expression node to a LeanExpr. -/
private partial def lowerExpr (j : Json) : LeanExpr :=
  .Lit (renderExpr j)

/-- Lower a function body (Block or expression) to a LeanExpr. -/
private partial def lowerBody (j : Json) : LeanExpr :=
  if isBlock j then
    let stmts := fieldArr j "statements"
    if stmts.size == 0 then .Lit "()"
    else if stmts.size == 1 then lowerBlockStmt (stmts.getD 0 default)
    else
      -- Multiple statements: render as let-chain or sequence
      let rendered := stmts.map fun s => renderExpr s
      .Lit (String.intercalate "\n" rendered.toList)
  else lowerExpr j
where
  lowerBlockStmt (j : Json) : LeanExpr :=
    let kind := nodeKind j
    if kind == "ReturnStatement" then
      .Lit ((fieldNode j "expression").map renderExpr |>.getD "()")
    else .Lit (renderExpr j)

-- ─── Declaration lowering ───────────────────────────────────────────────────────

/-- Extract type parameters from a JSON declaration node. -/
private def extractTypeParams (j : Json) : Array LeanTyParam :=
  (fieldArr j "typeParameters").map fun tp =>
    { name := nodeText tp, explicit := true, constraints := none : LeanTyParam }

/-- Lower a parameter node. -/
private def lowerParam (j : Json) : LeanParam :=
  let name := (fieldNode j "name").map nodeText |>.getD "_"
  let ty := match fieldNode j "type" with
    | some tn => mapTypeNode tn
    | none => mapResolvedType j
  { name := name, ty := ty }

-- Variable statement: const x: T = expr
private partial def lowerVarStatement (j : Json) : Array LeanDecl :=
  let declList := fieldNode j "declarationList"
  let decls := declList.map (fieldArr · "declarations") |>.getD #[]
  let flags := declList.map (fun dl => fieldNat dl "flags") |>.getD 0
  let _isConst := flags &&& NF_Const != 0
  decls.filterMap fun d =>
    let name := (fieldNode d "name").map nodeText |>.getD "_"
    let ty := match fieldNode d "type" with
      | some tn => mapTypeNode tn
      | none => mapResolvedType d
    let body := match fieldNode d "initializer" with
      | some init => lowerExpr init
      | none => .Default (some ty)
    some (.Def false name #[] #[] ty body none none none)

-- Function declaration
private partial def lowerFuncDecl (j : Json) : Array LeanDecl :=
  let name := (fieldNode j "name").map nodeText |>.getD "_"
  let tyParams := extractTypeParams j
  let params := (fieldArr j "parameters").map lowerParam
  let retTy := match fieldNode j "type" with
    | some tn => mapTypeNode tn
    | none => mapResolvedType j
  let body := match fieldNode j "body" with
    | some b => lowerBody b
    | none => .Default (some retTy)
  -- Detect partial: does the body reference the function name?
  let bodyText := match body with | .Lit s => s | _ => ""
  let parts := bodyText.splitOn name
  let isPartial := parts.length > 1
  #[.Def isPartial name tyParams params retTy body none none none]

-- Interface declaration → Structure
private partial def lowerInterfaceDecl (j : Json) : Array LeanDecl :=
  let name := (fieldNode j "name").map nodeText |>.getD "_"
  let tyParams := extractTypeParams j
  let members := fieldArr j "members"
  let fields := members.filterMap fun m =>
    if isPropertySignature m then
      let fname := (fieldNode m "name").map nodeText |>.getD "_"
      let fty := match fieldNode m "type" with
        | some tn => mapTypeNode tn
        | none => mapResolvedType m
      some (LeanField.mk fname fty none)
    else none
  #[.Structure name tyParams fields none DEFAULT_DERIVING none]

-- Class declaration → Structure + Namespace
private partial def lowerClassDecl (j : Json) : Array LeanDecl :=
  let name := (fieldNode j "name").map nodeText |>.getD "_"
  let members := fieldArr j "members"
  let fields := members.filterMap fun m =>
    if isPropertyDeclaration m || isPropertySignature m then
      let fname := (fieldNode m "name").map nodeText |>.getD "_"
      let fty := match fieldNode m "type" with
        | some tn => mapTypeNode tn
        | none => mapResolvedType m
      some (LeanField.mk fname fty none)
    else none
  #[.Structure name #[] fields none DEFAULT_DERIVING none]

-- Type alias → Abbrev
private partial def lowerTypeAliasDecl (j : Json) : Array LeanDecl :=
  let name := (fieldNode j "name").map nodeText |>.getD "_"
  let tyParams := extractTypeParams j
  let body := match fieldNode j "type" with
    | some tn => mapTypeNode tn
    | none => .TyName "Unit"
  #[.Abbrev name tyParams body none]

-- Enum declaration → Inductive
private partial def lowerEnumDecl (j : Json) : Array LeanDecl :=
  let name := (fieldNode j "name").map nodeText |>.getD "_"
  let members := fieldArr j "members"
  let ctors := members.map fun m =>
    let cname := (fieldNode m "name").map nodeText |>.getD "_"
    LeanCtor.mk cname #[]
  #[.Inductive name #[] ctors DEFAULT_DERIVING none]

/-- Lower a top-level JSON statement to LeanDecl(s). -/
private partial def lowerStatement (j : Json) : Array LeanDecl :=
  let kind := nodeKind j
  let comments := fieldArr j "leadingComments"
  let commentDecls := comments.foldl (fun acc c =>
    match getStr c with
    | some text =>
      let stripped := text.replace "//" "" |>.replace "/*" "" |>.replace "*/" "" |>.trim
      if stripped.isEmpty then acc else acc.push (.Comment stripped)
    | none => acc
  ) #[]
  let decls := if kind == "VariableStatement" then lowerVarStatement j
    else if kind == "FunctionDeclaration" then lowerFuncDecl j
    else if kind == "InterfaceDeclaration" then lowerInterfaceDecl j
    else if kind == "ClassDeclaration" then lowerClassDecl j
    else if kind == "TypeAliasDeclaration" then lowerTypeAliasDecl j
    else if kind == "EnumDeclaration" then lowerEnumDecl j
    else #[]
  commentDecls ++ decls

-- ─── Import resolution ──────────────────────────────────────────────────────────

/-- Scan declarations for import needs. -/
private def resolveImports (_json : Json) : Array String :=
  -- Always include base imports; dynamic resolution would scan for
  -- HashMap, WebAPI, Monad usage
  #["TSLean.Runtime.Basic", "TSLean.Runtime.Coercions"]

-- ─── Module lowering ────────────────────────────────────────────────────────────

/-- Lower a full JSON AST to a LeanFile. -/
def lowerJsonModule (json : Json) : LeanFile :=
  let fileName := fieldStr json "fileName"
  let ns := fileToModuleName fileName
  let stmts := fieldArr json "statements"

  let imports := resolveImports json
  let decls : Array LeanDecl := #[]
  let decls := imports.foldl (fun acc imp => acc.push (.Import imp)) decls
  let decls := decls.push .Blank
  let decls := decls.push (.Open #["TSLean"])
  let decls := decls.push .Blank

  let bodyDecls := stmts.foldl (fun acc s =>
    let ds := lowerStatement s
    if ds.isEmpty then acc
    else acc ++ ds ++ #[.Blank]
  ) #[]

  let useNs := !ns.isEmpty && ns != "T" && ns != "Test"
  let decls := if useNs then
    decls.push (.Namespace ns bodyDecls)
  else
    decls ++ bodyDecls

  {
    banner := some "Auto-generated by ts-lean-transpiler"
    sourcePath := some fileName
    decls := decls
  }

end TSLean.V2.FromJSON
