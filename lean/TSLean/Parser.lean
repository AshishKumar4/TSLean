-- TSLean.Parser
-- Lean-native parser: JSON AST → IR types.
-- Reads JSON-serialized TS AST (from tsc-to-json.ts) and produces
-- IRModule / IRDecl / IRExpr values that the codegen can consume.

import Lean.Data.Json
import TSLean.JsonAST
import TSLean.Generated.SelfHost.ir_types

namespace TSLean.Parser

open Lean
open TSLean.JsonAST
open TSLean.Generated.Types

-- ─── Type mapping ───────────────────────────────────────────────────────────────

/-- Map resolved TypeFlags from the JSON to an IRType. -/
def mapTypeFromFlags (flags : Nat) (name : String) : IRType :=
  -- Check flags in priority order (matching the TS parser's mapType)
  if flags &&& TF_StringLiteral != 0 then TyString
  else if flags &&& TF_NumberLiteral != 0 then TyFloat
  else if flags &&& TF_BooleanLiteral != 0 then TyBool
  else if flags &&& TF_String != 0 then TyString
  else if flags &&& TF_Number != 0 then TyFloat
  else if flags &&& TF_Boolean != 0 then TyBool
  else if flags &&& TF_Void != 0 then TyUnit
  else if flags &&& TF_Undefined != 0 then .Option TyUnit
  else if flags &&& TF_Null != 0 then .Option TyUnit
  else if flags &&& TF_Never != 0 then TyNever
  else if flags &&& TF_BigInt != 0 then TyInt
  else if flags &&& TF_Any != 0 then TyRef "TSAny"
  else if flags &&& TF_Unknown != 0 then TyRef "TSAny"
  -- For object/union/intersection types, use the name
  else if name == "number" then TyFloat
  else if name == "string" then TyString
  else if name == "boolean" then TyBool
  else if name == "void" then TyUnit
  else if name == "never" then TyNever
  else if name == "any" then TyRef "TSAny"
  else if name == "unknown" then TyRef "TSAny"
  else if name.isEmpty then TyUnit
  else TyRef name

/-- Map a resolved type JSON to an IRType. -/
def mapResolvedType (j : Json) : IRType :=
  match resolvedType j with
  | some rt =>
    let flags := typeFlags rt
    let name := typeName rt
    mapTypeFromFlags flags name
  | none => TyUnit

/-- Map a type-annotation node (NumberKeyword, StringKeyword, etc.) to IRType. -/
partial def mapTypeNode (j : Json) : IRType :=
  let kind := nodeKind j
  if kind == "NumberKeyword" then TyFloat
  else if kind == "StringKeyword" then TyString
  else if kind == "BooleanKeyword" then TyBool
  else if kind == "VoidKeyword" then TyUnit
  else if kind == "NeverKeyword" then TyNever
  else if kind == "AnyKeyword" then TyRef "TSAny"
  else if kind == "UndefinedKeyword" then .Option TyUnit
  else if kind == "TypeReference" then
    let name := (fieldNode j "typeName").map (fieldStr · "text") |>.getD (nodeText j)
    -- Check for known container types
    if name.isEmpty then mapResolvedType j else TyRef name
  else if kind == "ArrayType" then
    let elem := (fieldNode j "elementType").map mapTypeNode |>.getD TyUnit
    TyArray elem
  else if kind == "UnionType" then
    -- Simplify: if it's T | undefined → Option T
    let types := fieldArr j "types"
    let nonUndef := types.filter (fun t => nodeKind t != "UndefinedKeyword" && nodeKind t != "NullKeyword")
    if nonUndef.size == 1 && nonUndef.size < types.size then
      .Option (mapTypeNode (nonUndef.getD 0 default))
    else mapResolvedType j
  else mapResolvedType j

-- ─── Expression parsing ─────────────────────────────────────────────────────────

/-- Parse a JSON AST expression node into an IRExpr. -/
partial def parseExpr (j : Json) : IRExpr :=
  let kind := nodeKind j
  let ty := mapResolvedType j
  -- Numeric literal
  if kind == "NumericLiteral" then
    let text := nodeText j
    let isInt := !text.contains '.' && !text.contains 'e' && !text.contains 'E'
    if isInt then
      match text.toNat? with
      | some n => { tag := "LitNat", value := text, type := TyNat, effect := Pure }
      | none => { tag := "LitFloat", value := text, type := TyFloat, effect := Pure }
    else { tag := "LitFloat", value := text, type := TyFloat, effect := Pure }
  -- String literal
  else if kind == "StringLiteral" || kind == "NoSubstitutionTemplateLiteral" then
    { tag := "LitString", value := nodeText j, type := TyString, effect := Pure }
  -- Boolean literals
  else if kind == "TrueKeyword" then
    { tag := "LitBool", value := "true", type := TyBool, effect := Pure }
  else if kind == "FalseKeyword" then
    { tag := "LitBool", value := "false", type := TyBool, effect := Pure }
  -- Null/undefined
  else if kind == "NullKeyword" || kind == "UndefinedKeyword" then
    { tag := "LitNull", type := .Option TyUnit, effect := Pure }
  -- Identifier
  else if kind == "Identifier" then
    { tag := "Var", name := nodeText j, type := ty, effect := Pure }
  -- This keyword
  else if kind == "ThisKeyword" then
    { tag := "Var", name := "self", type := ty, effect := Pure }
  -- Binary expression
  else if kind == "BinaryExpression" then
    let left := (fieldNode j "left").map parseExpr |>.getD default
    let right := (fieldNode j "right").map parseExpr |>.getD default
    let opKind := (fieldNode j "operatorToken").map (fun t => nodeKind t) |>.getD ""
    let op := mapBinOp opKind
    { tag := "BinOp", op := op, left := left.tag, right := right.tag, type := ty, effect := Pure }
  -- Property access: x.y
  else if kind == "PropertyAccessExpression" then
    let obj := (fieldNode j "expression").map parseExpr |>.getD default
    let field := (fieldNode j "name").map nodeText |>.getD ""
    { tag := "FieldAccess", obj := obj.tag, field := field, type := ty, effect := Pure }
  -- Call expression: f(x, y)
  else if kind == "CallExpression" then
    let fn := (fieldNode j "expression").map parseExpr |>.getD default
    { tag := "App", fn := fn.tag, type := ty, effect := Pure }
  -- Return statement
  else if kind == "ReturnStatement" then
    let val := (fieldNode j "expression").map parseExpr |>.getD litUnit
    { tag := "Return", value := val.tag, type := val.type, effect := val.effect }
  -- Parenthesized
  else if kind == "ParenthesizedExpression" then
    (fieldNode j "expression").map parseExpr |>.getD default
  -- Array literal
  else if kind == "ArrayLiteralExpression" then
    { tag := "ArrayLit", type := ty, effect := Pure }
  -- Object literal
  else if kind == "ObjectLiteralExpression" then
    { tag := "StructLit", type := ty, effect := Pure }
  -- Prefix unary: !x, -x
  else if kind == "PrefixUnaryExpression" then
    let operand := (fieldNode j "operand").map parseExpr |>.getD default
    let opCode := fieldNat j "operator"
    let op := if opCode == 53 then "Not" else if opCode == 40 then "Neg" else "Not"
    { tag := "UnOp", op := op, type := ty, effect := Pure }
  -- Conditional: cond ? a : b
  else if kind == "ConditionalExpression" then
    let cond := (fieldNode j "condition").map parseExpr |>.getD default
    let whenTrue := (fieldNode j "whenTrue").map parseExpr |>.getD default
    let whenFalse := (fieldNode j "whenFalse").map parseExpr |>.getD default
    { tag := "IfThenElse", cond := cond.tag, then_ := whenTrue.tag,
      else_ := whenFalse.tag, type := ty, effect := Pure }
  -- Template expression: `hello ${name}`
  else if kind == "TemplateExpression" then
    { tag := "LitString", value := "(template)", type := TyString, effect := Pure }
  -- Await
  else if kind == "AwaitExpression" then
    let inner := (fieldNode j "expression").map parseExpr |>.getD default
    { tag := "Await", expr := inner.tag, type := ty, effect := Effect.Async }
  -- Default fallback
  else { tag := "Hole", type := ty, effect := Pure }
where
  mapBinOp (kind : String) : String := match kind with
    | "PlusToken" => "Add"
    | "MinusToken" => "Sub"
    | "AsteriskToken" => "Mul"
    | "SlashToken" => "Div"
    | "PercentToken" => "Mod"
    | "EqualsEqualsToken" | "EqualsEqualsEqualsToken" => "Eq"
    | "ExclamationEqualsToken" | "ExclamationEqualsEqualsToken" => "Ne"
    | "LessThanToken" => "Lt"
    | "LessThanEqualsToken" => "Le"
    | "GreaterThanToken" => "Gt"
    | "GreaterThanEqualsToken" => "Ge"
    | "AmpersandAmpersandToken" => "And"
    | "BarBarToken" => "Or"
    | _ => "Add"

-- ─── Statement parsing ──────────────────────────────────────────────────────────

/-- Parse a block body (array of statements) into an IRExpr sequence. -/
partial def parseBlock (j : Json) : IRExpr :=
  let stmts := fieldArr j "statements"
  if stmts.size == 0 then litUnit
  else if stmts.size == 1 then parseBlockStmt (stmts.getD 0 default)
  else
    -- Build a let-chain: each statement binds to _ except the last
    let last := parseBlockStmt (stmts.getD (stmts.size - 1) default)
    last
where
  parseBlockStmt (j : Json) : IRExpr :=
    let kind := nodeKind j
    if kind == "ReturnStatement" then
      let val := (fieldNode j "expression").map parseExpr |>.getD litUnit
      { tag := "Return", value := val.tag, type := val.type, effect := val.effect }
    else if kind == "ExpressionStatement" then
      (fieldNode j "expression").map parseExpr |>.getD litUnit
    else if kind == "VariableStatement" then
      -- For blocks, a variable statement inside a function body is complex.
      -- For MVP, just parse the initializer of the first declaration.
      let declList := fieldNode j "declarationList"
      let decls := declList.map (fieldArr · "declarations") |>.getD #[]
      if decls.size > 0 then
        let d := decls.getD 0 default
        let name := (fieldNode d "name").map nodeText |>.getD "_"
        let val := (fieldNode d "initializer").map parseExpr |>.getD (holeExpr TyUnit)
        let ty := mapResolvedType d
        -- Build a let expression (body is the remaining code, simplified to the value)
        { tag := "Let", name := name, value := val.tag, type := ty, effect := Pure }
      else litUnit
    else if kind == "IfStatement" then
      let cond := (fieldNode j "expression").map parseExpr |>.getD default
      let thenBranch := (fieldNode j "thenStatement").map parseBlockOrExpr |>.getD litUnit
      let elseBranch := (fieldNode j "elseStatement").map parseBlockOrExpr |>.getD litUnit
      { tag := "IfThenElse", cond := cond.tag, then_ := thenBranch.tag,
        else_ := elseBranch.tag, type := thenBranch.type, effect := Pure }
    else parseExpr j
  parseBlockOrExpr (j : Json) : IRExpr :=
    if isBlock j then parseBlock j else parseBlockStmt j

-- ─── Parameter parsing ──────────────────────────────────────────────────────────

/-- Parse a function parameter from JSON. -/
def parseParam (j : Json) : IRParam :=
  let name := (fieldNode j "name").map nodeText |>.getD "_"
  let ty := match fieldNode j "type" with
    | some typeNode => mapTypeNode typeNode
    | none => mapResolvedType j
  { name := name, type := ty, implicit := none, default_ := none }

-- ─── Declaration parsing ────────────────────────────────────────────────────────

/-- Parse a top-level statement from JSON AST into an IRDecl. -/
partial def parseStatement (j : Json) : Option IRDecl :=
  let kind := nodeKind j
  -- Variable statement: const x: T = expr
  if kind == "VariableStatement" then
    let declList := fieldNode j "declarationList"
    let decls := declList.map (fieldArr · "declarations") |>.getD #[]
    let flags := declList.map (fun dl => fieldNat dl "flags") |>.getD 0
    let isConst := flags &&& NF_Const != 0
    if decls.size > 0 then
      let d := decls.getD 0 default
      let name := (fieldNode d "name").map nodeText |>.getD "_"
      let ty := match fieldNode d "type" with
        | some typeNode => mapTypeNode typeNode
        | none => mapResolvedType d
      let val := (fieldNode d "initializer").map parseExpr |>.getD (holeExpr ty)
      some (.VarDecl name ty val (!isConst))
    else none

  -- Function declaration: function f(params): RetType { body }
  else if kind == "FunctionDeclaration" then
    let name := (fieldNode j "name").map nodeText |>.getD "_"
    let params := (fieldArr j "parameters").map parseParam
    let retTy := match fieldNode j "type" with
      | some typeNode => mapTypeNode typeNode
      | none => mapResolvedType j
    let body := match fieldNode j "body" with
      | some bodyNode => parseBlock bodyNode
      | none => holeExpr retTy
    some (.FuncDef name #[] params retTy Pure body none none none none)

  -- Interface declaration: interface X { fields }
  else if kind == "InterfaceDeclaration" then
    let name := (fieldNode j "name").map nodeText |>.getD "_"
    let members := fieldArr j "members"
    let fields := members.filterMap fun m =>
      if isPropertySignature m then
        let fname := (fieldNode m "name").map nodeText |>.getD "_"
        some fname
      else none
    some (.StructDef name #[] fields none none none)

  -- Type alias: type X = T
  else if kind == "TypeAliasDeclaration" then
    let name := (fieldNode j "name").map nodeText |>.getD "_"
    let ty := match fieldNode j "type" with
      | some typeNode => mapTypeNode typeNode
      | none => TyUnit
    some (.TypeAlias name #[] ty none)

  -- Class declaration
  else if kind == "ClassDeclaration" then
    let name := (fieldNode j "name").map nodeText |>.getD "_"
    let members := fieldArr j "members"
    let fields := members.filterMap fun m =>
      if isPropertyDeclaration m || isPropertySignature m then
        let fname := (fieldNode m "name").map nodeText |>.getD "_"
        some fname
      else none
    some (.StructDef name #[] fields none none none)

  -- Enum declaration
  else if kind == "EnumDeclaration" then
    let name := (fieldNode j "name").map nodeText |>.getD "_"
    let members := fieldArr j "members"
    let ctors := members.map fun m =>
      (fieldNode m "name").map nodeText |>.getD "_"
    some (.InductiveDef name #[] ctors none)

  -- Import declaration (skip for now — handled by codegen)
  else if kind == "ImportDeclaration" then none

  -- Export declaration (skip)
  else if kind == "ExportDeclaration" || kind == "ExportAssignment" then none

  -- Expression statement (parse as side-effecting expression, skip in decl context)
  else if kind == "ExpressionStatement" then none

  else none

-- ─── Module parsing ─────────────────────────────────────────────────────────────

/-- Convert a file path to a module name (e.g., "foo/bar.ts" → "TSLean.Generated.Bar"). -/
def fileToModuleName (filePath : String) : String :=
  let parts := filePath.splitOn "/"
  let base := (parts.getLast?.getD "unknown").replace ".ts" "" |>.replace ".tsx" ""
  let capitalized := base.capitalize
  s!"TSLean.Generated.{capitalized}"

/-- Parse a JSON AST file into an IRModule. -/
def parseModule (json : Json) : IRModule :=
  let fileName := fieldStr json "fileName"
  let stmts := fieldArr json "statements"
  let decls := stmts.filterMap parseStatement
  let name := fileToModuleName fileName
  {
    name := name
    imports := #[]
    decls := decls
    comments := #[]
    sourceFile := some (some fileName)
  }

end TSLean.Parser
