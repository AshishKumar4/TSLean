-- TSLean.V2.FromJSON
-- Direct JSON AST → V2 LeanAST lowering.
-- Preserves full type/field information from JSON for fixpoint bootstrap.

import Lean.Data.Json
import TSLean.JsonAST
import TSLean.V2.LeanAST

namespace TSLean.V2.FromJSON

open Lean
open TSLean.JsonAST
open TSLean.V2.LeanAST

private def DEFAULT_DERIVING : Array String := #["Repr", "BEq", "Inhabited"]

-- ─── Namespace naming ───────────────────────────────────────────────────────────

private def fileToModuleName (filePath : String) : String :=
  let parts := filePath.splitOn "/"
  let base := (parts.getLast?.getD "unknown").replace ".ts" "" |>.replace ".tsx" ""
  let segments := base.splitOn "-"
  let capitalized := segments.map fun s =>
    if s.isEmpty then s else s.set ⟨0⟩ (s.get ⟨0⟩ |>.toUpper)
  s!"TSLean.Generated.{String.join capitalized}"

-- ─── Type mapping ───────────────────────────────────────────────────────────────

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

private def mapResolvedTypeJson (rt : Json) : LeanTy :=
  let flags := typeFlags rt
  let sym := typeSymbol rt
  let name := typeName rt
  let eName := if !sym.isEmpty then sym else if !name.isEmpty then name else ""
  mapTypeFromFlags flags eName

private partial def mapResolvedType (j : Json) : LeanTy :=
  match resolvedType j with
  | some rt =>
    let flags := typeFlags rt
    if flags &&& TF_Union != 0 then
      let types := fieldArr rt "types"
      let nonUndef := types.filter fun t =>
        let tf := typeFlags t; tf &&& TF_Undefined == 0 && tf &&& TF_Null == 0
      if nonUndef.size == 1 && nonUndef.size < types.size then
        .TyApp (.TyName "Option") #[mapResolvedTypeJson (nonUndef.getD 0 default)]
      else mapResolvedTypeJson rt
    else mapResolvedTypeJson rt
  | none => .TyName "Unit"

private partial def mapTypeNode (j : Json) : LeanTy :=
  let kind := nodeKind j
  if kind == "NumberKeyword" then .TyName "Float"
  else if kind == "StringKeyword" then .TyName "String"
  else if kind == "BooleanKeyword" then .TyName "Bool"
  else if kind == "VoidKeyword" then .TyName "Unit"
  else if kind == "NeverKeyword" then .TyName "Empty"
  else if kind == "AnyKeyword" then .TyName "TSAny"
  else if kind == "UndefinedKeyword" then .TyApp (.TyName "Option") #[.TyName "Unit"]
  else if kind == "TypeReference" then
    let name := (fieldNode j "typeName").bind (fun tn => getStr tn) |>.getD (nodeText j)
    if name.isEmpty then mapResolvedType j else .TyName name
  else if kind == "ArrayType" then
    .TyApp (.TyName "Array") #[(fieldNode j "elementType").map mapTypeNode |>.getD (.TyName "Unit")]
  else if kind == "UnionType" then
    let types := fieldArr j "types"
    let nonUndef := types.filter fun t =>
      nodeKind t != "UndefinedKeyword" && nodeKind t != "NullKeyword" && nodeKind t != "LiteralType"
    if nonUndef.size == 1 && nonUndef.size < types.size then
      .TyApp (.TyName "Option") #[mapTypeNode (nonUndef.getD 0 default)]
    else mapResolvedType j
  else if kind == "FunctionType" then
    let params := (fieldArr j "parameters").map fun p =>
      (fieldNode p "type").map mapTypeNode |>.getD (.TyName "Unit")
    .TyArrow params ((fieldNode j "type").map mapTypeNode |>.getD (.TyName "Unit"))
  else if kind == "TupleType" then
    let elems := (fieldArr j "elements").map mapTypeNode
    if elems.size == 0 then .TyName "Unit" else .TyTuple elems
  else if kind == "ParenthesizedType" then
    (fieldNode j "type").map mapTypeNode |>.getD (.TyName "Unit")
  else mapResolvedType j

-- ─── Expression rendering ───────────────────────────────────────────────────────

private def parenIfCompoundExpr (j : Json) (rendered : String) : String :=
  let kind := nodeKind j
  if kind == "BinaryExpression" || kind == "ConditionalExpression" ||
     kind == "ArrowFunction" || kind == "AwaitExpression" ||
     (kind == "CallExpression" && (fieldArr j "arguments").size > 0) then
    "(" ++ rendered ++ ")"
  else rendered

/-- Map JS field/method names to Lean equivalents. -/
private def mapFieldName (field : String) : String := match field with
  | "length" => "size" | "push" => "push" | "pop" => "back?"
  | "map" => "map" | "filter" => "filter" | "find" => "find?"
  | "some" => "any" | "every" => "all" | "reduce" => "foldl"
  | "reverse" => "reverse" | "flat" => "join" | "flatMap" => "flatMap"
  | "includes" => "contains" | "indexOf" => "indexOf?"
  | "toLowerCase" => "toLower" | "toUpperCase" => "toUpper"
  | "trim" => "trim" | "startsWith" => "startsWith" | "endsWith" => "endsWith"
  | "toString" => "toString" | "split" => "splitOn" | "join" => "intercalate"
  | other => other

/-- Rewrite method calls: Math.sqrt(x) → Float.sqrt x, etc. -/
private def rewriteMethodCall (fnJ : Option Json) (fn : String) (args : Array String) : Option String :=
  -- Math.X(args) → Float.X args
  if fn.startsWith "Math." then
    let method := fn.drop 5
    let leanFn := match method with
      | "sqrt" => "Float.sqrt" | "abs" => "Float.abs"
      | "floor" => "Float.floor" | "ceil" => "Float.ceil"
      | "round" => "Float.round" | "min" => "Float.min" | "max" => "Float.max"
      | other => "Float." ++ other
    some (leanFn ++ " " ++ String.intercalate " " args.toList)
  -- console.log(args) → IO.println args
  else if fn == "console.log" then
    some ("IO.println " ++ String.intercalate " " args.toList)
  -- Array method calls: arr.push(x) → Array.push arr x
  else if fn.endsWith ".push" && args.size == 1 then
    let obj := fn.dropRight 5
    some ("Array.push " ++ obj ++ " " ++ (args.getD 0 ""))
  else if fn.endsWith ".map" && args.size == 1 then
    let obj := fn.dropRight 4
    some ("Array.map " ++ (args.getD 0 "") ++ " " ++ obj)
  else if fn.endsWith ".filter" && args.size == 1 then
    let obj := fn.dropRight 7
    some ("Array.filter " ++ (args.getD 0 "") ++ " " ++ obj)
  else if fn.endsWith ".join" && args.size == 1 then
    let obj := fn.dropRight 5
    some ("String.intercalate " ++ (args.getD 0 "") ++ " " ++ obj)
  else none

/-- Parenthesize a binary expression operand if it has lower precedence. -/
private def parenBinOperand (j : Json) (rendered : String) (parentOp : String) : String :=
  let kind := nodeKind j
  if kind != "BinaryExpression" then rendered
  else
    let childOp := (fieldNode j "operatorToken").map nodeKind |>.getD ""
    -- Parenthesize add/sub inside mul/div
    let needsParens :=
      (parentOp == "AsteriskToken" || parentOp == "SlashToken" || parentOp == "PercentToken") &&
      (childOp == "PlusToken" || childOp == "MinusToken")
    if needsParens then "(" ++ rendered ++ ")" else rendered

private partial def renderExpr (j : Json) : String :=
  let kind := nodeKind j
  if kind == "NumericLiteral" then nodeText j
  else if kind == "StringLiteral" || kind == "NoSubstitutionTemplateLiteral" then
    "\"" ++ nodeText j ++ "\""
  else if kind == "TrueKeyword" then "true"
  else if kind == "FalseKeyword" then "false"
  else if kind == "NullKeyword" || kind == "UndefinedKeyword" then "none"
  else if kind == "Identifier" then nodeText j
  else if kind == "ThisKeyword" then "self"
  else if kind == "AsExpression" || kind == "SatisfiesExpression" ||
          kind == "NonNullExpression" then
    (fieldNode j "expression").map renderExpr |>.getD "default"
  else if kind == "ParenthesizedExpression" then
    -- Preserve parens for explicit parenthesization in source
    "(" ++ ((fieldNode j "expression").map renderExpr |>.getD "default") ++ ")"
  else if kind == "BinaryExpression" then
    let leftJ := fieldNode j "left"
    let rightJ := fieldNode j "right"
    let left := leftJ.map renderExpr |>.getD "default"
    let right := rightJ.map renderExpr |>.getD "default"
    let opKind := (fieldNode j "operatorToken").map nodeKind |>.getD ""
    let op := mapBinOpSym opKind
    -- Precedence-aware parenthesization
    let left := match leftJ with | some lj => parenBinOperand lj left opKind | none => left
    let right := match rightJ with
      | some rj => parenBinOperand rj (parenIfCompoundExpr rj right) opKind
      | none => right
    left ++ " " ++ op ++ " " ++ right
  else if kind == "PropertyAccessExpression" then
    let obj := (fieldNode j "expression").map renderExpr |>.getD "default"
    let field := (fieldNode j "name").map nodeText |>.getD ""
    -- Map JS field names to Lean equivalents
    let mappedField := mapFieldName field
    obj ++ "." ++ mappedField
  else if kind == "CallExpression" then
    let fnJ := fieldNode j "expression"
    let fn := fnJ.map renderExpr |>.getD "default"
    let args := (fieldArr j "arguments").map fun a => parenIfCompoundExpr a (renderExpr a)
    -- Method call rewriting: Math.sqrt(x) → Float.sqrt x
    let rewritten := rewriteMethodCall fnJ fn args
    match rewritten with
    | some r => r
    | none => if args.size == 0 then fn
              else fn ++ " " ++ String.intercalate " " args.toList
  else if kind == "ReturnStatement" then
    (fieldNode j "expression").map renderExpr |>.getD "()"
  else if kind == "PrefixUnaryExpression" then
    let operand := (fieldNode j "operand").map renderExpr |>.getD "default"
    let opCode := fieldNat j "operator"
    (if opCode == 53 then "!" else if opCode == 40 then "-" else "!") ++ operand
  else if kind == "ConditionalExpression" then
    let c := (fieldNode j "condition").map renderExpr |>.getD "default"
    let t := (fieldNode j "whenTrue").map renderExpr |>.getD "default"
    let f := (fieldNode j "whenFalse").map renderExpr |>.getD "default"
    s!"if {c} then {t} else {f}"
  else if kind == "TemplateExpression" then
    let headText := (fieldNode j "head").map nodeText |>.getD ""
    let spans := fieldArr j "templateSpans"
    let parts := spans.foldl (fun acc span =>
      let expr := (fieldNode span "expression").map renderExpr |>.getD ""
      let lit := (fieldNode span "literal").map nodeText |>.getD ""
      acc ++ "{" ++ expr ++ "}" ++ lit) headText
    "s!\"" ++ parts ++ "\""
  else if kind == "ObjectLiteralExpression" then
    let props := fieldArr j "properties"
    let fields := props.filterMap fun p =>
      let pk := nodeKind p
      if pk == "PropertyAssignment" then
        let n := (fieldNode p "name").map nodeText |>.getD "_"
        let v := (fieldNode p "initializer").map renderExpr |>.getD "default"
        some (n ++ " := " ++ v)
      else if pk == "ShorthandPropertyAssignment" then
        let n := (fieldNode p "name").map nodeText |>.getD "_"
        some (n ++ " := " ++ n)
      else none
    if fields.size == 0 then "{}" else "{ " ++ String.intercalate ", " fields.toList ++ " }"
  else if kind == "ArrayLiteralExpression" then
    let elems := (fieldArr j "elements").map renderExpr
    "#[" ++ String.intercalate ", " elems.toList ++ "]"
  else if kind == "AwaitExpression" then
    (fieldNode j "expression").map renderExpr |>.getD "default"
  else if kind == "ArrowFunction" || kind == "FunctionExpression" then
    let params := (fieldArr j "parameters").map fun p => (fieldNode p "name").map nodeText |>.getD "_"
    let bodyJ := fieldNode j "body"
    let body := match bodyJ with
      | some b => if isBlock b then "(block)" else renderExpr b
      | none => "default"
    "fun " ++ String.intercalate " " params.toList ++ " => " ++ body
  else "default"
where
  mapBinOpSym (kind : String) : String := match kind with
    | "PlusToken" => "+" | "MinusToken" => "-" | "AsteriskToken" => "*"
    | "SlashToken" => "/" | "PercentToken" => "%"
    | "EqualsEqualsToken" | "EqualsEqualsEqualsToken" => "=="
    | "ExclamationEqualsToken" | "ExclamationEqualsEqualsToken" => "!="
    | "LessThanToken" => "<" | "LessThanEqualsToken" => "<="
    | "GreaterThanToken" => ">" | "GreaterThanEqualsToken" => ">="
    | "AmpersandAmpersandToken" => "&&" | "BarBarToken" => "||"
    | _ => "+"

-- ─── Body lowering ──────────────────────────────────────────────────────────────

private partial def lowerExpr (j : Json) : LeanExpr := .Lit (renderExpr j)

mutual

private partial def lowerBody (j : Json) : LeanExpr :=
  if isBlock j then
    let stmts := fieldArr j "statements"
    if stmts.size == 0 then .Lit "()" else lowerStmtSeq stmts.toList
  else lowerExpr j

private partial def lowerStmtSeq : List Json → LeanExpr
  | [] => .Lit "()"
  | [s] => lowerBlockStmt s
  | s :: rest =>
    let kind := nodeKind s
    if kind == "IfStatement" then
      let cond := (fieldNode s "expression").map renderExpr |>.getD "true"
      let thenB := (fieldNode s "thenStatement").map lowerBody |>.getD (.Lit "()")
      let elseB := match fieldNode s "elseStatement" with
        | some e => lowerBody e | none => lowerStmtSeq rest
      .If (.Lit cond) thenB elseB
    else if kind == "VariableStatement" then
      let declList := fieldNode s "declarationList"
      let decls := declList.map (fieldArr · "declarations") |>.getD #[]
      if decls.size > 0 then
        let d := decls.getD 0 default
        let name := (fieldNode d "name").map nodeText |>.getD "_"
        let val := (fieldNode d "initializer").map renderExpr |>.getD "default"
        -- Add type annotation from explicit type or resolved type
        let ty := match fieldNode d "type" with
          | some tn => some (mapTypeNode tn)
          | none =>
            -- Use resolved type if it's informative (not Unit/TSAny)
            let rt := mapResolvedType d
            match rt with
            | .TyName "Unit" | .TyName "TSAny" => none
            | _ => some rt
        .Let name ty (.Lit val) (lowerStmtSeq rest) false
      else lowerStmtSeq rest
    else
      let expr := lowerBlockStmt s
      match rest with | [] => expr | _ => .Seq #[expr, lowerStmtSeq rest]

private partial def lowerBlockStmt (j : Json) : LeanExpr :=
  let kind := nodeKind j
  if kind == "ReturnStatement" then
    .Lit ((fieldNode j "expression").map renderExpr |>.getD "()")
  else if kind == "IfStatement" then
    let cond := (fieldNode j "expression").map renderExpr |>.getD "true"
    let thenB := (fieldNode j "thenStatement").map lowerBody |>.getD (.Lit "()")
    let elseB := (fieldNode j "elseStatement").map lowerBody |>.getD (.Lit "()")
    .If (.Lit cond) thenB elseB
  else .Lit (renderExpr j)

end -- mutual

-- ─── Helpers ────────────────────────────────────────────────────────────────────

private partial def exprContainsName (e : LeanExpr) (name : String) : Bool :=
  match e with
  | .Lit s => (s.splitOn name).length > 1
  | .Var n => n == name
  | .If c t f => exprContainsName c name || exprContainsName t name || exprContainsName f name
  | .Let _ _ v b _ => exprContainsName v name || exprContainsName b name
  | .Seq stmts => stmts.any (exprContainsName · name)
  | .Do b | .Pure b | .Return b => exprContainsName b name
  | _ => false

/-- Check if a body expression needs `do` wrapping (multiple lets). -/
private def needsDoWrap (e : LeanExpr) : Bool :=
  match e with
  | .Let _ _ _ body _ => match body with
    | .Let .. | .If .. | .Match .. | .Seq .. => true
    | _ => false
  | _ => false

-- ─── Declaration lowering ───────────────────────────────────────────────────────

private def extractTypeParams (j : Json) : Array LeanTyParam :=
  (fieldArr j "typeParameters").map fun tp =>
    let name := (fieldNode tp "name").map nodeText |>.getD (nodeText tp)
    { name := name, explicit := true, constraints := none : LeanTyParam }

private def lowerParam (j : Json) : LeanParam :=
  let name := (fieldNode j "name").map nodeText |>.getD "_"
  let ty := match fieldNode j "type" with | some tn => mapTypeNode tn | none => mapResolvedType j
  { name := name, ty := ty }

private partial def lowerVarStatement (j : Json) : Array LeanDecl :=
  let declList := fieldNode j "declarationList"
  let decls := declList.map (fieldArr · "declarations") |>.getD #[]
  decls.filterMap fun d =>
    let name := (fieldNode d "name").map nodeText |>.getD "_"
    let ty := match fieldNode d "type" with | some tn => mapTypeNode tn | none => mapResolvedType d
    let body := match fieldNode d "initializer" with
      | some init => lowerExpr init | none => .Default (some ty)
    some (.Def false name #[] #[] ty body none none none)

private partial def lowerFuncDecl (j : Json) : Array LeanDecl :=
  let name := (fieldNode j "name").map nodeText |>.getD "_"
  let tyParams := extractTypeParams j
  let params := (fieldArr j "parameters").map lowerParam
  let retTy := match fieldNode j "type" with | some tn => mapTypeNode tn | none => mapResolvedType j
  -- Detect async: check for async modifier
  let mods := fieldArr j "modifiers"
  let isAsync := mods.any fun m => nodeKind m == "AsyncKeyword"
  -- Wrap return type in IO for async functions
  let retTy := if isAsync then .TyApp (.TyName "IO") #[retTy] else retTy
  let body := match fieldNode j "body" with | some b => lowerBody b | none => .Default (some retTy)
  -- Wrap in `do` if body has Let bindings or is async
  let body := if needsDoWrap body || isAsync then .Do body else body
  let isPartial := exprContainsName body name
  #[.Def isPartial name tyParams params retTy body none none none]

private partial def lowerInterfaceDecl (j : Json) : Array LeanDecl :=
  let name := (fieldNode j "name").map nodeText |>.getD "_"
  let tyParams := extractTypeParams j
  let members := fieldArr j "members"
  let fields := members.filterMap fun m =>
    if isPropertySignature m then
      let fn := (fieldNode m "name").map nodeText |>.getD "_"
      let fty := match fieldNode m "type" with | some tn => mapTypeNode tn | none => mapResolvedType m
      some (LeanField.mk fn fty none)
    else none
  #[.Structure name tyParams fields none DEFAULT_DERIVING none]

private partial def lowerClassDecl (j : Json) : Array LeanDecl :=
  let name := (fieldNode j "name").map nodeText |>.getD "_"
  let members := fieldArr j "members"
  let fields := members.filterMap fun m =>
    if isPropertyDeclaration m || isPropertySignature m then
      let fn := (fieldNode m "name").map nodeText |>.getD "_"
      let fty := match fieldNode m "type" with | some tn => mapTypeNode tn | none => mapResolvedType m
      some (LeanField.mk fn fty none)
    else none
  #[.Structure name #[] fields none DEFAULT_DERIVING none]

private partial def lowerTypeAliasDecl (j : Json) : Array LeanDecl :=
  let name := (fieldNode j "name").map nodeText |>.getD "_"
  let tyParams := extractTypeParams j
  let body := match fieldNode j "type" with | some tn => mapTypeNode tn | none => .TyName "Unit"
  #[.Abbrev name tyParams body none]

private partial def lowerEnumDecl (j : Json) : Array LeanDecl :=
  let name := (fieldNode j "name").map nodeText |>.getD "_"
  let ctors := (fieldArr j "members").map fun m =>
    LeanCtor.mk ((fieldNode m "name").map nodeText |>.getD "_") #[]
  #[.Inductive name #[] ctors DEFAULT_DERIVING none]

private partial def lowerStatement (j : Json) : Array LeanDecl :=
  let kind := nodeKind j
  let comments := fieldArr j "leadingComments"
  let commentDecls := comments.foldl (fun acc c =>
    match getStr c with
    | some text =>
      -- Preserve // prefix (TS lowering keeps it); only strip /* */ block markers
      let stripped := text.trim
      let stripped := if stripped.startsWith "/*" then
        stripped.replace "/*" "" |>.replace "*/" "" |>.replace "* " "" |>.trim
      else stripped
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

-- ─── Module lowering ────────────────────────────────────────────────────────────

private def textContains (text : String) (sub : String) : Bool :=
  (text.splitOn sub).length > 1

/-- Scan JSON statements for import needs. -/
private def scanImports (stmts : Array Json) : Array String :=
  let needs := #["TSLean.Runtime.Basic", "TSLean.Runtime.Coercions"]
  let text := stmts.foldl (fun acc s => acc ++ toString s) ""
  let needs := if textContains text "async" || textContains text "await" ||
    textContains text "Promise" then needs.push "TSLean.Runtime.Monad" else needs
  let needs := if textContains text "fetch" || textContains text "Request" ||
    textContains text "Response" then needs.push "TSLean.Runtime.WebAPI" else needs
  let needs := if textContains text "Map" || textContains text "Set" then
    needs.push "TSLean.Stdlib.HashMap" else needs
  needs

/-- Determine open namespaces from imports. -/
private def resolveOpens (imports : Array String) : Array String :=
  let opens := #["TSLean"]
  let opens := if imports.any (textContains · "WebAPI") then opens.push "TSLean.WebAPI" else opens
  let opens := if imports.any (textContains · "HashMap") then opens.push "TSLean.Stdlib.HashMap" else opens
  opens

def lowerJsonModule (json : Json) : LeanFile :=
  let fileName := fieldStr json "fileName"
  let ns := fileToModuleName fileName
  let stmts := fieldArr json "statements"
  let imports := scanImports stmts
  let decls := imports.map fun imp => LeanDecl.Import imp
  let decls := decls.push .Blank
  let decls := decls.push (.Open (resolveOpens imports))
  let decls := decls.push .Blank
  let bodyDecls := stmts.foldl (fun acc s =>
    let ds := lowerStatement s
    if ds.isEmpty then acc else acc ++ ds ++ #[.Blank]
  ) #[]
  let useNs := !ns.isEmpty && ns != "T" && ns != "Test"
  let decls := if useNs then decls.push (.Namespace ns bodyDecls) else decls ++ bodyDecls
  { banner := some "Auto-generated by ts-lean-transpiler"
    sourcePath := some fileName
    decls := decls }

end TSLean.V2.FromJSON
