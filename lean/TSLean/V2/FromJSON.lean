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

-- ─── Discriminated union registry ───────────────────────────────────────────────

/-- Info about one variant (constructor) of a discriminated union. -/
structure VariantInfo where
  ctorName : String         -- e.g. "Shape.Circle"
  fields   : Array String   -- non-discriminant field names, e.g. #["radius"]

/-- Metadata about a discriminated union type. -/
structure UnionInfo where
  typeName  : String
  discField : String              -- e.g. "kind", "tag", "type"
  variants  : Array (String × VariantInfo)  -- key (lowercase literal) → info

/-- Registry of known discriminated union types. -/
abbrev UnionRegistry := Array UnionInfo

private def lookupUnionByName (reg : UnionRegistry) (name : String) : Option UnionInfo :=
  reg.find? fun u => u.typeName == name

private def lookupVariant (u : UnionInfo) (key : String) : Option VariantInfo :=
  -- Try both original and lowercased key
  (u.variants.find? fun (k, _) => k == key).map (·.2)
    |>.orElse fun _ => (u.variants.find? fun (k, _) => k == key.decapitalize).map (·.2)

/-- Context for expression rendering inside a constructor pattern match arm.
    Maps scrutinee field accesses to bound pattern variables. -/
structure MatchSubst where
  scrutineeVar : String                   -- e.g. "s"
  fieldBindings : Array (String × String) -- (fieldName, boundVar) e.g. ("radius", "radius")
  unionInfo : UnionInfo                   -- the union being matched

-- ─── Namespace naming ───────────────────────────────────────────────────────────

private def fileToModuleName (filePath : String) : String :=
  let parts := filePath.splitOn "/"
  let base := (parts.getLast?.getD "unknown").replace ".ts" "" |>.replace ".tsx" ""
  let segments := base.splitOn "-"
  let capitalized := segments.map fun s =>
    if s.isEmpty then s else (s.front.toUpper.toString) ++ (s.drop 1).toString
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
  -- Anonymous object types (TS internal __type) → String as compilable approximation
  else if name == "__type" then .TyName "String"
  else .TyName name

private def mapResolvedTypeJson (rt : Json) : LeanTy :=
  let flags := typeFlags rt
  let sym := typeSymbol rt
  let name := typeName rt
  let alias := typeAliasName rt
  let eName := if !sym.isEmpty then sym
    else if !name.isEmpty then name
    else if !alias.isEmpty then alias
    else ""
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
      else
        -- Check for alias name on the resolved type
        let alias := typeAliasName rt
        if !alias.isEmpty then .TyName alias
        -- Multiple non-nil types: take the first one (matches TS mapUnion fallthrough)
        else if nonUndef.size > 0 then mapResolvedTypeJson (nonUndef.getD 0 default)
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
    -- Extract name: try typeName field, then resolvedType.aliasName, then nodeText
    let nameFromTypeName := (fieldNode j "typeName").bind getStr
    let nameFromAlias := resolvedType j |>.bind (fun rt => getField rt "aliasName" |>.bind getStr)
    let name := nameFromTypeName.getD (nameFromAlias.getD (nodeText j))
    let typeArgs := fieldArr j "typeArguments"
    if name.isEmpty then mapResolvedType j
    -- Promise<T> is unwrapped; IO wrapper added at function declaration level
    else if name == "Promise" && typeArgs.size == 1 then mapTypeNode (typeArgs.getD 0 default)
    -- JS Error types map to String in the Lean model
    else if name == "Error" || name.endsWith "Error" then .TyName "String"
    -- Record<K,V> → String (matches TS pipeline which maps Record types to String)
    else if name == "Record" then .TyName "String"
    -- Extract<T, U> → resolve via resolvedType flags (TS maps Extract to TSAny via flags)
    else if name == "Extract" then mapResolvedType j
    -- Set<T> → Array T (matches TS pipeline which maps Set to Array)
    else if name == "Set" then .TyApp (.TyName "Array") (typeArgs.map mapTypeNode)
    -- Map<K,V> → AssocMap K V (matches TS pipeline)
    else if name == "Map" && typeArgs.size == 2 then .TyApp (.TyName "AssocMap") (typeArgs.map mapTypeNode)
    else if typeArgs.size > 0 then .TyApp (.TyName name) (typeArgs.map mapTypeNode)
    else .TyName name
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
    let rawParams := (fieldArr j "parameters").map fun p =>
      (fieldNode p "type").map mapTypeNode |>.getD (.TyName "Unit")
    let params := if rawParams.size == 0 then #[.TyName "Unit"] else rawParams
    let retNode := fieldNode j "type"
    -- If return type is Promise<T>, wrap inner as IO T
    let retTy := match retNode with
      | some rn =>
        let rk := nodeKind rn
        if rk == "TypeReference" then
          let rAlias := resolvedType rn |>.bind (fun rt => getField rt "aliasName" |>.bind getStr)
          let rName := (fieldNode rn "typeName").map nodeText |>.orElse (fun _ => rAlias)
          if rName == some "Promise" then
            let inner := mapTypeNode rn  -- recursive call unwraps Promise<T> to T
            .TyApp (.TyName "IO") #[inner]
          else mapTypeNode rn
        else mapTypeNode rn
      | none => .TyName "Unit"
    .TyArrow params retTy
  else if kind == "TupleType" then
    let elems := (fieldArr j "elements").map mapTypeNode
    if elems.size == 0 then .TyName "Unit" else .TyTuple elems
  else if kind == "ParenthesizedType" then
    (fieldNode j "type").map mapTypeNode |>.getD (.TyName "Unit")
  -- Anonymous object types (TypeLiteral) → String as compilable approximation
  else if kind == "TypeLiteral" then .TyName "String"
  else mapResolvedType j

-- ─── Discriminant field detection ────────────────────────────────────────────────

private def DISCRIMINANT_FIELDS : Array String := #["kind", "tag", "type"]

private def isDiscriminantField (name : String) : Bool :=
  DISCRIMINANT_FIELDS.contains name

-- ─── Expression rendering ───────────────────────────────────────────────────────

/-- Substitution context: when inside a discriminated union match arm,
    field accesses on the scrutinee variable are replaced with bound pattern variables. -/
abbrev SubstCtx := Option MatchSubst

private def substFieldAccess (ctx : SubstCtx) (obj : String) (field : String) : Option String :=
  match ctx with
  | some subst =>
    if obj == subst.scrutineeVar then
      (subst.fieldBindings.find? fun (f, _) => f == field).map (·.2)
    else none
  | none => none

/-- Sanitize identifier: wrap Lean keywords in «» (matches TS sanitize function). -/
private def sanitizeId (name : String) : String :=
  if #["def","fun","let","in","if","then","else","match","with","do","return","where",
       "have","show","from","by","class","instance","structure","inductive","namespace",
       "end","open","import","theorem","lemma","example","variable","universe","abbrev",
       "opaque","partial","mutual","private","protected","section","attribute","and","or",
       "not","true","false","Type","Prop",
       "for","while","repeat","at","try","catch","throw","macro","syntax","tactic",
       "set_option","derive","deriving","extends","override"].any (· == name)
  then "«" ++ name ++ "»" else name

/-- Escape special characters in string literals for Lean output (matches JSON.stringify behavior). -/
private def escapeLitStr (s : String) : String :=
  s.foldl (fun acc c =>
    if c == '\n' then acc ++ "\\n"
    else if c == '\r' then acc ++ "\\r"
    else if c == '\t' then acc ++ "\\t"
    else if c == '\\' then acc ++ "\\\\"
    else if c == '"' then acc ++ "\\\""
    else acc.push c) ""

private def mapBinOpSym (kind : String) : String := match kind with
  | "PlusToken" => "+" | "MinusToken" => "-" | "AsteriskToken" => "*"
  | "SlashToken" => "/" | "PercentToken" => "%"
  | "EqualsEqualsToken" | "EqualsEqualsEqualsToken" => "=="
  | "ExclamationEqualsToken" | "ExclamationEqualsEqualsToken" => "!="
  | "LessThanToken" | "FirstBinaryOperator" => "<" | "LessThanEqualsToken" => "<="
  | "GreaterThanToken" => ">" | "GreaterThanEqualsToken" => ">="
  | "AmpersandAmpersandToken" => "&&" | "BarBarToken" => "||"
  | _ => "+"

-- Fields with simple Option-wrapped types (string?, string[]?) that need .isSome in conditions.
-- Complex union? fields (LeanTy?, LeanExpr?) and boolean? fields do NOT get .isSome —
-- the TS type checker expands complex unions, preventing Option wrapping.
private def isStringOptionalField (name : String) : Bool :=
  name == "banner" || name == "sourcePath" || name == "comment" || name == "docComment" ||
  name == "extends_" || name == "reason" || name == "constraints" || name == "name"

private def wrapConditionIsSome (j : Json) (rendered : String) : String :=
  if nodeKind j == "PropertyAccessExpression" then
    let fieldName := (fieldNode j "name").map nodeText |>.getD ""
    if isStringOptionalField fieldName then rendered ++ ".isSome"
    else rendered
  else rendered

-- Render a condition for if-statements, recursively adding .isSome for
-- string-optional fields and handling !== undefined → .isSome.
private partial def renderIfCondition (render : Json → String) (j : Json) : String :=
  let kind := nodeKind j
  if kind == "BinaryExpression" then
    let opKind := (fieldNode j "operatorToken").map nodeKind |>.getD ""
    if opKind == "ExclamationEqualsEqualsToken" || opKind == "ExclamationEqualsToken" then
      let rightK := (fieldNode j "right").map nodeKind |>.getD ""
      if rightK == "Identifier" && ((fieldNode j "right").map nodeText |>.getD "") == "undefined" then
        let left := (fieldNode j "left").map render |>.getD "default"
        left ++ ".isSome"
      else
        let l := (fieldNode j "left").map (renderIfCondition render) |>.getD "default"
        let r := (fieldNode j "right").map (renderIfCondition render) |>.getD "default"
        l ++ " != " ++ r
    else if opKind == "AmpersandAmpersandToken" || opKind == "BarBarToken" then
      -- Sub-expressions use plain render; wrap BinaryExpr operands in parens
      -- matching TS lowerExprP which wraps BinOp children in Paren
      let leftJ := fieldNode j "left"
      let rightJ := fieldNode j "right"
      let l := leftJ.map render |>.getD "default"
      let r := rightJ.map render |>.getD "default"
      -- Parenthesize BinaryExpression operands (TS lowerExprP wraps BinOp in Paren)
      let l := match leftJ with
        | some lj => if nodeKind lj == "BinaryExpression" then "(" ++ l ++ ")" else l
        | none => l
      let r := match rightJ with
        | some rj => if nodeKind rj == "BinaryExpression" then "(" ++ r ++ ")" else r
        | none => r
      let op := if opKind == "AmpersandAmpersandToken" then "&&" else "||"
      let result := l ++ " " ++ op ++ " " ++ r
      -- Check if this || has optional operands → append .isSome to whole result
      let leftIsOpt := match leftJ with
        | some lj => nodeKind lj == "PropertyAccessExpression" &&
            isStringOptionalField ((fieldNode lj "name").map nodeText |>.getD "")
        | none => false
       let rightIsOpt := match rightJ with
        | some rj => nodeKind rj == "PropertyAccessExpression" &&
            isStringOptionalField ((fieldNode rj "name").map nodeText |>.getD "")
        | none => false
      if leftIsOpt || rightIsOpt then result ++ ".isSome"
      else result
    else wrapConditionIsSome j (render j)
  else if kind == "PrefixUnaryExpression" then
    let opCode := fieldNat j "operator"
    if opCode == 53 then
      let inner := (fieldNode j "operand").map (renderIfCondition render) |>.getD "default"
      "!" ++ inner
    else wrapConditionIsSome j (render j)
  else wrapConditionIsSome j (render j)

private def parenIfCompoundExpr (j : Json) (rendered : String) : String :=
  let kind := nodeKind j
  if kind == "BinaryExpression" || kind == "ConditionalExpression" ||
     kind == "ArrowFunction" || kind == "AwaitExpression" ||
     kind == "TemplateExpression" ||
     kind == "CallExpression" ||
     (kind == "NewExpression" && (fieldArr j "arguments").size > 0) then
    "(" ++ rendered ++ ")"
  else rendered

/-- Try to rewrite an ObjectLiteralExpression as a constructor application
    if it matches a known discriminated union pattern. -/
private def tryStructToCtor (reg : UnionRegistry) (props : Array Json)
    (renderFn : Json → String) : Option String :=
  let discProp := props.find? fun p =>
    nodeKind p == "PropertyAssignment" &&
    isDiscriminantField ((fieldNode p "name").map nodeText |>.getD "")
  match discProp with
  | none => none
  | some dp =>
    let initJ := fieldNode dp "initializer"
    let litVal := match initJ with
      | some init => if nodeKind init == "StringLiteral" then some (nodeText init) else none
      | none => none
    match litVal with
    | none => none
    | some key =>
      let found := reg.findSome? fun u =>
        (lookupVariant u key).map fun vi => (u, vi)
      match found with
      | none => none
      | some (_, vi) =>
        let argProps := props.filter fun p =>
          let pname := (fieldNode p "name").map nodeText |>.getD ""
          !isDiscriminantField pname
        let args := argProps.map fun p =>
          let rendered := (fieldNode p "initializer").map renderFn |>.getD "default"
          match fieldNode p "initializer" with
          | some init => parenIfCompoundExpr init rendered
          | none => rendered
        let argStr := if args.size == 0 then "" else " " ++ String.intercalate " " args.toList
        some (vi.ctorName ++ argStr)

/-- Map JS field/method names to Lean equivalents. -/
-- Lean keywords that need «» escaping when used as identifiers/field names
private def isLeanKeyword (name : String) : Bool :=
  name == "def" || name == "fun" || name == "let" || name == "in" ||
  name == "if" || name == "then" || name == "else" || name == "match" ||
  name == "with" || name == "do" || name == "return" || name == "where" ||
  name == "have" || name == "show" || name == "from" || name == "by" ||
  name == "class" || name == "instance" || name == "structure" || name == "inductive" ||
  name == "namespace" || name == "end" || name == "open" || name == "import" ||
  name == "theorem" || name == "lemma" || name == "example" || name == "variable" ||
  name == "universe" || name == "abbrev" || name == "opaque" || name == "partial" ||
  name == "mutual" || name == "private" || name == "protected" || name == "section" ||
  name == "attribute" || name == "and" || name == "or" || name == "not" ||
  name == "true" || name == "false" || name == "Type" || name == "Prop" ||
  name == "for" || name == "while" || name == "repeat" || name == "at" ||
  name == "try" || name == "catch" || name == "throw" || name == "macro" ||
  name == "syntax" || name == "tactic" || name == "set_option" || name == "derive" ||
  name == "deriving" || name == "extends" || name == "override"

private def escapeLeanKeyword (name : String) : String :=
  if isLeanKeyword name then "«" ++ name ++ "»" else name

private def mapFieldName (field : String) : String := match field with
  | "length" => "size" | "push" => "push" | "pop" => "back?"
  | "map" => "map" | "filter" => "filter" | "find" => "find?"
  | "some" => "any" | "every" => "all" | "reduce" => "foldl"
  | "reverse" => "reverse" | "flat" => "join" | "flatMap" => "flatMap"
  | "includes" => "includes" | "indexOf" => "indexOf?"
  | "slice" => "extract"
  | "toLowerCase" => "toLower" | "toUpperCase" => "toUpper"
  | "trim" => "trim" | "startsWith" => "startsWith" | "endsWith" => "endsWith"
  | "toString" => "toString" | "split" => "splitOn" | "join" => "intercalate"
  | other => escapeLeanKeyword other

/-- Rewrite method calls: Math.sqrt(x) → Float.sqrt x, etc. -/
private def rewriteMethodCall (fnJ : Option Json) (fn : String) (args : Array String) : Option String :=
  -- Math.X(args) → matching TS stdlib table
  if fn.startsWith "Math." then
    let method := (fn.drop 5).toString
    let leanFn := match method with
      | "sqrt" => "Float.sqrt" | "abs" => "Float.abs"
      | "floor" => "Float.floor" | "ceil" => "Float.ceil"
      | "round" => "Float.round" | "min" => "min" | "max" => "max"
      | "pow" => "Float.pow" | "log" => "Float.log"
      | other => "Float." ++ other
    some (leanFn ++ " " ++ String.intercalate " " args.toList)
  -- console.log(args) → IO.println args
  else if fn == "console.log" then
    some ("IO.println " ++ String.intercalate " " args.toList)
  -- JSON.stringify(x) → serialize x
  else if fn == "JSON.stringify" then
    some ("serialize " ++ String.intercalate " " args.toList)
  -- fetch(url) → WebAPI.fetch url
  else if fn == "fetch" then
    some ("WebAPI.fetch " ++ String.intercalate " " args.toList)
  -- response.json() → sorry (untyped Response method)
  else if fn.endsWith ".json" && args.size == 0 then some "sorry"
  -- Array method calls: arr.push(x) → Array.push arr x
  else if fn.endsWith ".push" && args.size == 1 then
    let obj := fn.dropEnd 5 |>.toString
    some ("Array.push " ++ obj ++ " " ++ (args.getD 0 ""))
  else if fn.endsWith ".map" && args.size == 1 then
    let obj := fn.dropEnd 4 |>.toString
    some ("Array.map " ++ (args.getD 0 "") ++ " " ++ obj)
  else if fn.endsWith ".filter" && args.size == 1 then
    let obj := fn.dropEnd 7 |>.toString
    some ("Array.filter " ++ (args.getD 0 "") ++ " " ++ obj)
  else if fn.endsWith ".join" && args.size == 1 then
    let obj := fn.dropEnd 5 |>.toString
    let obj := if obj.any (· == ' ') then "(" ++ obj ++ ")" else obj
    some ("String.intercalate " ++ (args.getD 0 "") ++ " " ++ obj)
  -- Also match after mapFieldName has renamed .join → .intercalate
  else if fn.endsWith ".intercalate" && args.size == 1 then
    let obj := fn.dropEnd 12 |>.toString
    let obj := if obj.any (· == ' ') then "(" ++ obj ++ ")" else obj
    some ("String.intercalate " ++ (args.getD 0 "") ++ " " ++ obj)
  -- .has(x) on a Set → AssocSet.contains SET x
  else if fn.endsWith ".has" && args.size == 1 then
    let obj := fn.dropEnd 4 |>.toString
    some ("AssocSet.contains " ++ obj ++ " " ++ (args.getD 0 ""))
  -- .add(x) on a Set → AssocSet.insert SET x  (TS Set.add, not Array — arrays use .push)
  else if fn.endsWith ".add" && args.size == 1 then
    let obj := fn.dropEnd 4 |>.toString
    some ("AssocSet.insert " ++ obj ++ " " ++ (args.getD 0 ""))
  -- .set(k, v) on a Map → AssocMap.insert MAP k v
  else if fn.endsWith ".set" && args.size == 2 then
    let obj := fn.dropEnd 4 |>.toString
    some ("AssocMap.insert " ++ obj ++ " " ++ (args.getD 0 "") ++ " " ++ (args.getD 1 ""))
  -- .get(k) on a Map → AssocMap.find? MAP k
  else if fn.endsWith ".get" && args.size == 1 then
    let obj := fn.dropEnd 4 |>.toString
    some ("AssocMap.find? " ++ obj ++ " " ++ (args.getD 0 ""))
  -- .keys() on a Map → AssocMap.keys MAP
  else if fn.endsWith ".keys" && args.size == 0 then
    let obj := fn.dropEnd 5 |>.toString
    some ("AssocMap.keys " ++ obj)
  -- .splitOn(sep) — after mapFieldName has renamed .split → .splitOn
  else if fn.endsWith ".splitOn" && args.size == 1 then
    let obj := fn.dropEnd 8 |>.toString
    some (obj ++ ".splitOn " ++ (args.getD 0 ""))
  -- .includes(x) → .contains for array literals (matches TS pipeline)
  else if fn.endsWith ".includes" && args.size == 1 then
    let objNode := fnJ.bind fun fj => fieldNode fj "expression"
    let objKind := objNode.map nodeKind |>.getD ""
    if objKind == "ArrayLiteralExpression" then
      let obj := fn.dropEnd 9 |>.toString
      some (obj ++ ".contains " ++ (args.getD 0 ""))
    else none
  else none

/-- Parenthesize a binary expression operand if it's compound.
    Matches the TS lowering which wraps BinOp/App/Lambda/IfThenElse/LitFloat sub-exprs. -/
private def parenBinOperand (j : Json) (rendered : String) (_parentOp : String) : String :=
  let kind := nodeKind j
  -- The TS lowering wraps any compound sub-expression in parens
   if kind == "BinaryExpression" || kind == "ConditionalExpression" ||
      kind == "AwaitExpression" || kind == "PrefixUnaryExpression" ||
      (kind == "CallExpression" && (fieldArr j "arguments").size > 0) ||
     -- Method chain: e.g. s.charAt(0).toUpper needs parens as binop operand
     (kind == "CallExpression" && (fieldArr j "arguments").size == 0 &&
       ((fieldNode j "expression").map nodeKind |>.getD "") == "PropertyAccessExpression" &&
       (((fieldNode j "expression").bind (fieldNode · "expression")).map nodeKind |>.getD "") == "CallExpression") ||
     -- Float literals need parens in Lean (matches TS needsParens for LitFloat)
     (kind == "NumericLiteral" && (nodeText j).any (· == '.')) then
    "(" ++ rendered ++ ")"
  else rendered

/-- Check if a JSON AST node has string type via resolved type flags or name. -/
private def isStringTyped (j : Json) : Bool :=
  match resolvedType j with
  | some rt =>
    let flags := typeFlags rt
    let name := typeName rt
    flags &&& TF_String != 0 || flags &&& TF_StringLiteral != 0 || name == "string"
  | none => false

/-- Recursively check if an expression involves string types
    (checks the node and walks through PropertyAccess/Call chains). -/
private partial def hasStringType (j : Json) : Bool :=
  if isStringTyped j then true
  else
    let kind := nodeKind j
    if kind == "PropertyAccessExpression" || kind == "CallExpression" then
      match fieldNode j "expression" with
      | some inner => hasStringType inner
      | none => false
    else false

/-- Render a block body inline as "let x := v; let y := w; ... ; final".
    Used for arrow function bodies with local variable declarations.
    Takes a render function for expressions to avoid forward-reference issues. -/
private partial def renderBlockStmtsInline (render : Json → String) (stmts : Array Json) : String :=
  let rec go : List Json → List String
    | [] => []
    | s :: rest =>
      let kind := nodeKind s
      if kind == "VariableStatement" then
        let declList := fieldNode s "declarationList"
        let decls := match declList with
          | some dl => fieldArr dl "declarations" | none => #[]
        let letParts := decls.toList.map fun d =>
          let dname := escapeLeanKeyword ((fieldNode d "name").map nodeText |>.getD "_")
          let init := (fieldNode d "initializer").map render |>.getD "default"
          "let " ++ dname ++ " := " ++ init
        (String.intercalate "; " letParts) :: go rest
      else if kind == "ReturnStatement" then
        -- Simple return at end of block: just the expression value
        [((fieldNode s "expression").map render |>.getD "()")]
      else if kind == "ExpressionStatement" then
        ((fieldNode s "expression").map render |>.getD "()") :: go rest
      else if kind == "ForOfStatement" then
        let iter := (fieldNode s "expression").map render |>.getD "default"
        let varName := match fieldNode s "initializer" with
          | some v =>
            if nodeKind v == "VariableDeclarationList" then
              let decls := fieldArr v "declarations"
              (decls.getD 0 default |> (fieldNode · "name")).map nodeText |>.getD "_"
            else render v
          | none => "_"
        let bodyStmts := match fieldNode s "statement" with
          | some b => if isBlock b then fieldArr b "statements" else #[b]
          | none => #[]
        let body := renderBlockStmtsInline render bodyStmts
        -- If body is a let binding (from +=), append "; ()" for Unit continuation
        let body := if body.startsWith "let " then body ++ "; ()" else body
        ("Array.forM " ++ iter ++ " (fun " ++ varName ++ " => " ++ body ++ ")") :: go rest
      else if kind == "IfStatement" then
        let cond := (fieldNode s "expression").map (renderIfCondition render) |>.getD "true"
        let thenBranch := match fieldNode s "thenStatement" with
          | some t =>
            if isBlock t then renderBlockStmtsInline render (fieldArr t "statements")
            else render t
          | none => "()"
        let hasElse := (fieldNode s "elseStatement").isSome
        let elseBranch := if hasElse then
            match fieldNode s "elseStatement" with
            | some e =>
              if isBlock e then renderBlockStmtsInline render (fieldArr e "statements")
              else render e
            | none => "()"
          else
            match rest with
            | r :: _ =>
              if nodeKind r == "ReturnStatement" then
                "pure " ++ ((fieldNode r "expression").map render |>.getD "()")
              else "()"
            | [] => "()"
        let ifStr := "if " ++ cond ++ " then " ++ thenBranch ++ " else " ++ elseBranch
        if !hasElse && match rest with | r :: _ => nodeKind r == "ReturnStatement" | [] => false then
          [ifStr]
        else
          ifStr :: go rest
      else (render s) :: go rest
  String.intercalate "; " (go stmts.toList)

/-- Render a JSON AST expression to a Lean expression string.
    Takes a union registry for struct-literal→ctor rewriting,
    and a substitution context for match arm body field access rewriting. -/
private partial def renderExprCtx (reg : UnionRegistry) (ctx : SubstCtx) (j : Json) : String :=
  let re := renderExprCtx reg ctx
  let kind := nodeKind j
  if kind == "NumericLiteral" then nodeText j
  else if kind == "StringLiteral" || kind == "NoSubstitutionTemplateLiteral" then
    let text := nodeText j
    -- Escape special chars: JSON text may contain actual newlines/tabs
    let text := text.replace "\\" "\\\\"
    let text := text.replace "\n" "\\n"
    let text := text.replace "\t" "\\t"
    let text := text.replace "\r" "\\r"
    "\"" ++ text ++ "\""
  else if kind == "RegularExpressionLiteral" then
    -- Render regex as a string literal: /pattern/flags → "/pattern/flags"
    -- Must escape backslashes/quotes (matches TS JSON.stringify behavior)
    let text := nodeText j
    "\"" ++ escapeLitStr text ++ "\""
  else if kind == "TrueKeyword" then "true"
  else if kind == "FalseKeyword" then "false"
  else if kind == "NullKeyword" || kind == "UndefinedKeyword" then "none"
  else if kind == "Identifier" then sanitizeId (nodeText j)
  else if kind == "ThisKeyword" then "self"
  else if kind == "AsExpression" then
    let inner := (fieldNode j "expression").map re |>.getD "default"
    -- Cast to Error → access .val (catch variables are TSError wrappers)
    let typeName := (fieldNode j "type").bind (fun t =>
      if nodeKind t == "TypeReference" then
        let fromTypeName := (fieldNode t "typeName").map nodeText
        let fromAlias := resolvedType t |>.bind (fun rt => getField rt "aliasName" |>.bind getStr)
        fromTypeName.orElse (fun _ => fromAlias)
      else none)
    let isError := match typeName with
      | some n => n == "Error" || n.endsWith "Error" | none => false
    if isError then inner ++ ".val" else inner
  else if kind == "SatisfiesExpression" || kind == "NonNullExpression" then
    (fieldNode j "expression").map re |>.getD "default"
  else if kind == "ParenthesizedExpression" then
    "(" ++ ((fieldNode j "expression").map re |>.getD "default") ++ ")"
  else if kind == "BinaryExpression" then
    let leftJ := fieldNode j "left"
    let rightJ := fieldNode j "right"
    let left := leftJ.map re |>.getD "default"
    let right := rightJ.map re |>.getD "default"
    let opKind := (fieldNode j "operatorToken").map nodeKind |>.getD ""
    -- Null coalescing: x ?? y → Option.getD x y
    if opKind == "QuestionQuestionToken" then
      let right := match rightJ with
        | some rj => parenIfCompoundExpr rj right | none => right
      "Option.getD " ++ left ++ " " ++ right
    -- Assignment: x = y → let x := y (rendered as statement context)
    else if opKind == "FirstAssignment" || opKind == "EqualsToken" then
      "let " ++ left ++ " := " ++ right
    -- Compound +=: merge LHS into s!"..." when RHS is safe template
    else if opKind == "FirstCompoundAssignment" || opKind == "PlusEqualsToken" then
      let rj := rightJ.getD default
      if nodeKind rj == "TemplateExpression" then
        let headText := (fieldNode rj "head").map nodeText |>.getD ""
        let spans := fieldArr rj "templateSpans"
        let allSafe := spans.all fun span =>
          let ek := (fieldNode span "expression").map nodeKind |>.getD ""
          ek == "Identifier" || ek == "PropertyAccessExpression"
        let allLitsSafe := !(headText.any (fun c => c == '{' || c == '}' || c == '"' || c == '\\')) &&
          spans.all fun span =>
            let lit := (fieldNode span "literal").map nodeText |>.getD ""
            !(lit.any (fun c => c == '{' || c == '}' || c == '"' || c == '\\'))
        if allSafe && allLitsSafe then
          let parts := spans.foldl (fun acc span =>
            let expr := (fieldNode span "expression").map re |>.getD ""
            let lit := (fieldNode span "literal").map nodeText |>.getD ""
            acc ++ "{" ++ expr ++ "}" ++ lit) headText
          "let " ++ left ++ " := s!\"{" ++ left ++ "}" ++ parts ++ "\""
        else "let " ++ left ++ " := " ++ left ++ " ++ " ++ right
      else "let " ++ left ++ " := " ++ left ++ " ++ " ++ right
    else
      -- Type-aware operator: PlusToken on strings → ++ (concat), otherwise +
      let op := if opKind == "PlusToken" then
        let isStringConcat := isStringTyped j ||
          (match leftJ with | some lj => hasStringType lj | none => false) ||
          (match rightJ with | some rj => hasStringType rj | none => false)
        if isStringConcat then "++" else "+"
      else mapBinOpSym opKind
      let left := match leftJ with | some lj => parenBinOperand lj left opKind | none => left
      let right := match rightJ with
        | some rj => parenBinOperand rj right opKind
        | none => right
      left ++ " " ++ op ++ " " ++ right
  else if kind == "PropertyAccessExpression" then
    let obj := (fieldNode j "expression").map re |>.getD "default"
    let field := (fieldNode j "name").map nodeText |>.getD ""
    -- Optional chaining: obj?.field → obj.bind (fun _oc => some _oc.field)
    let hasQuestionDot := (fieldNode j "questionDotToken").isSome
    if hasQuestionDot then
      obj ++ ".bind (fun _oc => some _oc." ++ field ++ ")"
    else
    -- .tag on inductive/union type aliases → (sorry : String)
    -- Matches TS IR lowerer's isInductiveType check for Effect, IRType, BinOp, UnOp
    let isInductiveTagAccess := field == "tag" && match fieldNode j "expression" with
      | some objJ =>
        let alias := resolvedType objJ |>.bind (fun rt => getField rt "aliasName" |>.bind getStr)
        match alias with
        | some n => n == "IRType" || n == "Effect" || n == "BinOp" || n == "UnOp"
        | none => false
      | none => false
    if isInductiveTagAccess then "(sorry : String)"
    else
    -- Discriminated union field substitution: s.radius → radius
    match substFieldAccess ctx obj field with
    | some bound => bound
    | none =>
      -- Global property rewriting: Math.PI → literal, etc.
      let fullName := obj ++ "." ++ field
      match fullName with
      | "Math.PI" => "3.14159265358979"
      | _ =>
        let objJ := fieldNode j "expression"
        let isStr := match objJ with | some oj => hasStringType oj | none => false
         let mapped := if field == "length" then (if isStr then "length" else "size")
          else mapFieldName field
        obj ++ "." ++ mapped
  else if kind == "CallExpression" then
    let fnJ := fieldNode j "expression"
    -- this.method(args) → method self args (matches TS lowerApp self-method rewriting)
    let isSelfMethodCall := match fnJ with
      | some fnNode =>
        nodeKind fnNode == "PropertyAccessExpression" &&
        ((fieldNode fnNode "expression").map nodeKind |>.getD "") == "ThisKeyword"
      | none => false
    if isSelfMethodCall then
      let methodName := match fnJ with
        | some fnNode => (fieldNode fnNode "name").map nodeText |>.getD "default"
        | none => "default"
      let args := (fieldArr j "arguments").map fun a =>
        if nodeKind a == "SpreadElement" then
          (fieldNode a "expression").map re |>.getD "default"
        else parenIfCompoundExpr a (re a)
      let allArgs := #["self"] ++ args
      methodName ++ " " ++ String.intercalate " " allArgs.toList
    else
    -- For method calls with args, wrap multi-arg call objects in parens
    -- (matches TS lowerMethodCall using lowerExprP for obj)
    let fn := match fnJ with
      | some fnNode =>
        if nodeKind fnNode == "PropertyAccessExpression" && (fieldArr j "arguments").size > 0 then
          let innerObjJ := fieldNode fnNode "expression"
          let innerObj := innerObjJ.map re |>.getD "default"
          let innerObj := match innerObjJ with
            | some ioj =>
              if nodeKind ioj == "CallExpression" && (fieldArr ioj "arguments").size >= 2 then
                "(" ++ innerObj ++ ")"
              else innerObj
            | none => innerObj
          let field := (fieldNode fnNode "name").map nodeText |>.getD ""
          let objJ2 := fieldNode fnNode "expression"
          let isStr := match objJ2 with | some oj => hasStringType oj | none => false
          let mapped := if field == "length" then (if isStr then "length" else "size")
            else mapFieldName field
          innerObj ++ "." ++ mapped
        else re fnNode
      | none => "default"
    let args := (fieldArr j "arguments").map fun a =>
      if nodeKind a == "SpreadElement" then
        (fieldNode a "expression").map re |>.getD "default"
      else parenIfCompoundExpr a (re a)
    let rewritten := rewriteMethodCall fnJ fn args
    match rewritten with
    | some r => r
    | none => if args.size == 0 then fn
              else fn ++ " " ++ String.intercalate " " args.toList
  else if kind == "ReturnStatement" then
    (fieldNode j "expression").map re |>.getD "()"
  else if kind == "PrefixUnaryExpression" then
    let operandJ := fieldNode j "operand"
    let operand := operandJ.map re |>.getD "default"
    let opCode := fieldNat j "operator"
    let op := if opCode == 53 then "!" else if opCode == 40 then "-" else "!"
    -- Parenthesize compound operands (matches TS lowerExprP/needsParens)
    let operand := match operandJ with
      | some oj => parenIfCompoundExpr oj operand | none => operand
    op ++ operand
  else if kind == "ConditionalExpression" then
    let c := (fieldNode j "condition").map (renderIfCondition re) |>.getD "default"
    let t := (fieldNode j "whenTrue").map re |>.getD "default"
    let f := (fieldNode j "whenFalse").map re |>.getD "default"
    s!"if {c} then {t} else {f}"
  else if kind == "TemplateExpression" then
    let headText := (fieldNode j "head").map nodeText |>.getD ""
    let spans := fieldArr j "templateSpans"
    let isSafe := spans.all fun span =>
      let ek := (fieldNode span "expression").map nodeKind |>.getD ""
      ek == "Identifier" || ek == "PropertyAccessExpression" ||
      ek == "StringLiteral" || ek == "NumericLiteral" ||
      ek == "TrueKeyword" || ek == "FalseKeyword"
     -- hasLiteral: at least one non-empty string literal part must exist for s!"..."
    -- Without literal text, TS trySInterp returns null → plain ++ concatenation
    let hasLiteral := headText != "" || spans.any fun span =>
      let lit := (fieldNode span "literal").map nodeText |>.getD ""
      lit != ""
    -- hasUnsafeChars: check for {, }, ", \ in string parts
    let hasUnsafeChars := headText.any (fun c => c == '{' || c == '}' || c == '"' || c == '\\') ||
      spans.any fun span =>
        let lit := (fieldNode span "literal").map nodeText |>.getD ""
        lit.any (fun c => c == '{' || c == '}' || c == '"' || c == '\\')
     if isSafe && hasLiteral && !hasUnsafeChars then
       let parts := spans.foldl (fun acc span =>
         let expr := (fieldNode span "expression").map re |>.getD ""
         let lit := (fieldNode span "literal").map nodeText |>.getD ""
         acc ++ "{" ++ expr ++ "}" ++ lit) headText
       "s!\"" ++ parts ++ "\""
     else if isSafe && (!hasLiteral || hasUnsafeChars) then
       -- All safe but no literal text OR unsafe chars → plain ++ chain (TS uses BinOp)
       -- Build individual pieces: expressions and escaped literal strings
       let pieces : Array String := Id.run do
         let mut parts : Array String := #[]
         if headText != "" then parts := parts.push ("\"" ++ escapeLitStr headText ++ "\"")
         for span in spans do
           let exprJ := fieldNode span "expression"
           let expr := exprJ.map re |>.getD ""
           let parenExpr := match exprJ with
             | some ej => parenIfCompoundExpr ej expr | none => expr
           parts := parts.push parenExpr
           let lit := (fieldNode span "literal").map nodeText |>.getD ""
           if lit != "" then parts := parts.push ("\"" ++ escapeLitStr lit ++ "\"")
         return parts
        match pieces.toList with
        | [] => "\"\""
        | [x] => x
        | x :: rest => rest.foldl (fun acc piece =>
          -- Left-nested parens matching TS lowerExprP wrapping BinOp children
          if (acc.splitOn " ++ ").length > 1 then "(" ++ acc ++ ") ++ " ++ piece
          else acc ++ " ++ " ++ piece) x
    else
      -- Hybrid approach: use s!"..." for the safe prefix, then ++ for the rest
      -- Find the first unsafe span
      let safePrefix := Id.run do
        let mut acc := headText
        for span in spans do
          let ek := (fieldNode span "expression").map nodeKind |>.getD ""
          let safe := ek == "Identifier" || ek == "PropertyAccessExpression" ||
            ek == "StringLiteral" || ek == "NumericLiteral" ||
            ek == "TrueKeyword" || ek == "FalseKeyword"
          if !safe then break
          let expr := (fieldNode span "expression").map re |>.getD ""
          let lit := (fieldNode span "literal").map nodeText |>.getD ""
          acc := acc ++ "{" ++ expr ++ "}" ++ lit
        return acc
      -- Count how many spans were safe
      let safePrefixSpanCount := Id.run do
        let mut count := 0
        for span in spans do
          let ek := (fieldNode span "expression").map nodeKind |>.getD ""
          let safe := ek == "Identifier" || ek == "PropertyAccessExpression" ||
            ek == "StringLiteral" || ek == "NumericLiteral" ||
            ek == "TrueKeyword" || ek == "FalseKeyword"
          if !safe then break
          count := count + 1
        return count
       let unsafeSpans := spans.toList.drop safePrefixSpanCount
      -- Check if safe prefix has literal text AND no unsafe chars
      let safePrefixHasLiteral := headText != "" || Id.run do
        let mut i := 0
        for span in spans do
          if i >= safePrefixSpanCount then break
          let lit := (fieldNode span "literal").map nodeText |>.getD ""
          if lit != "" then return true
          i := i + 1
        return false
      let safePrefixHasUnsafe := (headText != "" && headText.any (fun c => c == '{' || c == '}' || c == '"' || c == '\\')) || Id.run do
        let mut i := 0
        for span in spans do
          if i >= safePrefixSpanCount then break
          let lit := (fieldNode span "literal").map nodeText |>.getD ""
          if lit != "" && lit.any (fun c => c == '{' || c == '}' || c == '"' || c == '\\') then return true
          i := i + 1
        return false
      let canUseSInterpPrefix := safePrefixSpanCount > 0 && safePrefixHasLiteral && !safePrefixHasUnsafe
      if unsafeSpans.length == 0 && canUseSInterpPrefix then
        "s!\"" ++ safePrefix ++ "\""
      else
         -- Build individual pieces for ++ chain
        -- Build prefix pieces: s!"..." if safe with literals, individual exprs if not
        let prefixStr : Array String := if safePrefix == "" then #[]
          else if canUseSInterpPrefix then
            #["s!\"" ++ safePrefix ++ "\""]
           else if safePrefixSpanCount > 0 then
            -- Can't use s!"..." (no literals, or unsafe chars) → individual expressions
            Id.run do
              let mut parts : Array String := #[]
              if headText != "" then parts := parts.push ("\"" ++ escapeLitStr headText ++ "\"")
              let mut i := 0
              for span in spans do
                if i >= safePrefixSpanCount then break
                let expr := (fieldNode span "expression").map re |>.getD ""
                parts := parts.push expr
                let lit := (fieldNode span "literal").map nodeText |>.getD ""
                if lit != "" then parts := parts.push ("\"" ++ escapeLitStr lit ++ "\"")
                i := i + 1
              return parts
          else #["\"" ++ escapeLitStr safePrefix ++ "\""]
        -- Build tail pieces with separate entries for expr and literal
        let tailPieces := unsafeSpans.foldl (fun acc span =>
          let expr := (fieldNode span "expression").map re |>.getD ""
          let exprJ := fieldNode span "expression"
          let parenExpr := match exprJ with
            | some ej => parenIfCompoundExpr ej expr | none => expr
           let lit := (fieldNode span "literal").map nodeText |>.getD ""
           if lit == "" then acc.push parenExpr
           else acc.push parenExpr |>.push ("\"" ++ escapeLitStr lit ++ "\"")
        ) #[]
        let allPieces := prefixStr ++ tailPieces
        -- Left-fold with parens to match TS lowerer's left-associative BinOp tree
        -- The TS lowerer wraps each BinOp child via lowerExprP/needsParens,
        -- so the first piece (e.g. s!"...") gets wrapped in Paren too.
        match allPieces.toList with
        | [] => "\"\""
        | [x] => x
        | x :: rest =>
          -- Wrap initial piece in parens when it's s!"..." (matches TS Paren(SInterp(...)))
          -- Plain string literals don't get parens since TS needsParens(LitString) is false
          let x := if x.startsWith "s!\"" then "(" ++ x ++ ")" else x
          rest.foldl (fun acc piece =>
            if (acc.splitOn " ++ ").length > 1 then "(" ++ acc ++ ") ++ " ++ piece
            else acc ++ " ++ " ++ piece) x
  else if kind == "ObjectLiteralExpression" then
    let props := fieldArr j "properties"
    -- Try struct-literal → constructor rewrite for discriminated unions
    match tryStructToCtor reg props re with
    | some ctorApp => ctorApp
    | none =>
       let spreadBase := props.findSome? fun p =>
         if nodeKind p == "SpreadAssignment" then (fieldNode p "expression").map re else none
       let fields := props.filterMap fun p =>
        let pk := nodeKind p
        if pk == "PropertyAssignment" then
          let nameJ := fieldNode p "name"
          let rawName := nameJ.map nodeText |>.getD "_"
          let nameKind := nameJ.map nodeKind |>.getD ""
          let sanitizeChars := fun (s : String) => s.map fun c =>
            if c.isAlphanum || c == '_' || c == '.' || c == '!' || c == '?' || c == '\'' then c
            else '_'
          let n := if nameKind == "StringLiteral" then
            let srcText := nameJ.bind (fun nj => getField nj "sourceText" |>.bind getStr)
            match srcText with
            | some st => sanitizeChars st
            | none => sanitizeChars rawName
          else rawName
          let v := (fieldNode p "initializer").map re |>.getD "default"
          some (n ++ " := " ++ v)
        else if pk == "ShorthandPropertyAssignment" then
          let n := (fieldNode p "name").map nodeText |>.getD "_"
          some (n ++ " := " ++ n)
        else none
      match spreadBase with
      | some base =>
        if fields.size == 0 then base
        else "{ " ++ base ++ " with " ++ String.intercalate ", " fields.toList ++ " }"
      | none =>
        if fields.size == 0 then "{}" else "{ " ++ String.intercalate ", " fields.toList ++ " }"
  else if kind == "ArrayLiteralExpression" then
    let elems := (fieldArr j "elements").map fun e =>
      if nodeKind e == "SpreadElement" then
        (fieldNode e "expression").map re |>.getD "default"
      else re e
    "#[" ++ String.intercalate ", " elems.toList ++ "]"
  else if kind == "AwaitExpression" then
    (fieldNode j "expression").map re |>.getD "default"
  else if kind == "ArrowFunction" || kind == "FunctionExpression" then
    let params := (fieldArr j "parameters").map fun p => (fieldNode p "name").map nodeText |>.getD "_"
    let bodyJ := fieldNode j "body"
    let body := match bodyJ with
      | some b =>
         if isBlock b then
          let stmts := (fieldArr b "statements").filter fun s =>
            nodeKind s != "ContinueStatement" && nodeKind s != "BreakStatement"
          renderBlockStmtsInline re stmts
        -- Strip ParenthesizedExpression around ObjectLiteral in arrow body
        -- (TS uses parens to avoid {} being parsed as block; IR strips them)
        else if nodeKind b == "ParenthesizedExpression" then
          match fieldNode b "expression" with
          | some inner => if nodeKind inner == "ObjectLiteralExpression" then re inner else re b
          | none => re b
        else re b
      | none => "default"
    "fun " ++ String.intercalate " " params.toList ++ " => " ++ body
  else if kind == "ElementAccessExpression" then
    -- array[index] → obj.getD index default
    let obj := (fieldNode j "expression").map re |>.getD "default"
    let idxJ := fieldNode j "argumentExpression"
    let idx := idxJ.map re |>.getD "0"
    let idx := match idxJ with
      | some ij => parenIfCompoundExpr ij idx
      | none => idx
    obj ++ ".getD " ++ idx ++ " default"
  else if kind == "NewExpression" then
    let ctorName := (fieldNode j "expression").map nodeText |>.getD ""
    let args := (fieldArr j "arguments").map fun a => parenIfCompoundExpr a (re a)
    -- new URL(x) → URL.parse x
    if ctorName == "URL" then
      "URL.parse " ++ String.intercalate " " args.toList
    -- new Response(body, init) → mkResponse body init
    else if ctorName == "Response" then
      "mkResponse " ++ String.intercalate " " args.toList
    -- new Error(msg) → TSError.typeError msg
    else if ctorName == "Error" then
      "TSError.typeError " ++ String.intercalate " " args.toList
    -- new Promise(...) can't be expressed in Lean
    else if ctorName == "Promise" then "default"
    -- new Set([...]) → #[] (Set not representable in Lean, drop to empty array)
    else if ctorName == "Set" || ctorName == "Map" then "#[]"
    else ctorName ++ " " ++ String.intercalate " " args.toList
  else if kind == "TypeOfExpression" then
    let expr := (fieldNode j "expression").map re |>.getD "default"
    "(TSLean.typeOf " ++ expr ++ ")"
  else "default"

/-- Render expression with no substitution context and no union registry. -/
private partial def renderExpr (j : Json) : String := renderExprCtx #[] none j

-- ─── Body lowering ──────────────────────────────────────────────────────────────

private partial def lowerExpr (j : Json) : LeanExpr := .Lit (renderExpr j)
private partial def lowerExprCtx (reg : UnionRegistry) (ctx : SubstCtx) (j : Json) : LeanExpr :=
  .Lit (renderExprCtx reg ctx j)

/-- Detect if a switch scrutinee is a discriminant field access (e.g. s.kind, t.tag).
    Returns (objectVarName, discriminantField, matchedUnion). -/
private def detectDiscriminant (reg : UnionRegistry) (scrutJ : Json)
    (paramTypes : Array (String × String)) : Option (String × String × UnionInfo) :=
  if nodeKind scrutJ != "PropertyAccessExpression" then none
  else
    let field := (fieldNode scrutJ "name").map nodeText |>.getD ""
    if !isDiscriminantField field then none
    else
      let objJ := fieldNode scrutJ "expression"
      let objName := match objJ with | some o => nodeText o | none => ""
      if objName.isEmpty then none
      else
        -- Look up the union type from function parameter types
        let paramTypeName := (paramTypes.find? fun (n, _) => n == objName).map (·.2)
        match paramTypeName with
        | some tname => (lookupUnionByName reg tname).map fun u => (objName, field, u)
        | none => none

private def textContains (text : String) (sub : String) : Bool :=
  (text.splitOn sub).length > 1

private def isThisAssignment (j : Json) : Bool :=
  if nodeKind j == "ExpressionStatement" then
    match fieldNode j "expression" with
    | some e =>
      if nodeKind e == "BinaryExpression" then
        let opKind := (fieldNode e "operatorToken").map nodeKind |>.getD ""
        let isAssign := opKind == "FirstAssignment" || opKind == "EqualsToken" ||
          opKind == "FirstCompoundAssignment" || opKind == "PlusEqualsToken" ||
          opKind == "MinusEqualsToken"
        if isAssign then
          match fieldNode e "left" with
          | some l =>
            nodeKind l == "PropertyAccessExpression" &&
            ((fieldNode l "expression").map nodeKind |>.getD "") == "ThisKeyword"
          | none => false
        else false
      else if nodeKind e == "PostfixUnaryExpression" then
        -- this.count++ → modify count = self.count + 1
        match fieldNode e "operand" with
        | some op =>
          nodeKind op == "PropertyAccessExpression" &&
          ((fieldNode op "expression").map nodeKind |>.getD "") == "ThisKeyword"
        | none => false
      else false
    | none => false
  else false

private partial def bodyHasThisAssign (stmts : Array Json) : Bool :=
  stmts.any fun s =>
    isThisAssignment s ||
    (nodeKind s == "IfStatement" &&
      (let thenStmts := match fieldNode s "thenStatement" with
        | some t => if nodeKind t == "Block" then fieldArr t "statements" else #[t]
        | none => #[]
      let elseStmts := match fieldNode s "elseStatement" with
        | some e => if nodeKind e == "Block" then fieldArr e "statements" else #[e]
        | none => #[]
      bodyHasThisAssign thenStmts || bodyHasThisAssign elseStmts))

private partial def bodyHasThrow (stmts : Array Json) : Bool :=
  stmts.any fun s =>
    nodeKind s == "ThrowStatement" ||
    (nodeKind s == "IfStatement" &&
      (let thenStmts := match fieldNode s "thenStatement" with
        | some t => if nodeKind t == "Block" then fieldArr t "statements" else #[t]
        | none => #[]
      let elseStmts := match fieldNode s "elseStatement" with
        | some e => if nodeKind e == "Block" then fieldArr e "statements" else #[e]
        | none => #[]
      bodyHasThrow thenStmts || bodyHasThrow elseStmts))

private def isPureFieldReturn (stmts : Array Json) : Option String :=
  if stmts.size == 1 then
    let s := stmts.getD 0 default
    if nodeKind s == "ReturnStatement" then
      match fieldNode s "expression" with
      | some e =>
        if nodeKind e == "PropertyAccessExpression" then
          if ((fieldNode e "expression").map nodeKind |>.getD "") == "ThisKeyword" then
            (fieldNode e "name").map nodeText
          else none
        else none
      | none => none
    else none
  else none

/-- Wrap the tail expression of a monadic body with `pure`.
    Transforms `expr` → `Pure expr` at return positions (end of Let/Bind chains, both If branches). -/
private partial def wrapReturnsPure (e : LeanExpr) : LeanExpr :=
  match e with
  | .Let n t v b r => .Let n t v (wrapReturnsPure b) r
  | .Bind n v b => .Bind n v (wrapReturnsPure b)
  | .Seq stmts =>
    let arr := stmts
    if arr.size == 0 then .Pure (.Lit "()")
    else
      let last := arr.getD (arr.size - 1) (.Lit "()")
      arr.set! (arr.size - 1) (wrapReturnsPure last) |> .Seq
  | .If c t f => .If c (wrapReturnsPure t) (wrapReturnsPure f)
  | .Do b => .Do (wrapReturnsPure b)
  | .Pure _ | .Return _ | .Throw _ => e  -- already wrapped
  | .Lit "()" => e  -- unit continuation stays as-is
  | .Lit s => .Pure (.Lit s)
  | other => .Pure other

mutual

/-- Check if a LeanExpr contains any Bind nodes. -/
private partial def exprHasBindsCheck (e : LeanExpr) : Bool :=
  match e with
  | .Bind .. => true
  | .Seq stmts => stmts.any exprHasBindsCheck
  | .Let _ _ _ body _ => exprHasBindsCheck body
  | .If _ t f => exprHasBindsCheck t || exprHasBindsCheck f
  | .Do body => exprHasBindsCheck body
  | _ => false

/-- Check if a LeanExpr ends with a Return/Pure/Throw. -/
private partial def exprEndsWithReturn (e : LeanExpr) : Bool :=
  match e with
  | .Return .. | .Pure .. | .Throw .. => true
  | .If _ t f => exprEndsWithReturn t && exprEndsWithReturn f
  | .Match _ arms => arms.all fun arm => match arm with | .mk _ _ body => exprEndsWithReturn body
  | .Seq stmts => stmts.size > 0 && exprEndsWithReturn (stmts.getD (stmts.size - 1) default)
  | .Do body => exprEndsWithReturn body
  | .Let _ _ _ body _ => exprEndsWithReturn body
  | .Bind _ _ body => exprEndsWithReturn body
  | _ => false

private partial def lowerBodyR (reg : UnionRegistry) (paramTypes : Array (String × String))
    (j : Json) : LeanExpr :=
  if isBlock j then
    let stmts := fieldArr j "statements"
    let stmts := stmts.filter fun s =>
      nodeKind s != "ContinueStatement" && nodeKind s != "BreakStatement"
    if stmts.size == 0 then .Lit "()" else lowerStmtSeqR reg paramTypes stmts.toList
  else lowerBlockStmtR reg paramTypes j

private partial def lowerStmtSeqR (reg : UnionRegistry) (paramTypes : Array (String × String))
    : List Json → LeanExpr
  | [] => .Lit "()"
  | [s] => lowerBlockStmtR reg paramTypes s
  | s :: rest =>
    let kind := nodeKind s
    if kind == "IfStatement" then
      let cond := (fieldNode s "expression").map (renderIfCondition renderExpr) |>.getD "true"
      let thenB := (fieldNode s "thenStatement").map (lowerBodyR reg paramTypes) |>.getD (.Lit "()")
      let hasElse := (fieldNode s "elseStatement").isSome
      let elseB := match fieldNode s "elseStatement" with
        | some e => lowerBodyR reg paramTypes e | none => lowerStmtSeqR reg paramTypes rest
      let ifExpr := LeanExpr.If (.Lit cond) thenB elseB
      -- When the if has an explicit else branch, rest is not folded into elseB
      if hasElse && rest.length > 0 then
        .Seq #[ifExpr, lowerStmtSeqR reg paramTypes rest]
      else ifExpr
    else if kind == "VariableStatement" then
      let declList := fieldNode s "declarationList"
      let decls := declList.map (fieldArr · "declarations") |>.getD #[]
      if decls.size > 0 then
        let d := decls.getD 0 default
        let name := (fieldNode d "name").map nodeText |>.getD "_"
        let initJ := fieldNode d "initializer"
        -- Detect await: const x = await expr → let x ← expr (Bind node)
        let isAwait := match initJ with
          | some init => nodeKind init == "AwaitExpression" | none => false
        -- For uninitialized Option variables, use `none` instead of `default`
        let tyNode := fieldNode d "type"
        let tyMapped := tyNode.map mapTypeNode
        let isOptionTy := match tyMapped with
          | some (.TyApp (.TyName "Option") _) => true | _ => false
        let defaultVal := if isOptionTy then "none" else "default"
        let val := if isAwait then
            (initJ.bind (fieldNode · "expression")).map renderExpr |>.getD defaultVal
          else initJ.map renderExpr |>.getD defaultVal
        let cont := lowerStmtSeqR reg paramTypes rest
        if isAwait then .Bind name (.Lit val) cont
        else
          -- Only annotate when explicit type or new X() initializer (matches TS pipeline)
          let hasExplicitType := (fieldNode d "type").isSome
          let isNewExpr := match initJ with
            | some init => nodeKind init == "NewExpression" | none => false
          let ty := if hasExplicitType then (fieldNode d "type").map mapTypeNode
            else if isNewExpr then
              initJ.bind fun init =>
                (fieldNode init "expression").map fun c => .TyName (nodeText c)
            else none
          .Let name ty (.Lit val) cont false
      else lowerStmtSeqR reg paramTypes rest
    else if kind == "SwitchStatement" then
      let sw := lowerSwitchR reg paramTypes s
      match rest with | [] => sw | _ => .Seq #[sw, lowerStmtSeqR reg paramTypes rest]
    else if kind == "ExpressionStatement" then
      -- Check for assignment: x = expr → Let x value ((); rest)
      let exprJ := fieldNode s "expression"
      let isAssign := match exprJ with
        | some e => nodeKind e == "BinaryExpression" &&
          let opKind := (fieldNode e "operatorToken").map nodeKind |>.getD ""
          opKind == "FirstAssignment" || opKind == "EqualsToken"
        | none => false
      if isAssign then
        let e := exprJ.getD default
        let lname := (fieldNode e "left").map renderExpr |>.getD "_"
        let rval := (fieldNode e "right").map renderExpr |>.getD "default"
        let cont := lowerStmtSeqR reg paramTypes rest
        .Let lname none (.Lit rval) (.Seq #[.Lit "()", cont]) false
      else
        let expr := lowerBlockStmtR reg paramTypes s
        match rest with | [] => expr | _ => .Seq #[expr, lowerStmtSeqR reg paramTypes rest]
    else if kind == "ContinueStatement" || kind == "BreakStatement" then
      -- Continue/break terminates the sequence (rest is dead code)
      .Lit "()"
    else
      let expr := lowerBlockStmtR reg paramTypes s
      match rest with | [] => expr | _ => .Seq #[expr, lowerStmtSeqR reg paramTypes rest]

private partial def lowerBlockStmtR (reg : UnionRegistry) (paramTypes : Array (String × String))
    (j : Json) : LeanExpr :=
  let kind := nodeKind j
  if kind == "Block" then lowerBodyR reg paramTypes j
  else if kind == "ReturnStatement" then
    .Lit ((fieldNode j "expression").map renderExpr |>.getD "()")
  else if kind == "IfStatement" then
    let cond := (fieldNode j "expression").map (renderIfCondition renderExpr) |>.getD "true"
    let thenB := (fieldNode j "thenStatement").map (lowerBodyR reg paramTypes) |>.getD (.Lit "()")
    let elseB := (fieldNode j "elseStatement").map (lowerBodyR reg paramTypes) |>.getD (.Lit "()")
    .If (.Lit cond) thenB elseB
  else if kind == "SwitchStatement" then
    lowerSwitchR reg paramTypes j
  else if kind == "ForOfStatement" || kind == "ForInStatement" then
    let iterJ := fieldNode j "expression"
    let rawIter := iterJ.map renderExpr |>.getD "default"
    -- Parenthesize compound iterators (method calls with args, etc.)
    let iter := match iterJ with
      | some ij => parenIfCompoundExpr ij rawIter
      | none => rawIter
    let varJ := fieldNode j "initializer"
    let varName := match varJ with
      | some v =>
        if nodeKind v == "VariableDeclarationList" then
          let decls := fieldArr v "declarations"
          let d := decls.getD 0 default
          (fieldNode d "name").map nodeText |>.getD "_"
        else renderExpr v
      | none => "_"
    let bodyExpr := (fieldNode j "statement").map (lowerBodyR reg paramTypes) |>.getD (.Lit "()")
    -- If body has binds (← in it), wrap in `do`
    let hasBinds := exprHasBindsCheck bodyExpr
    let bodyExpr := if hasBinds then .Do bodyExpr else bodyExpr
    let lam := .Lam #[varName] bodyExpr
    -- Always wrap lambda in parens (matches TS needsParens for Lambda)
    let lam := .Paren lam
    .App (.Var "Array.forM") #[.Lit iter, lam]
  else if kind == "ForStatement" then
    -- for (let i = init; cond; incr) body → let rec _loop_POS := fun i => if cond then body; _loop(incr) else pure ()
    let pos := fieldNat j "pos"
    let loopName := s!"_loop_{pos}"
    let initDeclList := fieldNode j "initializer"
    let (iName, iVal) := match initDeclList with
      | some il =>
        if nodeKind il == "VariableDeclarationList" then
          let decls := fieldArr il "declarations"
          let d := decls.getD 0 default
          let n := (fieldNode d "name").map nodeText |>.getD "_i"
          let v := (fieldNode d "initializer").map renderExpr |>.getD "0"
          (n, v)
        else ("_i", "0")
      | none => ("_i", "0")
    let cond := (fieldNode j "condition").map renderExpr |>.getD "true"
    let incrJ := fieldNode j "incrementor"
    let incr := match incrJ with
      | some ij =>
        if nodeKind ij == "PostfixUnaryExpression" || nodeKind ij == "PrefixUnaryExpression" then
          let operand := (fieldNode ij "operand").map renderExpr |>.getD iName
          operand ++ " + 1"
        else renderExpr ij
      | none => iName ++ " + 1"
    let bodyExpr := (fieldNode j "statement").map (lowerBodyR reg paramTypes) |>.getD (.Lit "()")
    let recurse := .App (.Var loopName) #[.Lit ("(" ++ incr ++ ")")]
    let thenBody := .Seq #[bodyExpr, recurse]
    let loopBody := .Lam #[iName] (.If (.Lit cond) thenBody (.Pure (.Lit "()")))
    let callLoop := .App (.Var loopName) #[.Lit iVal]
    .Let loopName none loopBody callLoop true
  else if kind == "TryStatement" then
    -- try { body } catch (e) { handler } → tryCatch body (fun e => handler)
    -- Apply pure wrapping since try body is in monadic context
    let tryBody := (fieldNode j "tryBlock").map (fun b => wrapReturnsPure (lowerBodyR reg paramTypes b)) |>.getD (.Lit "()")
    let catchClause := fieldNode j "catchClause"
    let errName := catchClause.bind (fun cc =>
      (fieldNode cc "variableDeclaration").bind (fun vd =>
        (fieldNode vd "name").map nodeText))
      |>.getD "_e"
    let handler := catchClause.bind (fun cc =>
      (fieldNode cc "block").map (lowerBodyR reg paramTypes))
      |>.getD (.Lit "()")
    .TryCatch tryBody errName handler
  else if kind == "ThrowStatement" then
    let expr := (fieldNode j "expression").map renderExpr |>.getD "default"
    .Throw (.Lit expr)
  else if kind == "ExpressionStatement" then
    -- Check for assignment: x = expr → Let x value ()
    let exprJ := fieldNode j "expression"
    let isAssign := match exprJ with
      | some e => nodeKind e == "BinaryExpression" &&
        let opKind := (fieldNode e "operatorToken").map nodeKind |>.getD ""
        opKind == "FirstAssignment" || opKind == "EqualsToken"
      | none => false
    if isAssign then
      let e := exprJ.getD default
      let lname := (fieldNode e "left").map renderExpr |>.getD "_"
      let rval := (fieldNode e "right").map renderExpr |>.getD "default"
      .Let lname none (.Lit rval) (.Lit "()") false
    else
      exprJ.map (fun e => .Lit (renderExpr e)) |>.getD (.Lit "()")
  else if kind == "ContinueStatement" || kind == "BreakStatement" then .Lit "()"
  else .Lit (renderExpr j)

/-- Lower a SwitchStatement to a Match expression.
    If the scrutinee is a discriminant field access on a known union type,
    produce constructor patterns with field bindings and body substitution. -/
private partial def lowerSwitchR (reg : UnionRegistry) (paramTypes : Array (String × String))
    (j : Json) : LeanExpr :=
  let scrutJ := fieldNode j "expression"
  let disc := scrutJ.bind (detectDiscriminant reg · paramTypes)
  match disc with
  | some (objName, _field, union) => lowerDiscSwitch reg paramTypes objName union j
  | none =>
    -- Fallback: non-discriminated switch
    let scrutinee := scrutJ.map renderExpr |>.getD "default"
    let clauses := (fieldNode j "caseBlock").map (fieldArr · "clauses") |>.getD #[]
    -- Collect (pattern, bodyStmts) pairs, handling fall-through
    let clauseInfo := clauses.filterMap fun clause =>
      let ck := nodeKind clause
      if ck == "CaseClause" then
        let pat := (fieldNode clause "expression").map fun e =>
          let ek := nodeKind e
          if ek == "StringLiteral" then LeanPat.PLit ("\"" ++ nodeText e ++ "\"")
          else if ek == "NumericLiteral" then .PLit (nodeText e)
          else .PVar (renderExpr e)
        let pat := pat.getD .PWild
        let stmts := fieldArr clause "statements"
        let bodyStmts := stmts.filter fun s =>
          nodeKind s != "BreakStatement" && nodeKind s != "ContinueStatement"
        some (pat, bodyStmts)
      else if ck == "DefaultClause" then
        let stmts := fieldArr clause "statements"
        let bodyStmts := stmts.filter fun s =>
          nodeKind s != "BreakStatement" && nodeKind s != "ContinueStatement"
        some (LeanPat.PWild, bodyStmts)
      else none
    -- Handle fall-through: for empty-body cases, find next non-empty body
    let findBodyStmts (i : Nat) : Array Json :=
      let rec go (k : Nat) (fuel : Nat) : Array Json :=
        if fuel == 0 then #[]
        else if k >= clauseInfo.size then #[]
        else
          let (_, stmts) := clauseInfo.getD k (.PWild, #[])
          if stmts.size > 0 then stmts else go (k + 1) (fuel - 1)
      go i clauseInfo.size
    let arms := Id.run do
      let mut result : Array LeanMatchArm := #[]
      for i in List.range clauseInfo.size do
        let (pat, _) := clauseInfo.getD i (.PWild, #[])
        let bodyStmts := findBodyStmts i
        let body := if bodyStmts.size == 0 then .Lit "()"
          else if bodyStmts.size == 1 then lowerBlockStmtR reg paramTypes (bodyStmts.getD 0 default)
          else lowerStmtSeqR reg paramTypes bodyStmts.toList
        result := result.push (LeanMatchArm.mk pat none body)
      return result
    .Match (.Lit scrutinee) arms

/-- Lower a discriminated union switch: produce constructor patterns
    with field bindings and substituted bodies. -/
private partial def lowerDiscSwitch (reg : UnionRegistry) (paramTypes : Array (String × String))
    (objName : String) (union : UnionInfo) (j : Json) : LeanExpr :=
  let clauses := (fieldNode j "caseBlock").map (fieldArr · "clauses") |>.getD #[]
  let arms := clauses.filterMap fun clause =>
    let ck := nodeKind clause
    if ck == "CaseClause" then
      let caseExprJ := fieldNode clause "expression"
      let key := match caseExprJ with
        | some e => if nodeKind e == "StringLiteral" then nodeText e else ""
        | none => ""
      let variant := lookupVariant union key
      match variant with
      | some vi =>
        -- Constructor pattern: .Circle radius
        let localCtor := vi.ctorName.splitOn "." |>.getLast?.getD vi.ctorName
        let pat := if vi.fields.size == 0 then LeanPat.PCtor localCtor #[]
          else LeanPat.PCtor localCtor (vi.fields.map fun f => .PVar f)
        -- Build substitution context for body rendering
        let subst : MatchSubst := {
          scrutineeVar := objName
          fieldBindings := vi.fields.map fun f => (f, f)
          unionInfo := union
        }
        let stmts := fieldArr clause "statements"
        let bodyStmts := stmts.filter fun s =>
          nodeKind s != "BreakStatement" && nodeKind s != "ContinueStatement"
        let body := if bodyStmts.size == 0 then .Lit "()"
          else if bodyStmts.size == 1 then
            lowerBlockStmtSubst reg paramTypes (some subst) (bodyStmts.getD 0 default)
          else lowerStmtSeqSubst reg paramTypes (some subst) bodyStmts.toList
        some (LeanMatchArm.mk pat none body)
      | none =>
        -- Unknown variant, fall back to string literal pattern
        let pat := LeanPat.PLit ("\"" ++ key ++ "\"")
        let stmts := fieldArr clause "statements"
        let bodyStmts := stmts.filter fun s =>
          nodeKind s != "BreakStatement" && nodeKind s != "ContinueStatement"
        let body := if bodyStmts.size == 0 then .Lit "()"
          else if bodyStmts.size == 1 then lowerBlockStmtR reg paramTypes (bodyStmts.getD 0 default)
          else lowerStmtSeqR reg paramTypes bodyStmts.toList
        some (LeanMatchArm.mk pat none body)
    else if ck == "DefaultClause" then
      let stmts := fieldArr clause "statements"
      let bodyStmts := stmts.filter fun s =>
        nodeKind s != "BreakStatement" && nodeKind s != "ContinueStatement"
      let body := if bodyStmts.size == 0 then .Lit "()"
        else if bodyStmts.size == 1 then lowerBlockStmtR reg paramTypes (bodyStmts.getD 0 default)
        else lowerStmtSeqR reg paramTypes bodyStmts.toList
      some (LeanMatchArm.mk .PWild none body)
    else none
  -- Scrutinee is the variable itself (not obj.field)
  .Match (.Lit objName) arms

/-- Lower a return statement with substitution context (for match arm bodies). -/
private partial def lowerBlockStmtSubst (reg : UnionRegistry) (paramTypes : Array (String × String))
    (ctx : SubstCtx) (j : Json) : LeanExpr :=
  let kind := nodeKind j
  if kind == "ReturnStatement" then
    .Lit ((fieldNode j "expression").map (renderExprCtx reg ctx) |>.getD "()")
  else lowerBlockStmtR reg paramTypes j

private partial def lowerStmtSeqSubst (reg : UnionRegistry) (paramTypes : Array (String × String))
    (ctx : SubstCtx) : List Json → LeanExpr
  | [] => .Lit "()"
  | [s] => lowerBlockStmtSubst reg paramTypes ctx s
  | s :: rest =>
    let kind := nodeKind s
    if kind == "ReturnStatement" then
      .Lit ((fieldNode s "expression").map (renderExprCtx reg ctx) |>.getD "()")
    else
      let expr := lowerBlockStmtSubst reg paramTypes ctx s
      match rest with | [] => expr | _ => .Seq #[expr, lowerStmtSeqSubst reg paramTypes ctx rest]

/-- Lower a class method body to a LeanExpr, handling this-assignments as Modify. -/
private partial def lowerMethodBodyM (reg : UnionRegistry) (paramTypes : Array (String × String))
    (stmts : Array Json) (isMutating : Bool) (retTy : LeanTy) : LeanExpr :=
  match isPureFieldReturn stmts with
  | some field => .FieldAccess (.Var "self") field
  | none =>
    let inner := lowerMethodStmtsM reg paramTypes stmts isMutating
    -- Extract the inner return type from StateT/ExceptT wrapping
    let innerRetTy := match retTy with
      | .TyApp (.TyName "StateT") args => args.getD (args.size - 1) (.TyName "Unit")
      | .TyApp (.TyName "ExceptT") args => args.getD (args.size - 1) (.TyName "Unit")
      | _ => retTy
    let isUnitRet := match innerRetTy with | .TyName "Unit" => true | _ => false
    -- For mutating Unit-return methods, append `pure ()` if body doesn't end with return
    let inner := if isMutating && isUnitRet && !exprEndsWithReturn inner then
      .Seq #[inner, .Pure (.Lit "()")]
    else inner
    -- Also wrap in Do for pure let-chains (matches TS pureBodyNeedsDo)
    let pureNeedsDo := match inner with
      | .Let _ _ _ body _ => match body with
        | .Let .. | .If .. | .Match .. => true
        | _ => false
      | .Seq stmts => stmts.size > 1 && stmts.any (fun s => match s with | .Let .. => true | _ => false)
      | _ => false
    if isMutating || pureNeedsDo then .Do inner else inner

private partial def lowerMethodStmtsM (reg : UnionRegistry) (paramTypes : Array (String × String))
    (stmts : Array Json) (isMutating : Bool) : LeanExpr :=
  match stmts.toList with
  | [] => .Pure (.Lit "()")
  | [s] => lowerMethodStmtM reg paramTypes s isMutating true
  | s :: rest =>
    let kind := nodeKind s
    -- Chain if-without-else: make the else branch the rest of the statements
    if kind == "IfStatement" && (fieldNode s "elseStatement").isNone then
      let cond := (fieldNode s "expression").map (renderExprCtx reg none) |>.getD "true"
      let thenStmts := match fieldNode s "thenStatement" with
        | some t => if nodeKind t == "Block" then fieldArr t "statements" else #[t]
        | none => #[]
      let thenBody := lowerMethodStmtsM reg paramTypes thenStmts isMutating
      let elseBody := lowerMethodStmtsM reg paramTypes rest.toArray isMutating
      .If (.Lit cond) thenBody elseBody
    else if kind == "VariableStatement" then
      -- Chain Let: let x := val; <rest of stmts>
      let declList := fieldNode s "declarationList"
      let decls := declList.map (fieldArr · "declarations") |>.getD #[]
      if decls.size > 0 then
        let d := decls.getD 0 default
         let dname := (fieldNode d "name").map nodeText |>.getD "_"
        let initJ := fieldNode d "initializer"
        let isAwait := match initJ with
          | some init => nodeKind init == "AwaitExpression" | none => false
        let val := if isAwait then
            (initJ.bind (fieldNode · "expression")).map (renderExprCtx reg none) |>.getD "default"
          else initJ.map (renderExprCtx reg none) |>.getD "default"
        let cont := lowerMethodStmtsM reg paramTypes rest.toArray isMutating
        if isAwait then .Bind dname (.Lit val) cont
        else
          -- Only annotate when explicit type or new X() initializer (matches TS pipeline)
          let hasExplicitType := (fieldNode d "type").isSome
          let isNewExpr := match initJ with
            | some init => nodeKind init == "NewExpression" | none => false
           let ty := if hasExplicitType then (fieldNode d "type").map mapTypeNode
            else if isNewExpr then
              initJ.bind fun init =>
                let ctorName := (fieldNode init "expression").map nodeText |>.getD ""
                let typeArgs := fieldArr init "typeArguments"
                if ctorName == "Set" then
                  let elem := if typeArgs.size > 0 then mapTypeNode (typeArgs.getD 0 default) else .TyName "String"
                  some (.TyApp (.TyName "Array") #[elem])
                else if ctorName == "Map" then
                  let k := if typeArgs.size > 0 then mapTypeNode (typeArgs.getD 0 default) else .TyName "String"
                  let v := if typeArgs.size > 1 then mapTypeNode (typeArgs.getD 1 default) else .TyName "String"
                  some (.TyApp (.TyName "AssocMap") #[k, v])
                else (fieldNode init "expression").map fun c => .TyName (nodeText c)
            else none
           .Let dname ty (.Lit val) cont false
      else lowerMethodStmtsM reg paramTypes rest.toArray isMutating
    else
      let first := lowerMethodStmtM reg paramTypes s isMutating false
      let remainder := lowerMethodStmtsM reg paramTypes rest.toArray isMutating
      .Seq #[first, remainder]

private partial def lowerMethodStmtM (reg : UnionRegistry) (paramTypes : Array (String × String))
    (j : Json) (isMutating : Bool) (isLast : Bool) : LeanExpr :=
  let kind := nodeKind j
  if isThisAssignment j then
    match lowerThisAssignM reg j with
    | some (field, value) =>
      .Modify (.Lam #["s"] (.StructUpdate (.Var "s") #[.mk field value]))
    | none => .Lit "()"
  else if kind == "ReturnStatement" then
    let expr := (fieldNode j "expression").map (renderExprCtx reg none) |>.getD "()"
    if isMutating then .Pure (.Lit expr) else .Lit expr
  else if kind == "IfStatement" then
    let cond := (fieldNode j "expression").map (renderExprCtx reg none) |>.getD "true"
    let thenStmts := match fieldNode j "thenStatement" with
      | some t => if nodeKind t == "Block" then fieldArr t "statements" else #[t]
      | none => #[]
    let elseStmts := match fieldNode j "elseStatement" with
      | some e => if nodeKind e == "Block" then fieldArr e "statements" else #[e]
      | none => #[]
    let thenBody := lowerMethodStmtsM reg paramTypes thenStmts isMutating
    let elseBody := if elseStmts.size > 0 then
        lowerMethodStmtsM reg paramTypes elseStmts isMutating
      else if isLast && isMutating then .Pure (.Lit "()")
      else .Lit "()"
    .If (.Lit cond) thenBody elseBody
  else if kind == "ThrowStatement" then
    let exprJ := fieldNode j "expression"
    let errExpr := match exprJ with
    | some e =>
      if nodeKind e == "NewExpression" then
        let args := fieldArr e "arguments"
        let msg := if args.size > 0 then renderExprCtx reg none (args.getD 0 default) else "\"error\""
        "TSError.typeError " ++ msg
      else renderExprCtx reg none e
    | none => "\"error\""
    .Throw (.Lit errExpr)
  else if kind == "ExpressionStatement" then
    match fieldNode j "expression" with
    | some e =>
      -- Check for await this.state.storage.X(...) → pure sorry
      if nodeKind e == "AwaitExpression" then
        let innerRendered := (fieldNode e "expression").map (renderExprCtx reg none) |>.getD ""
        if textContains innerRendered "state.storage" || textContains innerRendered "self.state.storage" then
          .Pure (.Sorry none none)
        else .Lit innerRendered
      else
        let rendered := renderExprCtx reg none e
        if textContains rendered "state.storage" || textContains rendered "self.state.storage" then
          .Pure (.Sorry none none)
        else .Lit rendered
    | none => .Lit "()"
  else if kind == "VariableStatement" then
    let declList := fieldNode j "declarationList"
    let decls := declList.map (fieldArr · "declarations") |>.getD #[]
    if decls.size > 0 then
      let d := decls.getD 0 default
      let dname := (fieldNode d "name").map nodeText |>.getD "_"
      let initJ := fieldNode d "initializer"
      let val := initJ.map (renderExprCtx reg none) |>.getD "default"
      -- Only annotate when explicit type or new X() initializer (matches TS pipeline)
      let hasExplicitType := (fieldNode d "type").isSome
      let isNewExpr := match initJ with
        | some init => nodeKind init == "NewExpression" | none => false
           let ty := if hasExplicitType then (fieldNode d "type").map mapTypeNode
            else if isNewExpr then
              initJ.bind fun init =>
                let ctorName := (fieldNode init "expression").map nodeText |>.getD ""
                let typeArgs := fieldArr init "typeArguments"
                -- Map TS constructor names to Lean types
                if ctorName == "Set" then
                  let elem := if typeArgs.size > 0 then mapTypeNode (typeArgs.getD 0 default) else .TyName "String"
                  some (.TyApp (.TyName "Array") #[elem])
                else if ctorName == "Map" then
                  let k := if typeArgs.size > 0 then mapTypeNode (typeArgs.getD 0 default) else .TyName "String"
                  let v := if typeArgs.size > 1 then mapTypeNode (typeArgs.getD 1 default) else .TyName "String"
                  some (.TyApp (.TyName "AssocMap") #[k, v])
                else (fieldNode init "expression").map fun c => .TyName (nodeText c)
        else none
      .Let dname ty (.Lit val) (.Lit "()") false
    else .Lit "()"
  else if kind == "SwitchStatement" then
    lowerSwitchR reg paramTypes j
  else if kind == "ForOfStatement" || kind == "ForInStatement" then
    lowerBlockStmtR reg paramTypes j
  else .Lit (renderExprCtx reg none j)

private partial def lowerThisAssignM (reg : UnionRegistry) (j : Json) : Option (String × LeanExpr) :=
  match fieldNode j "expression" with
  | some e =>
    if nodeKind e == "PostfixUnaryExpression" then
      -- this.field++ or this.field-- → (field, self.field ± 1)
      match fieldNode e "operand" with
      | some op =>
        let field := (fieldNode op "name").map nodeText |>.getD ""
        let opCode := fieldNat e "operator"
        if opCode == 46 then some (field, .BinOp "+" (.FieldAccess (.Var "self") field) (.Lit "1"))
        else if opCode == 47 then some (field, .BinOp "-" (.FieldAccess (.Var "self") field) (.Lit "1"))
        else none
      | none => none
    else
      let left := fieldNode e "left"
      let right := fieldNode e "right"
      let opKind := (fieldNode e "operatorToken").map nodeKind |>.getD ""
      match left, right with
      | some l, some r =>
        let field := (fieldNode l "name").map nodeText |>.getD ""
        if opKind == "FirstAssignment" || opKind == "EqualsToken" then
          some (field, .Lit (renderExprCtx reg none r))
        else if opKind == "FirstCompoundAssignment" || opKind == "PlusEqualsToken" then
          some (field, .BinOp "+" (.FieldAccess (.Var "self") field) (.Lit (renderExprCtx reg none r)))
        else if opKind == "MinusEqualsToken" then
          some (field, .BinOp "-" (.FieldAccess (.Var "self") field) (.Lit (renderExprCtx reg none r)))
        else none
      | _, _ => none
  | none => none

end -- mutual

-- Legacy wrappers used by non-registry-aware callers
private partial def lowerBody (j : Json) : LeanExpr := lowerBodyR #[] #[] j

-- ─── Helpers ────────────────────────────────────────────────────────────────────

private partial def exprContainsName (e : LeanExpr) (name : String) : Bool :=
  match e with
  | .Lit s => (s.splitOn name).length > 1
  | .Var n => n == name
  | .If c t f => exprContainsName c name || exprContainsName t name || exprContainsName f name
  | .Let _ _ v b _ => exprContainsName v name || exprContainsName b name
  | .Seq stmts => stmts.any (exprContainsName · name)
  | .Do b | .Pure b | .Return b => exprContainsName b name
  | .Match scrut arms => exprContainsName scrut name ||
    arms.any (fun arm => match arm with | .mk _ _ body => exprContainsName body name)
  | .App fn args => exprContainsName fn name || args.any (exprContainsName · name)
  | .Lam _ body => exprContainsName body name
  | .Paren inner => exprContainsName inner name
  | .Throw val => exprContainsName val name
  | .Bind _ v b => exprContainsName v name || exprContainsName b name
  | .TryCatch body _ handler => exprContainsName body name || exprContainsName handler name
  | .Modify fn => exprContainsName fn name
  | _ => false

/-- Check if a body expression needs `do` wrapping (multiple lets).
    Matches TS pureBodyNeedsDo: Let→(Let|If|Match) or Seq with Let + length > 1. -/
private def needsDoWrap (e : LeanExpr) : Bool :=
  match e with
  | .Let _ _ _ body _ => match body with
    | .Let .. | .If .. | .Match .. => true
    | _ => false
  | .Seq stmts => stmts.size > 1 && stmts.any (fun s => match s with | .Let .. => true | _ => false)
  | _ => false

-- ─── Declaration lowering ───────────────────────────────────────────────────────

private def extractTypeParams (j : Json) : Array LeanTyParam :=
  (fieldArr j "typeParameters").map fun tp =>
    let name := (fieldNode tp "name").map nodeText |>.getD (nodeText tp)
    { name := name, explicit := true, constraints := none : LeanTyParam }

private partial def lowerParam (j : Json) : LeanParam :=
  let name := (fieldNode j "name").map nodeText |>.getD "_"
  let baseTy := match fieldNode j "type" with | some tn => mapTypeNode tn | none => mapResolvedType j
  -- Optional parameters (questionToken) get wrapped in Option
  let ty := if fieldBool j "questionToken" then .TyApp (.TyName "Option") #[baseTy] else baseTy
  -- Default value from initializer
  let def_ := (fieldNode j "initializer").map fun init => .Lit (renderExpr init)
  { name := name, ty := ty, default_ := def_ }

private def extractJSDocSummary (text : String) : Option String :=
  if !text.trimAsciiStart.toString.startsWith "/**" then none
  else
    let cleaned := text.replace "/**" "" |>.replace "*/" ""
    let descLines := (cleaned.splitOn "\n").foldl (fun acc line =>
      let stripped := line.replace "* " "" |>.trimAscii.toString
      let stripped := if stripped == "*" then "" else stripped
      if stripped.startsWith "@" || stripped.isEmpty then acc
      else acc.push stripped
    ) #[]
    let result := String.intercalate " " descLines.toList |>.trimAscii.toString
    if result.isEmpty then none else some result

private def isModuleJSDoc (text : String) : Bool :=
  text.trimAsciiStart.toString.startsWith "/**" && textContains text "@module"

private def extractDocComment (j : Json) : Option String :=
  (fieldArr j "leadingComments").findSome? fun c =>
    match getStr c with
    | some text =>
      if text.trimAsciiStart.toString.startsWith "/**" && !isModuleJSDoc text then extractJSDocSummary text else none
    | none => none

private def extractLeadingComment (j : Json) : Option String :=
  let comments := fieldArr j "leadingComments"
  if comments.size == 0 then none
  else
    let combined := String.intercalate "\n" (comments.toList.filterMap getStr)
    if combined.isEmpty then none else some combined

private partial def lowerVarStatement (j : Json) : Array LeanDecl :=
  let declList := fieldNode j "declarationList"
  let decls := declList.map (fieldArr · "declarations") |>.getD #[]
  decls.filterMap fun d =>
    let name := (fieldNode d "name").map nodeText |>.getD "_"
    let initJ := fieldNode d "initializer"
    -- Detect new Set([...]) / new Map([...]) → Array String type
    let initCtorName := match initJ with
      | some init => if nodeKind init == "NewExpression" then
          (fieldNode init "expression").map nodeText |>.getD ""
        else ""
      | none => ""
    let ty := if initCtorName == "Set" || initCtorName == "Map" then
        .TyApp (.TyName "Array") #[.TyName "String"]
      else match fieldNode d "type" with | some tn => mapTypeNode tn | none => mapResolvedType d
    let body := match initJ with
      | some init => lowerExpr init | none => .Default (some ty)
    some (.Def false name #[] #[] ty body none none none)

/-- Extract the type name from a parameter's type annotation for union lookup. -/
private def paramTypeName (j : Json) : Option String :=
  match fieldNode j "type" with
  | some tn =>
    if nodeKind tn == "TypeReference" then
      (fieldNode tn "typeName").bind (fun t => getStr t)
        |>.orElse fun _ => resolvedType tn |>.bind (fun rt => getField rt "aliasName" |>.bind getStr)
        |>.orElse fun _ => some (nodeText tn)
    else none
  | none =>
    resolvedType j |>.bind fun rt =>
      let flags := typeFlags rt
      if flags &&& TF_Union != 0 then
        let aliasName := fieldStr rt "aliasName"
        if !aliasName.isEmpty then some aliasName else none
      else none

/-- Check if statements contain variable reassignment (x = expr, not this.x = expr).
    Used to detect State effect for non-async functions. -/
private partial def bodyHasVarReassign (stmts : Array Json) : Bool :=
  stmts.any fun s =>
    let kind := nodeKind s
    if kind == "ExpressionStatement" then
      match fieldNode s "expression" with
      | some e =>
        if nodeKind e == "BinaryExpression" then
          let opKind := (fieldNode e "operatorToken").map nodeKind |>.getD ""
          let isAssign := opKind == "FirstAssignment" || opKind == "EqualsToken"
          if isAssign then
            match fieldNode e "left" with
            | some l => nodeKind l == "Identifier"
            | none => false
          else false
        else false
      | none => false
    else if kind == "IfStatement" then
      let thenStmts := match fieldNode s "thenStatement" with
        | some t => if nodeKind t == "Block" then fieldArr t "statements" else #[t]
        | none => #[]
      let elseStmts := match fieldNode s "elseStatement" with
        | some e => if nodeKind e == "Block" then fieldArr e "statements" else #[e]
        | none => #[]
      bodyHasVarReassign thenStmts || bodyHasVarReassign elseStmts
    else false

private partial def lowerFuncDeclR (reg : UnionRegistry) (j : Json) : Array LeanDecl :=
  let name := (fieldNode j "name").map nodeText |>.getD "_"
  let tyParams := extractTypeParams j
  let params := (fieldArr j "parameters").map lowerParam
  let retTy := match fieldNode j "type" with | some tn => mapTypeNode tn | none => mapResolvedType j
  -- Build param name → type name mapping for discriminant detection
  let paramTypes := (fieldArr j "parameters").filterMap fun p =>
    let pname := (fieldNode p "name").map nodeText |>.getD ""
    match paramTypeName p with
    | some tname => some (pname, tname)
    | none => none
  -- Detect async and combined effects
  let mods := fieldArr j "modifiers"
  let isAsync := mods.any fun m => nodeKind m == "AsyncKeyword"
  let bodyStmts := match fieldNode j "body" with
    | some b => fieldArr b "statements" | none => #[]
  let bodyText := bodyStmts.foldl (fun acc s => acc ++ toString s) ""
  let hasThrowInBody := textContains bodyText "ThrowStatement"
  let hasTryCatch := textContains bodyText "TryStatement"
  let hasVarReassign := textContains bodyText "FirstAssignment"
  -- Variable reassignment detection (x = expr, not this.x = expr)
  let hasBodyVarReassign := bodyHasVarReassign bodyStmts
  -- Combined effects: State + Except when there's try/catch + throw + mutable vars
  let retTy := if isAsync && hasThrowInBody && (hasTryCatch || hasVarReassign) then
    .TyApp (.TyName "StateT") #[.TyName "Unit",
      .TyApp (.TyName "ExceptT") #[.TyName "String", .TyName "IO"], retTy]
  else if isAsync then .TyApp (.TyName "IO") #[retTy]
  -- Non-async with variable reassignment → StateT Unit IO
  else if hasBodyVarReassign then
    .TyApp (.TyName "StateT") #[.TyName "Unit", .TyName "IO", retTy]
  else retTy
  let body := match fieldNode j "body" with
    | some b => lowerBodyR reg paramTypes b
    | none => .Default (some retTy)
  -- In async functions or state functions, wrap tail expressions with `pure`
  let body := if isAsync || hasBodyVarReassign then wrapReturnsPure body else body
  let body := if needsDoWrap body || isAsync || hasBodyVarReassign then .Do body else body
  let isPartial := exprContainsName body name
  let docComment := extractDocComment j
  let comment := if docComment.isSome then none else extractLeadingComment j
  #[.Def isPartial name tyParams params retTy body none docComment comment]

/-- Resolve the type of an optional member field to match TS parser behavior.
    The TS parser uses checker.getTypeOfSymbol (which includes undefined for optional),
    then mapType handles the T|undefined union. The result is wrapped by the caller. -/
private partial def resolveOptionalFieldType (m : Json) : LeanTy :=
  match fieldNode m "type" with
  | some tn =>
    if nodeKind tn == "TypeReference" then
      -- TypeReference: may resolve to complex union (alias expanded like LeanExpr)
      let memberRt := resolvedType m
      match memberRt with
      | some mrt =>
        let flags := typeFlags mrt
        if flags &&& TF_Union != 0 then
          let types := fieldArr mrt "types"
          let nonUndef := types.filter fun t =>
            let tf := typeFlags t; tf &&& TF_Undefined == 0 && tf &&& TF_Null == 0
          if nonUndef.size > 1 then
            -- Complex union (alias expanded) → take first member → String/etc
            mapResolvedTypeJson (nonUndef.getD 0 default)
          else mapResolvedType m
        else mapResolvedType m
      | none => mapTypeNode tn
    else
      -- Non-TypeReference (ArrayType, StringKeyword, etc.):
      -- Use resolved type to match TS mapType(T|undefined) behavior.
      -- For T that doesn't expand (string → 1 member): gives Option(T)
      -- For T that expands (boolean → true|false → 2 members): falls through → T
      -- BUT: resolved type loses array info (string[] → {}) → detect and fall back
      let memberRt := resolvedType m
      match memberRt with
      | some mrt =>
        let flags := typeFlags mrt
        if flags &&& TF_Union != 0 then
          let types := fieldArr mrt "types"
          let nonUndef := types.filter fun t =>
            let tf := typeFlags t; tf &&& TF_Undefined == 0 && tf &&& TF_Null == 0
          if nonUndef.size == 1 && nonUndef.size < types.size then
            let inner := mapResolvedTypeJson (nonUndef.getD 0 default)
            let innerIsUseful := match inner with
              | .TyName n => n != "{}" && n != "Unit"
              | _ => true
            if innerIsUseful then .TyApp (.TyName "Option") #[inner]
            else .TyApp (.TyName "Option") #[mapTypeNode tn]
          else mapResolvedTypeJson (nonUndef.getD 0 default)
        else mapTypeNode tn
      | none => mapTypeNode tn
  | none => mapResolvedType m

private partial def lowerInterfaceDecl (j : Json) : Array LeanDecl :=
  let name := (fieldNode j "name").map nodeText |>.getD "_"
  let tyParams := extractTypeParams j
  let members := fieldArr j "members"
  let fields := members.filterMap fun m =>
    if isPropertySignature m then
      let fn := (fieldNode m "name").map nodeText |>.getD "_"
      let isOptional := fieldBool m "questionToken"
      let fty := if isOptional then
        .TyApp (.TyName "Option") #[resolveOptionalFieldType m]
      else
        match fieldNode m "type" with | some tn => mapTypeNode tn | none => mapResolvedType m
      some (LeanField.mk fn fty none)
    else none
  let comment := extractLeadingComment j
  #[.Structure name tyParams fields none DEFAULT_DERIVING comment]

-- Excluded fields for DurableObject state structs
private def DO_EXCLUDED_FIELDS : Array String := #["state", "storage", "env", "config"]
private def DO_EXCLUDED_TYPES : Array String := #["DurableObjectState", "Env", "CompilerHost"]

private partial def lowerClassDecl (reg : UnionRegistry) (j : Json) : Array LeanDecl :=
  let name := (fieldNode j "name").map nodeText |>.getD "_"
  let tyParams := extractTypeParams j
  let members := fieldArr j "members"
  let stateName := name ++ "State"
  -- Build state type with generic args
  let stateType := if tyParams.size > 0 then
    .TyApp (.TyName stateName) (tyParams.map fun tp => .TyName tp.name)
  else .TyName stateName
  -- Detect DurableObject class: has a DurableObjectState constructor param
  let isDO := members.any fun m =>
    nodeKind m == "Constructor" && (fieldArr m "parameters").any fun p =>
      let typeName := (fieldNode p "type").bind (fieldNode · "typeName") |>.map nodeText |>.getD ""
      typeName == "DurableObjectState"
  -- Extract property fields (excluding DO framework fields)
  let fields := members.filterMap fun m =>
    if isPropertyDeclaration m || isPropertySignature m then
      let fn := (fieldNode m "name").map nodeText |>.getD "_"
      -- Exclude DO framework fields
      if isDO && (DO_EXCLUDED_FIELDS.contains fn) then none
      else
        let fty := match fieldNode m "type" with | some tn => mapTypeNode tn | none => mapResolvedType m
        -- Also exclude by type name
        let excludeByType := isDO && match fty with
          | .TyName n => DO_EXCLUDED_TYPES.contains n
          | _ => false
        if excludeByType then none
        else some (LeanField.mk fn fty none)
    else none
  -- For DO classes, generate simple init constant instead of constructor method
  let ctorDecls := if isDO then
    -- DO init: simple struct literal with default field values
    let fieldInits := fields.map fun f =>
      let defVal := match f.ty with
        | .TyName "Float" => .TypeAnnot (.Lit "0") (.TyName "Float")
        | .TyName "String" => .Lit "\"\""
        | .TyName "Bool" => .Lit "false"
        | .TyApp (.TyName "Array") _ => .ArrayLit #[]
        | _ => .Default none
      LeanFieldVal.mk f.name defVal
    #[.Def false (name ++ ".init") #[] #[] stateType (.StructLit fieldInits) none none none]
  else
    -- Regular class: extract constructor as init method
    members.filterMap fun m =>
      if nodeKind m == "Constructor" then
        let params := (fieldArr m "parameters").map fun p =>
          let pname := (fieldNode p "name").map nodeText |>.getD "_"
          let pty := match fieldNode p "type" with | some tn => mapTypeNode tn | none => mapResolvedType p
          let pdef := match fieldNode p "initializer" with
            | some init => some (.Lit (renderExpr init))
            | none => none
          { name := pname, ty := pty, default_ := pdef : LeanParam }
        let stmts := match fieldNode m "body" with
          | some b => fieldArr b "statements" | none => #[]
        let selfParam : LeanParam := { name := "self", ty := stateType }
        let allParams := #[selfParam] ++ params
        let retTy := .TyApp (.TyName "StateT") #[stateType, .TyName "IO", .TyName "Unit"]
        let body := lowerMethodBodyM reg #[] stmts true retTy
        some (.Def false (name ++ ".init") tyParams allParams retTy body none none none)
      else none
  -- Extract methods as standalone defs
  let methods := members.filterMap fun m =>
    if isMethodDeclaration m then
      let mname := (fieldNode m "name").map nodeText |>.getD "_"
      let params := (fieldArr m "parameters").map fun p =>
        let pname := (fieldNode p "name").map nodeText |>.getD "_"
        let pty := match fieldNode p "type" with | some tn => mapTypeNode tn | none => mapResolvedType p
        { name := pname, ty := pty : LeanParam }
      let retTy := match fieldNode m "type" with | some tn => mapTypeNode tn | none => mapResolvedType m
      let stmts := match fieldNode m "body" with
        | some b => fieldArr b "statements" | none => #[]
      -- Detect mutation and throw effects
      let isMutating := bodyHasThisAssign stmts
      let hasThrow := bodyHasThrow stmts
      let selfParam : LeanParam := { name := "self", ty := stateType }
      let allParams := #[selfParam] ++ params
      -- Check for pure field return (e.g., getCount → self.count)
      let pureReturn := isPureFieldReturn stmts
      let (retTy, body) := match pureReturn with
      | some _field =>
        -- Pure field return: no monad wrapping
        (retTy, lowerMethodBodyM reg #[] stmts false retTy)
      | none =>
        -- Determine effect-based return type
        let wrappedRet := if isMutating && hasThrow then
            .TyApp (.TyName "StateT") #[stateType, .TyApp (.TyName "ExceptT") #[.TyName "String", .TyName "IO"], retTy]
          else if isMutating then
            .TyApp (.TyName "StateT") #[stateType, .TyName "IO", retTy]
          else retTy
        (wrappedRet, lowerMethodBodyM reg #[] stmts isMutating wrappedRet)
      some (.Def false (name ++ "." ++ mname) tyParams allParams retTy body none none none)
    else none
  -- Interleave blanks between methods
  let allMethods := ctorDecls ++ methods
  let methodDecls := allMethods.foldl (fun acc m => acc ++ #[.Blank, m]) #[]
  -- Comment + state struct + methods
  let result := #[LeanDecl.Comment ("State for " ++ name)]
  let result := result.push (.Structure stateName tyParams fields none DEFAULT_DERIVING none)
  -- For DO classes, wrap init + methods in inner namespace
  if isDO then
    -- Remove leading blank from method decls for namespace body
    let nsDecls := if methodDecls.size > 0 && (match methodDecls.getD 0 default with | .Blank => true | _ => false)
      then methodDecls.extract 1 methodDecls.size ++ #[.Blank]
      else methodDecls ++ #[.Blank]
    let result := result.push .Blank
    let result := result.push (.Namespace name nsDecls)
    result
  else
    let result := result ++ methodDecls
    result

private def hasDiscriminantField (j : Json) : Bool :=
  let members := fieldArr j "members"
  members.any fun m =>
    let fname := (fieldNode m "name").map nodeText |>.getD ""
    let isDisc := isDiscriminantField fname
    let hasLiteralType := match fieldNode m "type" with
      | some tn => nodeKind tn == "LiteralType"
      | none => false
    isDisc && hasLiteralType

/-- Extract discriminated union info from variant JSON nodes for the registry. -/
private def extractUnionInfo (name : String) (variants : Array Json) : UnionInfo :=
  -- Find the discriminant field name from the first variant
  let discField := variants.foldl (fun acc v =>
    if !acc.isEmpty then acc else
    let members := fieldArr v "members"
    let dm := members.find? fun m => isDiscriminantField ((fieldNode m "name").map nodeText |>.getD "")
    match dm with | some m => (fieldNode m "name").map nodeText |>.getD "" | none => acc
  ) ""
  let variantEntries := variants.filterMap fun v =>
    let members := fieldArr v "members"
    let discMember := members.find? fun m =>
      isDiscriminantField ((fieldNode m "name").map nodeText |>.getD "")
    match discMember with
    | some dm =>
      let litType := fieldNode dm "type"
      let litText := litType.bind fun lt => (fieldNode lt "literal").map nodeText
      let key := litText.getD ""
      let ctorName := key.capitalize
      let fields := members.filterMap fun m =>
        let fname := (fieldNode m "name").map nodeText |>.getD ""
        if isDiscriminantField fname then none else some fname
      some (key, { ctorName := name ++ "." ++ ctorName, fields := fields : VariantInfo })
    | none => none
  { typeName := name, discField := discField, variants := variantEntries }

private partial def lowerDiscriminatedUnion (name : String) (tyParams : Array LeanTyParam)
    (variants : Array Json) (comment : Option String := none) : Array LeanDecl :=
  let ctors := variants.map fun v =>
    let members := fieldArr v "members"
    let discMember := members.find? fun m =>
      let fname := (fieldNode m "name").map nodeText |>.getD ""
      isDiscriminantField fname
    let ctorName := match discMember with
      | some dm =>
        let litType := fieldNode dm "type"
        let litText := litType.bind fun lt => (fieldNode lt "literal").map nodeText
        (litText.getD "Unknown").capitalize
      | none => "Unknown"
    let fields := members.filterMap fun m =>
      let fname := (fieldNode m "name").map nodeText |>.getD ""
      if isDiscriminantField fname then none
      else
        let isOptional := fieldBool m "questionToken"
        let fty := if isOptional then
          .TyApp (.TyName "Option") #[resolveOptionalFieldType m]
        else
          match fieldNode m "type" with
          | some tn => mapTypeNode tn | none => mapResolvedType m
        some (some fname, fty)
    LeanCtor.mk ctorName fields
  #[.Inductive name tyParams ctors DEFAULT_DERIVING comment]

private partial def lowerTypeAliasDecl (j : Json) : Array LeanDecl :=
  let name := (fieldNode j "name").map nodeText |>.getD "_"
  let tyParams := extractTypeParams j
  let comment := extractLeadingComment j
  -- Check for discriminated union pattern: type X = {kind:'A',...} | {kind:'B',...}
  let typeNode := fieldNode j "type"
  match typeNode with
  | some tn =>
    if nodeKind tn == "UnionType" then
      let types := fieldArr tn "types"
      -- Check for discriminated union: {kind:'A',...} | {kind:'B',...}
      let isDiscriminated := types.size > 0 && types.all fun t =>
        nodeKind t == "TypeLiteral" && hasDiscriminantField t
      -- Check for string enum: 'a' | 'b' | 'c'
      let isStringEnum := types.size > 0 && types.all fun t =>
        nodeKind t == "LiteralType"
      if isDiscriminated then
        lowerDiscriminatedUnion name tyParams types comment
      else if isStringEnum then
        let ctors := types.map fun t =>
          let text := (fieldNode t "literal").map nodeText |>.getD "Unknown"
          LeanCtor.mk text.capitalize #[]
        #[.Inductive name tyParams ctors DEFAULT_DERIVING comment]
      else
        #[.Abbrev name tyParams (mapTypeNode tn) comment]
    else
      #[.Abbrev name tyParams (mapTypeNode tn) comment]
  | none => #[.Abbrev name tyParams (.TyName "Unit") comment]

/-- Check if a TypeLiteral has a discriminant field (kind/tag/type with string literal). -/
private partial def lowerEnumDecl (j : Json) : Array LeanDecl :=
  let name := (fieldNode j "name").map nodeText |>.getD "_"
  let ctors := (fieldArr j "members").map fun m =>
    LeanCtor.mk ((fieldNode m "name").map nodeText |>.getD "_") #[]
  #[.Inductive name #[] ctors DEFAULT_DERIVING none]

private partial def lowerStatementR (reg : UnionRegistry) (j : Json) : Array LeanDecl :=
  let kind := nodeKind j
  -- Comments are handled via comment/docComment fields on declarations.
  -- No separate Comment decls needed; each lowerer extracts its own comments.
  if kind == "VariableStatement" then lowerVarStatement j
    else if kind == "FunctionDeclaration" then lowerFuncDeclR reg j
    else if kind == "InterfaceDeclaration" then lowerInterfaceDecl j
    else if kind == "ClassDeclaration" then lowerClassDecl reg j
    else if kind == "TypeAliasDeclaration" then lowerTypeAliasDecl j
    else if kind == "EnumDeclaration" then lowerEnumDecl j
    else #[]

-- ─── Module lowering ────────────────────────────────────────────────────────────

/-- Check if any class has mutating methods (needs Monad import). -/
private def hasClassMutation (stmts : Array Json) : Bool :=
  stmts.any fun s =>
    if nodeKind s == "ClassDeclaration" then
      let members := fieldArr s "members"
      members.any fun m =>
        if isMethodDeclaration m || nodeKind m == "Constructor" then
          let bodyStmts := match fieldNode m "body" with
            | some b => fieldArr b "statements" | none => #[]
          bodyHasThisAssign bodyStmts
        else false
    else false

/-- Check if any function is async. -/
private def hasAsyncFunc (stmts : Array Json) : Bool :=
  stmts.any fun s =>
    if nodeKind s == "FunctionDeclaration" then
      let mods := fieldArr s "modifiers"
      mods.any fun m => nodeKind m == "AsyncKeyword"
    else false

/-- Check if file uses DurableObject patterns. -/
private def hasDurableObjectPattern (stmts : Array Json) : Bool :=
  let text := stmts.foldl (fun acc s => acc ++ toString s) ""
  textContains text "DurableObjectState" || textContains text "this.state.storage"

/-- Check if any function has variable reassignment (needs Monad import). -/
private partial def hasFuncVarReassign (stmts : Array Json) : Bool :=
  stmts.any fun s =>
    if nodeKind s == "FunctionDeclaration" then
      let bodyStmts := match fieldNode s "body" with
        | some b => fieldArr b "statements" | none => #[]
      bodyHasVarReassign bodyStmts
    else false

/-- Walk JSON AST for actual WebAPI usage: TypeReference nodes with
    Request/Response/URL/Headers/WebSocket, or fetch() calls/methods.
    Uses AST node kinds to avoid false positives from string literals
    like `['Request', 'Response', 'URL']` in lower.ts. -/
private partial def hasWebAPIUsage (stmts : Array Json) : Bool :=
  let webAPITypes := #["Request", "Response", "URL", "Headers", "WebSocket"]
  let getChildren (j : Json) : Array Json :=
    fieldArr j "statements" ++ fieldArr j "members" ++
    fieldArr j "parameters" ++ fieldArr j "declarations" ++
    fieldArr j "typeArguments" ++ fieldArr j "arguments" ++
    fieldArr j "types" ++ fieldArr j "elements" ++ fieldArr j "clauses" ++
    fieldArr j "heritageClauses" ++
    (#["type", "body", "expression", "declarationList",
       "initializer", "thenStatement", "elseStatement", "returnType",
       "typeName", "constraint", "default"].filterMap (fieldNode j ·))
  let rec go (j : Json) (fuel : Nat) : Bool :=
    if fuel == 0 then false else
    let kind := nodeKind j
    if kind == "TypeReference" then
      let tn := (fieldNode j "typeName").map nodeText |>.getD ""
      webAPITypes.contains tn
    else if kind == "CallExpression" then
      let callee := (fieldNode j "expression").map nodeText |>.getD ""
      callee == "fetch" || (getChildren j).any (go · (fuel - 1))
    else if kind == "MethodDeclaration" then
      let mname := (fieldNode j "name").map nodeText |>.getD ""
      mname == "fetch" || (getChildren j).any (go · (fuel - 1))
    else (getChildren j).any (go · (fuel - 1))
  stmts.any (go · 25)

/-- Scan JSON statements for import needs. -/
private def scanImports (stmts : Array Json) : Array String :=
  let needs := #["TSLean.Runtime.Basic", "TSLean.Runtime.Coercions"]
  let text := stmts.foldl (fun acc s => acc ++ toString s) ""
  -- Monad needed for async, class mutations, variable reassignment, or state patterns
  let needsMonad := textContains text "async" || textContains text "await" ||
    textContains text "Promise" || hasClassMutation stmts || hasAsyncFunc stmts ||
    hasFuncVarReassign stmts
  let needs := if needsMonad then needs.push "TSLean.Runtime.Monad" else needs
  -- WebAPI — walk AST for actual type refs and fetch calls (not text search)
  let needs := if hasWebAPIUsage stmts then needs.push "TSLean.Runtime.WebAPI" else needs
  -- HashMap
  let needs := if textContains text "Map" || textContains text "Set" then
    needs.push "TSLean.Stdlib.HashMap" else needs
  -- DurableObjects
  let hasDO := hasDurableObjectPattern stmts
  let needs := if hasDO then
    needs.push "TSLean.DurableObjects.Http"
    |>.push "TSLean.DurableObjects.Model"
    |>.push "TSLean.DurableObjects.State"
    |>.push "TSLean.DurableObjects.Storage"
  else needs
  -- Sort imports alphabetically (matches TS pipeline)
  needs.toList.mergeSort (· < ·) |>.toArray

/-- Determine open namespaces from imports. -/
private def resolveOpens (imports : Array String) : Array String :=
  let opens := #["TSLean"]
  let opens := if imports.any (textContains · "WebAPI") then opens.push "TSLean.WebAPI" else opens
  let opens := if imports.any (textContains · "HashMap") then opens.push "TSLean.Stdlib.HashMap" else opens
  let opens := if imports.any (textContains · "DurableObjects") then opens.push "TSLean.DO" else opens
  opens

/-- Collect discriminated union info from type alias declarations in the AST. -/
private def collectUnionRegistry (stmts : Array Json) : UnionRegistry :=
  stmts.foldl (fun reg s =>
    if nodeKind s == "TypeAliasDeclaration" then
      let name := (fieldNode s "name").map nodeText |>.getD ""
      match fieldNode s "type" with
      | some tn =>
        if nodeKind tn == "UnionType" then
          let types := fieldArr tn "types"
          let isDiscriminated := types.size > 0 && types.all fun t =>
            nodeKind t == "TypeLiteral" && hasDiscriminantField t
          if isDiscriminated then reg.push (extractUnionInfo name types) else reg
        else reg
      | none => reg
    else reg
  ) #[]

-- ─── Mutual block detection ─────────────────────────────────────────────────

/-- Collect names of type declarations (interfaces and discriminated union type aliases). -/
private def collectTypeNames (stmts : Array Json) : Array String :=
  stmts.filterMap fun s =>
    let kind := nodeKind s
    if kind == "InterfaceDeclaration" then
      (fieldNode s "name").map nodeText
    else if kind == "TypeAliasDeclaration" then
      match fieldNode s "type" with
      | some tn =>
        if nodeKind tn == "UnionType" then (fieldNode s "name").map nodeText
        else none
      | none => none
    else none

/-- Collect TypeReference names from all member types of a type declaration. -/
private partial def collectTypeRefs (s : Json) (typeNames : Array String) (selfName : String) : Array String :=
  let members := match nodeKind s with
    | "InterfaceDeclaration" => fieldArr s "members"
    | "TypeAliasDeclaration" =>
      match fieldNode s "type" with
      | some tn =>
        if nodeKind tn == "UnionType" then
          (fieldArr tn "types").foldl (fun acc t => acc ++ fieldArr t "members") #[]
        else #[]
      | none => #[]
    | _ => #[]
  let refs := members.foldl (fun acc m =>
    let rec scanTypeNode (j : Json) (refs : Array String) : Array String :=
      let kind := nodeKind j
      if kind == "TypeReference" then
        let name := (fieldNode j "typeName").map nodeText |>.getD ""
        let refs := if typeNames.contains name && name != selfName && !refs.contains name
          then refs.push name else refs
        -- Also scan type arguments
        (fieldArr j "typeArguments").foldl (fun r a => scanTypeNode a r) refs
      else if kind == "ArrayType" then
        match fieldNode j "elementType" with
        | some et => scanTypeNode et refs | none => refs
      else if kind == "UnionType" then
        (fieldArr j "types").foldl (fun r t => scanTypeNode t r) refs
      else refs
    match fieldNode m "type" with
    | some tn => scanTypeNode tn acc
    | none => acc
  ) #[]
  refs

/-- Find mutual group: types that transitively cross-reference each other. -/
private def findMutualGroup (start : String) (typeRefs : Array (String × Array String))
    : Array String :=
  -- Use LIFO (stack) ordering to match TS queue.pop() behavior
  let rec go (stack : Array String) (group : Array String) (fuel : Nat) : Array String :=
    match fuel with
    | 0 => group
    | fuel + 1 =>
      if stack.isEmpty then group
      else
        let name := stack.back!
        let stack := stack.pop
        if group.contains name then go stack group fuel
        else
          let group := group.push name
          let refs := (typeRefs.find? fun (n, _) => n == name).map (·.2) |>.getD #[]
          let stack := refs.foldl (fun s ref =>
            let backRefs := (typeRefs.find? fun (n, _) => n == ref).map (·.2) |>.getD #[]
            if group.any (fun g => backRefs.contains g) then s.push ref else s
          ) stack
          go stack group fuel
  let group := go #[start] #[] 100
  if group.size > 1 then group else #[]

/-- Detect mutual groups among type declarations. -/
private def detectMutualGroups (stmts : Array Json) : Array (Array String) :=
  let typeNames := collectTypeNames stmts
  let typeRefs := stmts.filterMap fun s =>
    let name := (fieldNode s "name").map nodeText |>.getD ""
    if typeNames.contains name then
      some (name, collectTypeRefs s typeNames name)
    else none
  let groups : Array (Array String) := #[]
  let assigned : Array String := #[]
  typeNames.foldl (fun (groups, assigned) name =>
    if assigned.contains name then (groups, assigned)
    else
      let group := findMutualGroup name typeRefs
      if group.size > 1 then
        (groups.push group, assigned ++ group)
      else (groups, assigned)
  ) (groups, assigned) |>.1

-- ─── Module lowering ────────────────────────────────────────────────────────

def lowerJsonModule (json : Json) : LeanFile :=
  let fileName := fieldStr json "fileName"
  let ns := fileToModuleName fileName
  let stmts := fieldArr json "statements"
  -- Collect discriminated union info for constructor pattern matching
  let reg := collectUnionRegistry stmts
  -- Detect mutual groups for cross-referencing types
  let mutualGroups := detectMutualGroups stmts
  let mutualNames := mutualGroups.foldl (fun acc g => acc ++ g) #[]
  let imports := scanImports stmts
  let decls := imports.map fun imp => LeanDecl.Import imp
  let decls := decls.push .Blank
  let decls := decls.push (.Open (resolveOpens imports))
  let decls := decls.push .Blank
  -- Lower statements, grouping mutual types
  let emittedMutuals : Array String := #[]
  let bodyDecls := stmts.foldl (fun (acc, emitted) s =>
    let name := (fieldNode s "name").map nodeText |>.getD ""
    if mutualNames.contains name && !emitted.contains name then
      -- Find this type's mutual group
      let group := (mutualGroups.find? fun g => g.contains name).getD #[]
      -- Lower all types in the group in mutual-detection order (BFS order)
      let mutualDecls := group.foldl (fun mutAcc gName =>
        let memberStmt := stmts.find? fun s2 =>
          ((fieldNode s2 "name").map nodeText |>.getD "") == gName
        match memberStmt with
        | some ms =>
          let ds := lowerStatementR reg ms
          -- Strip deriving and blank lines; merge leading comments into decl
          let ds := ds.filterMap fun d => match d with
            | .Structure n tp fs ext _ c => some (.Structure n tp fs ext #[] c)
            | .Inductive n tp ctors _ c => some (.Inductive n tp ctors #[] c)
            | .Blank => none
            | _ => some d
          -- Merge consecutive Comment decls into the following type decl's comment field
          let merged := ds.foldl (fun (acc, pendingComments) d =>
            match d with
            | .Comment text => (acc, pendingComments ++ [text])
            | .Structure n tp fs ext der existingComment =>
              let comment := if !pendingComments.isEmpty then
                some (String.intercalate "\n" pendingComments)
              else existingComment
              (acc.push (.Structure n tp fs ext der comment), [])
            | .Inductive n tp ctors der existingComment =>
              let comment := if !pendingComments.isEmpty then
                some (String.intercalate "\n" pendingComments)
              else existingComment
              (acc.push (.Inductive n tp ctors der comment), [])
            | _ => (acc.push d, pendingComments)
          ) (#[], ([] : List String))
          mutAcc ++ merged.1
        | none => mutAcc
      ) #[]
      let mutualDecl := LeanDecl.Mutual mutualDecls
      -- Generate standalone instances in group order (matches TS codegen)
      let instances := group.foldl (fun instAcc gName =>
        instAcc
          |>.push (.StandaloneInstance s!"instance : Inhabited {gName} := ⟨sorry⟩")
          |>.push (.StandaloneInstance s!"instance : BEq {gName} := ⟨fun _ _ => false⟩")
          |>.push (.StandaloneInstance s!"instance : Repr {gName} := ⟨fun _ _ => .text s!\"{gName}\"⟩")
      ) #[]
      let emitted := emitted ++ group
      (acc ++ #[mutualDecl, .Blank] ++ instances ++ #[.Blank], emitted)
    else if emitted.contains name then
      -- Already emitted as part of a mutual group
      (acc, emitted)
    else
      let ds := lowerStatementR reg s
      if ds.isEmpty then (acc, emitted) else (acc ++ ds ++ #[.Blank], emitted)
  ) (#[], emittedMutuals)
  let bodyDecls := bodyDecls.1
  let useNs := !ns.isEmpty && ns != "T" && ns != "Test"
  let decls := if useNs then decls.push (.Namespace ns bodyDecls) else decls ++ bodyDecls
  { banner := some "Auto-generated by ts-lean-transpiler"
    sourcePath := some fileName
    decls := decls }

end TSLean.V2.FromJSON
