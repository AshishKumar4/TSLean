-- TSLean.JsonAST
-- Read a JSON-serialized TypeScript AST (produced by tsc-to-json.ts).
-- Provides typed accessors for JSON node fields and type resolution.

import Lean.Data.Json

namespace TSLean.JsonAST

open Lean

-- ─── JSON field accessors ───────────────────────────────────────────────────────

/-- Get a field from a JSON object by key. -/
def getField (j : Json) (key : String) : Option Json :=
  match j with
  | .obj m => m.get? key
  | _ => none

/-- Get a string from a JSON value. -/
def getStr (j : Json) : Option String :=
  match j with
  | .str s => some s
  | _ => none

/-- Get a number as Float from a JSON value. -/
def getNum (j : Json) : Option Float :=
  match j with
  | .num n => some n.toFloat
  | _ => none

/-- Get a number as Nat from a JSON value. -/
def getNat (j : Json) : Nat :=
  match j with
  | .num n => n.toFloat.toUInt64.toNat
  | _ => 0

/-- Get a boolean from a JSON value. -/
def getBool (j : Json) : Bool :=
  match j with
  | .bool b => b
  | _ => false

/-- Get an array from a JSON value. -/
def getArr (j : Json) : Array Json :=
  match j with
  | .arr a => a
  | _ => #[]

/-- Get a string field from a JSON object. -/
def fieldStr (j : Json) (key : String) : String :=
  (getField j key |>.bind getStr).getD ""

/-- Get a Nat field from a JSON object. -/
def fieldNat (j : Json) (key : String) : Nat :=
  (getField j key).map getNat |>.getD 0

/-- Get a boolean field from a JSON object. -/
def fieldBool (j : Json) (key : String) : Bool :=
  (getField j key).map getBool |>.getD false

/-- Get an array field from a JSON object. -/
def fieldArr (j : Json) (key : String) : Array Json :=
  (getField j key).map getArr |>.getD #[]

/-- Get an optional sub-node from a JSON object. -/
def fieldNode (j : Json) (key : String) : Option Json :=
  getField j key

-- ─── Node kind access ───────────────────────────────────────────────────────────

/-- Get the kind string of a JSON AST node. -/
def nodeKind (j : Json) : String := fieldStr j "kind"

/-- Get the text content of a JSON AST node (for identifiers/literals). -/
def nodeText (j : Json) : String := fieldStr j "text"

/-- Get the flags of a JSON AST node. -/
def nodeFlags (j : Json) : Nat := fieldNat j "flags"

-- ─── Kind predicates ────────────────────────────────────────────────────────────

def isVariableStatement (j : Json) : Bool := nodeKind j == "VariableStatement"
def isFunctionDeclaration (j : Json) : Bool := nodeKind j == "FunctionDeclaration"
def isClassDeclaration (j : Json) : Bool := nodeKind j == "ClassDeclaration"
def isInterfaceDeclaration (j : Json) : Bool := nodeKind j == "InterfaceDeclaration"
def isTypeAliasDeclaration (j : Json) : Bool := nodeKind j == "TypeAliasDeclaration"
def isEnumDeclaration (j : Json) : Bool := nodeKind j == "EnumDeclaration"
def isModuleDeclaration (j : Json) : Bool := nodeKind j == "ModuleDeclaration"
def isImportDeclaration (j : Json) : Bool := nodeKind j == "ImportDeclaration"
def isExportDeclaration (j : Json) : Bool := nodeKind j == "ExportDeclaration"
def isExportAssignment (j : Json) : Bool := nodeKind j == "ExportAssignment"
def isExpressionStatement (j : Json) : Bool := nodeKind j == "ExpressionStatement"
def isReturnStatement (j : Json) : Bool := nodeKind j == "ReturnStatement"
def isIfStatement (j : Json) : Bool := nodeKind j == "IfStatement"
def isBlock (j : Json) : Bool := nodeKind j == "Block"
def isIdentifier (j : Json) : Bool := nodeKind j == "Identifier"
def isNumericLiteral (j : Json) : Bool := nodeKind j == "NumericLiteral"
def isStringLiteral (j : Json) : Bool := nodeKind j == "StringLiteral"
def isPropertySignature (j : Json) : Bool := nodeKind j == "PropertySignature"
def isPropertyDeclaration (j : Json) : Bool := nodeKind j == "PropertyDeclaration"
def isPropertyAssignment (j : Json) : Bool := nodeKind j == "PropertyAssignment"
def isMethodDeclaration (j : Json) : Bool := nodeKind j == "MethodDeclaration"
def isConstructorDeclaration (j : Json) : Bool := nodeKind j == "Constructor"
def isParameter (j : Json) : Bool := nodeKind j == "Parameter"
def isArrowFunction (j : Json) : Bool := nodeKind j == "ArrowFunction"
def isFunctionExpression (j : Json) : Bool := nodeKind j == "FunctionExpression"
def isBinaryExpression (j : Json) : Bool := nodeKind j == "BinaryExpression"
def isCallExpression (j : Json) : Bool := nodeKind j == "CallExpression"
def isPropertyAccessExpression (j : Json) : Bool := nodeKind j == "PropertyAccessExpression"
def isObjectLiteralExpression (j : Json) : Bool := nodeKind j == "ObjectLiteralExpression"
def isArrayLiteralExpression (j : Json) : Bool := nodeKind j == "ArrayLiteralExpression"
def isConditionalExpression (j : Json) : Bool := nodeKind j == "ConditionalExpression"
def isTemplateExpression (j : Json) : Bool := nodeKind j == "TemplateExpression"
def isNoSubstitutionTemplate (j : Json) : Bool := nodeKind j == "NoSubstitutionTemplateLiteral"
def isAwaitExpression (j : Json) : Bool := nodeKind j == "AwaitExpression"
def isSpreadElement (j : Json) : Bool := nodeKind j == "SpreadElement"
def isForOfStatement (j : Json) : Bool := nodeKind j == "ForOfStatement"
def isForStatement (j : Json) : Bool := nodeKind j == "ForStatement"
def isForInStatement (j : Json) : Bool := nodeKind j == "ForInStatement"
def isWhileStatement (j : Json) : Bool := nodeKind j == "WhileStatement"
def isThrowStatement (j : Json) : Bool := nodeKind j == "ThrowStatement"
def isTryStatement (j : Json) : Bool := nodeKind j == "TryStatement"
def isSwitchStatement (j : Json) : Bool := nodeKind j == "SwitchStatement"
def isShorthandPropertyAssignment (j : Json) : Bool := nodeKind j == "ShorthandPropertyAssignment"
def isGetAccessor (j : Json) : Bool := nodeKind j == "GetAccessor"
def isSetAccessor (j : Json) : Bool := nodeKind j == "SetAccessor"
def isNewExpression (j : Json) : Bool := nodeKind j == "NewExpression"
def isPrefixUnaryExpression (j : Json) : Bool := nodeKind j == "PrefixUnaryExpression"
def isPostfixUnaryExpression (j : Json) : Bool := nodeKind j == "PostfixUnaryExpression"
def isObjectBindingPattern (j : Json) : Bool := nodeKind j == "ObjectBindingPattern"
def isArrayBindingPattern (j : Json) : Bool := nodeKind j == "ArrayBindingPattern"

-- ─── Type resolution ────────────────────────────────────────────────────────────

-- TypeFlags constants (matching TS compiler)
def TF_Any            : Nat := 1
def TF_Unknown        : Nat := 2
def TF_String         : Nat := 4
def TF_Number         : Nat := 8
def TF_Boolean        : Nat := 16
def TF_Enum           : Nat := 32
def TF_BigInt         : Nat := 64
def TF_StringLiteral  : Nat := 128
def TF_NumberLiteral  : Nat := 256
def TF_BooleanLiteral : Nat := 512
def TF_Undefined      : Nat := 1024
def TF_Null           : Nat := 2048
def TF_Void           : Nat := 4096
def TF_Never          : Nat := 8192
def TF_TypeParameter  : Nat := 16384
def TF_Object         : Nat := 32768
def TF_Union          : Nat := 65536
def TF_Intersection   : Nat := 131072

-- NodeFlags.Const (for variable declarations)
def NF_Const : Nat := 2

/-- Get the resolved type from a JSON node. -/
def resolvedType (j : Json) : Option Json := getField j "resolvedType"

/-- Get the type flags from a resolved type JSON. -/
def typeFlags (j : Json) : Nat := fieldNat j "flags"

/-- Get the type name from a resolved type JSON. -/
def typeName (j : Json) : String := fieldStr j "name"

/-- Get the symbol name from a resolved type JSON. -/
def typeSymbol (j : Json) : String := fieldStr j "symbol"

-- ─── File reading ───────────────────────────────────────────────────────────────

/-- Parse a JSON AST file content into a structured Json value. -/
def parseJsonContent (content : String) : IO Json := do
  match Json.parse content with
  | .ok json => pure json
  | .error e => throw (IO.userError s!"JSON parse error: {e}")

/-- Read and parse a JSON AST file. -/
def readJsonFile (path : String) : IO Json := do
  let content ← IO.FS.readFile ⟨path⟩
  parseJsonContent content

end TSLean.JsonAST
