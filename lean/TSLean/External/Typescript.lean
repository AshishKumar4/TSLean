-- TSLean.External.Typescript
-- Stubs for the TypeScript Compiler API.
-- Models ts.Node, ts.SyntaxKind, ts.TypeChecker, ts.Signature, etc. at the
-- level needed by the transpiled self-hosting code.  No real TS compiler is
-- invoked — these are structural placeholders for Lean type-checking.

namespace TSLean.External.Typescript

-- ─── ts.TypeFlags ──────────────────────────────────────────────────────────────
-- Bitflag enum for ts.TypeFlags.  In real TS these are powers of 2;
-- we model the commonly-checked flags as named constants.

namespace TypeFlags
  def Any            : Nat := 1
  def Unknown        : Nat := 2
  def String         : Nat := 4
  def Number         : Nat := 8
  def Boolean        : Nat := 16
  def Enum           : Nat := 32
  def BigInt         : Nat := 64
  def StringLiteral  : Nat := 128
  def NumberLiteral  : Nat := 256
  def BooleanLiteral : Nat := 512
  def Undefined      : Nat := 1024
  def Null           : Nat := 2048
  def Void           : Nat := 4096
  def Never          : Nat := 8192
  def TypeParameter  : Nat := 16384
  def Object         : Nat := 32768
  def Union          : Nat := 65536
  def Intersection   : Nat := 131072
  def Index          : Nat := 262144
  def Conditional    : Nat := 524288
end TypeFlags

-- ─── ts.ObjectFlags ────────────────────────────────────────────────────────────

namespace ObjectFlags
  def Class          : Nat := 1
  def Interface      : Nat := 2
  def Reference      : Nat := 4
  def Tuple          : Nat := 8
  def Anonymous      : Nat := 16
  def Mapped         : Nat := 32
end ObjectFlags

-- ─── ts.SymbolFlags ────────────────────────────────────────────────────────────

namespace SymbolFlags
  def None           : Nat := 0
  def FunctionScoped : Nat := 1
  def BlockScoped    : Nat := 2
  def Property       : Nat := 4
  def EnumMember     : Nat := 8
  def Function       : Nat := 16
  def Class          : Nat := 32
  def Interface      : Nat := 64
  def Method         : Nat := 128
  def Optional       : Nat := 16777216
end SymbolFlags

-- ─── ts.SyntaxKind ─────────────────────────────────────────────────────────────

inductive SyntaxKind where
  | Unknown | EndOfFileToken
  -- Literals and identifiers
  | NumericLiteral | BigIntLiteral | StringLiteral | RegularExpressionLiteral
  | NoSubstitutionTemplateLiteral | TemplateHead | TemplateMiddle | TemplateTail
  | Identifier
  -- Punctuation tokens
  | OpenBraceToken | CloseBraceToken | OpenParenToken | CloseParenToken
  | OpenBracketToken | CloseBracketToken
  | DotToken | DotDotDotToken | SemicolonToken | CommaToken
  | QuestionToken | QuestionDotToken | ExclamationToken
  | EqualsToken | EqualsEqualsToken | EqualsEqualsEqualsToken
  | ExclamationEqualsToken | ExclamationEqualsEqualsToken
  | PlusToken | MinusToken | AsteriskToken | SlashToken | PercentToken
  | PlusPlusToken | MinusMinusToken
  | LessThanToken | GreaterThanToken | LessThanEqualsToken | GreaterThanEqualsToken
  | AmpersandToken | BarToken | CaretToken | TildeToken
  | AmpersandAmpersandToken | BarBarToken
  | PlusEqualsToken | MinusEqualsToken | AsteriskEqualsToken | SlashEqualsToken
  | PercentEqualsToken
  | EqualsGreaterThanToken
  -- Keywords
  | BreakKeyword | CaseKeyword | CatchKeyword | ClassKeyword | ConstKeyword
  | ContinueKeyword | DefaultKeyword | DeleteKeyword | DoKeyword | ElseKeyword
  | ExportKeyword | ExtendsKeyword | FalseKeyword | FinallyKeyword | ForKeyword
  | FunctionKeyword | IfKeyword | ImportKeyword | InKeyword | InstanceOfKeyword
  | NewKeyword | NullKeyword | ReturnKeyword | SuperKeyword | SwitchKeyword
  | ThisKeyword | ThrowKeyword | TrueKeyword | TryKeyword | TypeOfKeyword
  | VarKeyword | VoidKeyword | WhileKeyword | WithKeyword | YieldKeyword
  | LetKeyword | AsyncKeyword | AwaitKeyword | AsKeyword
  | ImplementsKeyword | InterfaceKeyword | PrivateKeyword | ProtectedKeyword
  | PublicKeyword | StaticKeyword | AbstractKeyword | DeclareKeyword
  | ReadonlyKeyword | OverrideKeyword
  -- Type keywords
  | AnyKeyword | BooleanKeyword | NeverKeyword | NumberKeyword
  | StringKeyword | SymbolKeyword | UndefinedKeyword | UnknownKeyword | VoidKeyword2
  -- Declarations
  | TypeReference | PropertySignature | MethodSignature
  | InterfaceDeclaration | ClassDeclaration | FunctionDeclaration
  | VariableDeclaration | VariableDeclarationList | VariableStatement
  | ExpressionStatement | ReturnStatement | IfStatement
  | WhileStatement | DoStatement | ForStatement | ForInStatement | ForOfStatement
  | SwitchStatement | CaseClause | DefaultClause | CaseBlock
  | Block | SourceFile | ModuleDeclaration | ImportDeclaration | ExportDeclaration
  | TypeAliasDeclaration | EnumDeclaration | EnumMember
  | Parameter | PropertyDeclaration | MethodDeclaration | GetAccessor | SetAccessor
  | Constructor | ArrowFunction | FunctionExpression
  -- Expressions
  | CallExpression | NewExpression | TaggedTemplateExpression
  | PropertyAccessExpression | ElementAccessExpression
  | BinaryExpression | PrefixUnaryExpression | PostfixUnaryExpression
  | ConditionalExpression | TemplateExpression
  | ArrayLiteralExpression | ObjectLiteralExpression | SpreadElement
  | AsExpression | TypeAssertionExpression | NonNullExpression
  | ParenthesizedExpression | AwaitExpression | YieldExpression
  | DeleteExpression | VoidExpression | TypeOfExpression
  -- Statements
  | ThrowStatement | TryStatement | CatchClause | LabeledStatement
  -- Patterns
  | TypeParameter | HeritageClause | Decorator | ComputedPropertyName
  | ShorthandPropertyAssignment | SpreadAssignment
  | PropertyAssignment | BindingElement
  | ArrayBindingPattern | ObjectBindingPattern
  -- Module specifiers
  | ImportSpecifier | ExportSpecifier | NamedImports | NamedExports
  | ImportClause | ExportAssignment
  -- Misc
  | JsxElement | JsxSelfClosingElement | JsxOpeningElement
  | SatisfiesExpression
  -- Catch-all for codes we don't enumerate
  | Other (code : Nat)
  deriving Repr, BEq, Inhabited

-- ─── ts.Symbol ─────────────────────────────────────────────────────────────────

structure Symbol where
  name           : String
  flags          : Nat := 0
  declarations   : Array Node := #[]
  valueDeclaration : Option Node := none
  deriving Inhabited

-- ─── ts.Type ───────────────────────────────────────────────────────────────────

structure TSType where
  flags       : Nat := 0
  symbol      : Option Symbol := none
  objectFlags : Nat := 0
  aliasSymbol : Option Symbol := none
  deriving Inhabited

-- Union and intersection types
structure UnionType extends TSType where
  types : Array TSType := #[]
  deriving Inhabited

structure IntersectionType extends TSType where
  types : Array TSType := #[]
  deriving Inhabited

structure TypeReference extends TSType where
  target     : TSType := {}
  typeArguments : Array TSType := #[]
  deriving Inhabited

structure StringLiteralType extends TSType where
  value : String := ""
  deriving Inhabited

structure ConditionalType extends TSType where
  checkType : TSType := {}
  extendsType : TSType := {}
  trueType  : TSType := {}
  falseType : TSType := {}
  deriving Inhabited

-- ─── ts.Signature ──────────────────────────────────────────────────────────────

structure Signature where
  declaration  : Option Node := none
  typeParameters : Array TSType := #[]
  parameters   : Array Symbol := #[]
  returnType   : TSType := {}
  deriving Inhabited

-- ─── ts.Node ───────────────────────────────────────────────────────────────────

structure Node where
  kind           : SyntaxKind
  pos            : Nat
  end_           : Nat
  flags          : Nat := 0
  parent         : Option Node := none
  modifiers      : Array Node := #[]
  decorators     : Array Node := #[]
  text           : String := ""
  -- For named nodes (identifiers, declarations):
  name           : Option Node := none
  -- For expression/statement nodes:
  expression     : Option Node := none
  body           : Option Node := none
  statements     : Array Node := #[]
  -- For declaration nodes:
  typeParameters : Array Node := #[]
  parameters     : Array Node := #[]
  type_          : Option Node := none
  initializer    : Option Node := none
  members        : Array Node := #[]
  heritageClauses : Array Node := #[]
  -- For binary/unary expressions:
  left           : Option Node := none
  right          : Option Node := none
  operand        : Option Node := none
  operatorToken  : Option Node := none
  -- For control flow:
  thenStatement  : Option Node := none
  elseStatement  : Option Node := none
  condition      : Option Node := none
  incrementor    : Option Node := none
  caseBlock      : Option Node := none
  clauses        : Array Node := #[]
  block          : Option Node := none
  catchClause    : Option Node := none
  finallyBlock   : Option Node := none
  variableDeclaration : Option Node := none
  -- For call/new expressions:
  arguments      : Array Node := #[]
  typeArguments  : Array Node := #[]
  -- For property access:
  questionDotToken : Option Node := none
  -- For import/export:
  moduleSpecifier : Option Node := none
  importClause   : Option Node := none
  -- For template literals:
  head           : Option Node := none
  templateSpans  : Array Node := #[]
  -- For spread:
  dotDotDotToken : Option Node := none
  -- Children (for generic traversal):
  children       : Array Node := #[]
  deriving Inhabited

-- ─── ts.SourceFile ─────────────────────────────────────────────────────────────

structure SourceFile extends Node where
  fileName    : String
  sourceText  : String
  deriving Inhabited

-- ─── ts.TypeChecker ────────────────────────────────────────────────────────────

structure TypeChecker where
  private mk_ ::
  dummy : Unit := ()
  deriving Repr, Inhabited

-- TypeChecker methods (opaque stubs returning default values)
namespace TypeChecker
  def getTypeAtLocation     (_c : TypeChecker) (_n : Node)   : TSType   := {}
  def getTypeOfSymbol       (_c : TypeChecker) (_s : Symbol) : TSType   := {}
  def getSymbolAtLocation   (_c : TypeChecker) (_n : Node)   : Option Symbol := none
  def getSignaturesOfType   (_c : TypeChecker) (_t : TSType) : Array Signature := #[]
  def getReturnTypeOfSignature (_c : TypeChecker) (_s : Signature) : TSType := {}
  def getTypeArguments      (_c : TypeChecker) (_t : TSType) : Array TSType := #[]
  def isArrayType           (_c : TypeChecker) (_t : TSType) : Bool := false
  def isTupleType           (_c : TypeChecker) (_t : TSType) : Bool := false
  def typeToString          (_c : TypeChecker) (_t : TSType) : String := "<type>"
  def getAnyType            (_c : TypeChecker)               : TSType := { flags := TypeFlags.Any }
  def getStringType         (_c : TypeChecker)               : TSType := { flags := TypeFlags.String }
  def getNumberType         (_c : TypeChecker)               : TSType := { flags := TypeFlags.Number }
  def getBooleanType        (_c : TypeChecker)               : TSType := { flags := TypeFlags.Boolean }
  def getTypeOfSymbolAtLocation (_c : TypeChecker) (_s : Symbol) (_n : Node) : TSType := {}
end TypeChecker

-- ─── ts.CompilerOptions ────────────────────────────────────────────────────────

structure CompilerOptions where
  target           : Option Nat := none
  module           : Option Nat := none
  moduleResolution : Option Nat := none
  strict           : Bool := true
  skipLibCheck     : Bool := true
  noResolve        : Bool := false
  lib              : Array String := #[]
  deriving Repr, Inhabited

-- ─── ts.CompilerHost ───────────────────────────────────────────────────────────
-- The TS compiler host abstracts file system access.  In our Lean model,
-- actual file I/O is opaque, so we provide the shape needed by the
-- transpiled parser code (which creates hosts via `makeAmbientHost`).

structure CompilerHost where
  /-- Return the current working directory. -/
  getCurrentDirectory : IO String := pure "."
  /-- The newline sequence for the platform. -/
  getNewLine : String := "\n"
  /-- Check if a file exists on disk. -/
  fileExists : String → Bool := fun _ => false
  /-- Read a file's contents. Returns empty string if not found. -/
  readFile : String → Option String := fun _ => none
  deriving Inhabited

-- ─── ts.Program ────────────────────────────────────────────────────────────────

structure Program where
  sourceFiles : Array SourceFile := #[]
  options     : CompilerOptions := {}
  deriving Inhabited

-- ─── API functions (opaque stubs) ──────────────────────────────────────────────

opaque createSourceFile (name : String) (text : String) (version : Nat) : SourceFile
opaque createProgram (rootNames : Array String) (options : CompilerOptions) : Program
opaque createCompilerHost (options : CompilerOptions) : CompilerHost
opaque getPreEmitDiagnostics (program : Program) : Array String

-- ─── Node kind predicates ──────────────────────────────────────────────────────

def isIdentifier          (n : Node) : Bool := n.kind == .Identifier
def isStringLiteral       (n : Node) : Bool := n.kind == .StringLiteral
def isNumericLiteral      (n : Node) : Bool := n.kind == .NumericLiteral
def isCallExpression      (n : Node) : Bool := n.kind == .CallExpression
def isPropertyAccessExpression (n : Node) : Bool := n.kind == .PropertyAccessExpression
def isElementAccessExpression  (n : Node) : Bool := n.kind == .ElementAccessExpression
def isBinaryExpression    (n : Node) : Bool := n.kind == .BinaryExpression
def isArrowFunction       (n : Node) : Bool := n.kind == .ArrowFunction
def isFunctionDeclaration (n : Node) : Bool := n.kind == .FunctionDeclaration
def isFunctionExpression  (n : Node) : Bool := n.kind == .FunctionExpression
def isMethodDeclaration   (n : Node) : Bool := n.kind == .MethodDeclaration
def isClassDeclaration    (n : Node) : Bool := n.kind == .ClassDeclaration
def isInterfaceDeclaration (n : Node) : Bool := n.kind == .InterfaceDeclaration
def isVariableStatement   (n : Node) : Bool := n.kind == .VariableStatement
def isVariableDeclaration (n : Node) : Bool := n.kind == .VariableDeclaration
def isExpressionStatement (n : Node) : Bool := n.kind == .ExpressionStatement
def isReturnStatement     (n : Node) : Bool := n.kind == .ReturnStatement
def isIfStatement         (n : Node) : Bool := n.kind == .IfStatement
def isForStatement        (n : Node) : Bool := n.kind == .ForStatement
def isForOfStatement      (n : Node) : Bool := n.kind == .ForOfStatement
def isForInStatement      (n : Node) : Bool := n.kind == .ForInStatement
def isWhileStatement      (n : Node) : Bool := n.kind == .WhileStatement
def isSwitchStatement     (n : Node) : Bool := n.kind == .SwitchStatement
def isBlock               (n : Node) : Bool := n.kind == .Block
def isImportDeclaration   (n : Node) : Bool := n.kind == .ImportDeclaration
def isExportDeclaration   (n : Node) : Bool := n.kind == .ExportDeclaration
def isTypeAliasDeclaration (n : Node) : Bool := n.kind == .TypeAliasDeclaration
def isEnumDeclaration     (n : Node) : Bool := n.kind == .EnumDeclaration
def isThrowStatement      (n : Node) : Bool := n.kind == .ThrowStatement
def isTryStatement        (n : Node) : Bool := n.kind == .TryStatement
def isAwaitExpression     (n : Node) : Bool := n.kind == .AwaitExpression
def isPropertySignature   (n : Node) : Bool := n.kind == .PropertySignature
def isPropertyDeclaration (n : Node) : Bool := n.kind == .PropertyDeclaration
def isParameter           (n : Node) : Bool := n.kind == .Parameter
def isSpreadElement       (n : Node) : Bool := n.kind == .SpreadElement
def isTemplateExpression  (n : Node) : Bool := n.kind == .TemplateExpression
def isObjectLiteralExpression (n : Node) : Bool := n.kind == .ObjectLiteralExpression
def isArrayLiteralExpression  (n : Node) : Bool := n.kind == .ArrayLiteralExpression
def isConditionalExpression   (n : Node) : Bool := n.kind == .ConditionalExpression
def isPrefixUnaryExpression   (n : Node) : Bool := n.kind == .PrefixUnaryExpression
def isPostfixUnaryExpression  (n : Node) : Bool := n.kind == .PostfixUnaryExpression
def isConstructorDeclaration  (n : Node) : Bool := n.kind == .Constructor
def isGetAccessor             (n : Node) : Bool := n.kind == .GetAccessor
def isSetAccessor             (n : Node) : Bool := n.kind == .SetAccessor
def isLabeledStatement        (n : Node) : Bool := n.kind == .LabeledStatement

-- ─── Traversal ─────────────────────────────────────────────────────────────────

def Node.getText (n : Node) : String := n.text

def Node.getChildren (n : Node) : Array Node := n.children

/-- Visit all children of a node (shallow, one level). -/
def forEachChild (node : Node) (f : Node → Unit) : Unit :=
  node.children.foldl (fun _ c => f c) ()

-- ─── Module / ScriptTarget / ModuleKind constants ──────────────────────────────

namespace ScriptTarget
  def ES5    : Nat := 1
  def ES2015 : Nat := 2
  def ES2022 : Nat := 9
  def Latest : Nat := 99
end ScriptTarget

namespace ModuleKind
  def CommonJS  : Nat := 1
  def AMD       : Nat := 2
  def ESNext    : Nat := 99
  def NodeNext  : Nat := 199
end ModuleKind

namespace ModuleResolutionKind
  def Classic   : Nat := 1
  def NodeJs    : Nat := 2
  def NodeNext  : Nat := 99
end ModuleResolutionKind

-- ─── Theorems ──────────────────────────────────────────────────────────────────

-- SyntaxKind uses derived BEq (not LawfulBEq), so beq_iff_eq doesn't apply.
axiom isIdentifier_kind (n : Node) : isIdentifier n = true ↔ n.kind = .Identifier
axiom isBlock_kind (n : Node) : isBlock n = true ↔ n.kind = .Block

end TSLean.External.Typescript
