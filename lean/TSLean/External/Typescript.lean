-- TSLean.External.Typescript
-- Stubs for the TypeScript Compiler API types.
-- These model ts.Node, ts.SyntaxKind, ts.SourceFile, etc. at the level
-- needed by the transpiled self-hosting code. No real TS compiler is
-- invoked — these are structural placeholders for type-checking.

namespace TSLean.External.Typescript

-- ts.SyntaxKind: enum of all TypeScript AST node kinds
inductive SyntaxKind where
  | Unknown | EndOfFileToken | NumericLiteral | StringLiteral
  | Identifier | TypeReference | PropertySignature | MethodSignature
  | InterfaceDeclaration | ClassDeclaration | FunctionDeclaration
  | VariableDeclaration | VariableStatement | ExpressionStatement
  | ReturnStatement | IfStatement | WhileStatement | ForStatement
  | ForOfStatement | SwitchStatement | CaseClause | DefaultClause
  | Block | SourceFile | ModuleDeclaration | ImportDeclaration
  | ExportDeclaration | TypeAliasDeclaration | EnumDeclaration
  | EnumMember | Parameter | PropertyDeclaration | MethodDeclaration
  | Constructor | ArrowFunction | CallExpression | NewExpression
  | PropertyAccessExpression | ElementAccessExpression
  | BinaryExpression | PrefixUnaryExpression | PostfixUnaryExpression
  | ConditionalExpression | TemplateExpression | TaggedTemplateExpression
  | ArrayLiteralExpression | ObjectLiteralExpression | SpreadElement
  | AsExpression | TypeAssertionExpression | ParenthesizedExpression
  | AwaitExpression | YieldExpression | DeleteExpression
  | ThrowStatement | TryStatement | CatchClause
  | TypeParameter | HeritageClause | Decorator
  | ComputedPropertyName | ShorthandPropertyAssignment
  | BindingElement | ArrayBindingPattern | ObjectBindingPattern
  | Other (code : Nat)
  deriving Repr, BEq, Inhabited

-- ts.Node: the base AST node
structure Node where
  kind      : SyntaxKind
  pos       : Nat
  end_      : Nat
  parent    : Option Node := none
  children  : Array Node := #[]
  text      : String := ""
  deriving Repr, Inhabited

-- ts.SourceFile: a parsed TypeScript source file
structure SourceFile where
  fileName  : String
  text      : String
  statements : Array Node
  deriving Repr, Inhabited

-- ts.TypeChecker: the type checker interface (opaque)
structure TypeChecker where
  dummy : Unit := ()
  deriving Repr, Inhabited

-- ts.Symbol: a named symbol in the type system
structure Symbol where
  name      : String
  flags     : Nat := 0
  deriving Repr, BEq, Inhabited

-- ts.Type: a TypeScript type (simplified)
structure TSType where
  flags     : Nat := 0
  symbol    : Option Symbol := none
  deriving Repr, Inhabited

-- ts.CompilerHost: file system abstraction for the compiler
structure CompilerHost where
  getSourceFile : String → Nat → (String → Unit) → Bool → SourceFile
  fileExists    : String → Bool
  readFile      : String → String
  deriving Inhabited

-- ts.CompilerOptions
structure CompilerOptions where
  target    : Option Nat := none
  module    : Option Nat := none
  strict    : Bool := true
  deriving Repr, Inhabited

-- ts.Program: a compiled program
structure Program where
  sourceFiles   : Array SourceFile
  options       : CompilerOptions
  deriving Inhabited

-- API functions (opaque stubs)
opaque createSourceFile (name : String) (text : String) (version : Nat)
    (setParent : Bool := false) : SourceFile
opaque createProgram (rootNames : Array String) (options : CompilerOptions) : Program
opaque getPreEmitDiagnostics (program : Program) : Array String
opaque forEachChild (node : Node) (f : Node → Unit) : Unit

-- Convenience
def isIdentifier (node : Node) : Bool := node.kind == .Identifier
def isStringLiteral (node : Node) : Bool := node.kind == .StringLiteral
def isCallExpression (node : Node) : Bool := node.kind == .CallExpression

end TSLean.External.Typescript
