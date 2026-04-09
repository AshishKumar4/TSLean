-- TSLean.Generated.SelfHost.Prelude
-- Forward declarations for ALL cross-file identifiers used by raw transpiler output.
-- 94 identifiers covering ts.TypeFlags, ts.SyntaxKind, parser/codegen/effects/rewrite
-- functions, and JS built-in type stubs.
-- Does NOT import IR_Types.lean to avoid cycles.

import TSLean.External.Typescript
import TSLean.Runtime.Basic
import TSLean.Runtime.Coercions
import TSLean.Runtime.Monad
import TSLean.Stdlib.HashMap

open TSLean TSLean.External.Typescript TSLean.Stdlib.HashMap

-- Declarations are in a dedicated namespace. Raw files should add:
--   open TSLean.Generated.SelfHost.Prelude
-- The transpiler codegen injects this open statement.
namespace TSLean.Generated.SelfHost.Prelude

-- ─── JS built-in type aliases ───────────────────────────────────────────────────

abbrev Boolean := Bool

-- ─── ts.TypeFlags.* ─────────────────────────────────────────────────────────────
-- The raw transpiler output references these as `ts.TypeFlags.String` etc.

namespace ts

namespace TypeFlags
  def Any            : Nat := 1
  def Unknown        : Nat := 2
  def String         : Nat := 4
  def Number         : Nat := 8
  def Boolean        : Nat := 16
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
  def Index          : Nat := 262144
  def Conditional    : Nat := 524288
end TypeFlags

namespace ObjectFlags
  def Reference : Nat := 4
end ObjectFlags

namespace SyntaxKind
  def EqualsToken          : TSLean.External.Typescript.SyntaxKind := .EqualsToken
  def PlusEqualsToken      : TSLean.External.Typescript.SyntaxKind := .PlusEqualsToken
  def MinusEqualsToken     : TSLean.External.Typescript.SyntaxKind := .MinusEqualsToken
  def AsteriskEqualsToken  : TSLean.External.Typescript.SyntaxKind := .AsteriskEqualsToken
  def SlashEqualsToken     : TSLean.External.Typescript.SyntaxKind := .SlashEqualsToken
  def PercentEqualsToken   : TSLean.External.Typescript.SyntaxKind := .PercentEqualsToken
  def PlusPlusToken        : TSLean.External.Typescript.SyntaxKind := .PlusPlusToken
  def MinusMinusToken      : TSLean.External.Typescript.SyntaxKind := .MinusMinusToken
end SyntaxKind

end ts

-- ─── TS compiler types used by raw output ───────────────────────────────────────

-- These alias into TSLean.External.Typescript types
abbrev TypeFlags := Nat
abbrev ConditionalType := TSType
abbrev Signature := TSLean.External.Typescript.Signature
abbrev Symbol := TSLean.External.Typescript.Symbol

-- ─── Structure stubs for types referenced by verification/codegen ───────────────

structure ProofObligation where
  kind     : String := ""
  funcName : String := ""
  detail   : String := ""
  deriving Repr, BEq, Inhabited

-- ─── IR type stubs (real types in ir_types.lean) ────────────────────────────────

abbrev IRType'   := Unit
abbrev IRExpr'   := Unit
abbrev IRDecl'   := Unit
abbrev IRModule' := Unit
abbrev Effect'   := Unit

-- ─── IR type constructor aliases ────────────────────────────────────────────────

def TyNat    : String := "Nat"
def TyInt    : String := "Int"
def TyFloat  : String := "Float"
def TyString : String := "String"
def TyBool   : String := "Bool"
def TyUnit   : String := "Unit"
def TyNever  : String := "Never"
def TyRef  (name : String)           : String := name
def TyArray(elem : String)           : String := s!"Array {elem}"
def TyOption(inner : String)         : String := s!"Option {inner}"
def TyMap  (k v : String)            : String := s!"AssocMap {k} {v}"
def TySet  (elem : String)           : String := s!"AssocSet {elem}"
def TyFn   (params : Array String) (ret : String) (_ : String := "Pure") : String :=
  s!"{" → ".intercalate params.toList} → {ret}"
def TyTuple(elems : Array String)    : String := s!"({" × ".intercalate elems.toList})"
def TyPromise(inner : String)        : String := s!"IO {inner}"
def TyVar  (name : String)           : String := name

-- ─── Effect constants ───────────────────────────────────────────────────────────

def Pure  : String := "Pure"
def Async : String := "Async"
def IO_   : String := "IO"

-- ─── SyntaxKind aliases ─────────────────────────────────────────────────────────

def VariableDeclaration  : SyntaxKind := .VariableDeclaration
def VariableStatement    : SyntaxKind := .VariableStatement
def FunctionDeclaration  : SyntaxKind := .FunctionDeclaration
def ClassDeclaration     : SyntaxKind := .ClassDeclaration
def InterfaceDeclaration : SyntaxKind := .InterfaceDeclaration
def TypeAliasDeclaration : SyntaxKind := .TypeAliasDeclaration
def EnumDeclaration      : SyntaxKind := .EnumDeclaration
def ModuleDeclaration    : SyntaxKind := .ModuleDeclaration
def ExportDeclaration    : SyntaxKind := .ExportDeclaration
def ImportDeclaration    : SyntaxKind := .ImportDeclaration
def ReturnStatement      : SyntaxKind := .ReturnStatement
def IfStatement          : SyntaxKind := .IfStatement
def SwitchStatement      : SyntaxKind := .SwitchStatement
def ForOfStatement       : SyntaxKind := .ForOfStatement
def ForStatement         : SyntaxKind := .ForStatement
def WhileStatement       : SyntaxKind := .WhileStatement
def TryStatement         : SyntaxKind := .TryStatement
def ThrowStatement       : SyntaxKind := .ThrowStatement
def ExpressionStatement  : SyntaxKind := .ExpressionStatement
def Block                : SyntaxKind := .Block
def VariableDeclarationKind := SyntaxKind  -- for Node.kind comparisons

-- ─── Parser functions ───────────────────────────────────────────────────────────

def parseFileSync     (_ : String)          : IRModule'  := default
def parseExpr         (_ _ : TSAny)         : TSAny      := default
def parseBlock        (_ _ _ : TSAny)       : TSAny      := default
def parseParams       (_ _ : TSAny)         : Array TSAny := #[]
def parseFnDecl       (_ _ : TSAny)         : TSAny      := default
def parseClassDecl    (_ _ : TSAny)         : TSAny      := default
def parseInterface    (_ _ : TSAny)         : TSAny      := default
def parseTypeAlias    (_ _ : TSAny)         : TSAny      := default
def parseEnum         (_ _ : TSAny)         : TSAny      := default
def parseVarStmt      (_ _ : TSAny)         : Array TSAny := #[]
def parseNamespace    (_ _ : TSAny)         : TSAny      := default
def parseExportDecl   (_ _ : TSAny)         : Option (Array TSAny) := none
def parseExportAssignment (_ _ : TSAny)     : Option (Array TSAny) := none
def parseArgs         (_ : Array String)    : TSAny      := default

-- ─── Typemap functions ──────────────────────────────────────────────────────────

def mapType           (_ _ : TSAny) (_ : Nat := 0) : TSAny := default
def mapUnion          (_ _ : TSAny) (_ : Nat)       : TSAny := default
def mapIntersection   (_ _ : TSAny) (_ : Nat)       : TSAny := default
def mapObject         (_ _ : TSAny) (_ : Nat)       : TSAny := default
def mapTypeRef        (_ _ : TSAny) (_ : Nat)       : TSAny := default
def irTypeToLean'     (_ : TSAny) (_ : Bool := false) : String := ""
def typeStr           (_ : TSAny)                    : String := ""
def getAliasName      (_ : TSAny)                    : Option String := none
def extractTypeParams (_ : TSAny)                    : Array String := #[]
def detectDiscriminatedUnion (_ : Array String)      : Option String := none
def extractStructFields (_ _ : TSAny)                : Array TSAny := #[]

-- ─── Effects functions ──────────────────────────────────────────────────────────

def inferNodeEffect       (_ _ : TSAny)     : TSAny := default
def monadString'          (_ : TSAny) (_ : String := "σ") : String := ""
def doMonadType           (_ : String)      : String := ""
def joinEffects'          (_ _ : TSAny)     : TSAny := default
def effectSubsumes'       (_ _ : TSAny)     : Bool  := false
def combineEffects'       (_ : Array TSAny) : TSAny := default
def getFunctionBody       (_ : TSAny)       : Option TSAny := none
def bodyContainsAwait     (_ : TSAny)       : Bool  := false
def bodyContainsThrow     (_ : TSAny)       : Bool  := false
def bodyContainsMutation  (_ : TSAny)       : Bool  := false
def bodyContainsIO        (_ : TSAny)       : Bool  := false
def isAssignOp            (_ : TSAny)       : Bool  := false
def isIncrDecr            (_ : TSAny)       : Bool  := false
def isNestedFnScope       (_ : TSAny)       : Bool  := false
def leanTypeName          (_ : TSAny)       : String := ""

-- ─── Rewrite functions ──────────────────────────────────────────────────────────

def rewriteModule'    (_ : TSAny)           : TSAny := default
def detectDiscriminant (_ : TSAny)          : Option TSAny := none
def rewriteDiscCase   (_ _ _ : TSAny)       : TSAny := default
def substituteFieldAccesses (_ _ _ : TSAny) : TSAny := default
def collectStructInfo (_ : TSAny)           : TSAny := default

-- ─── Codegen functions ──────────────────────────────────────────────────────────

def generateLean'     (_ : TSAny)           : String := ""
def sanitize'         (_ : String)          : String := ""
def sanitize          (_ : String)          : String := ""
def genPattern        (_ : TSAny)           : String := ""
def genExpr           (_ : TSAny) (_ : Nat := 0) : String := ""
def genPat            (_ : TSAny)           : String := ""
def needsParens       (_ : TSAny)           : Bool  := false
def emit              (_ : String)          : TSAny := default
def output            : String              := ""
def emitFunc          (_ : TSAny)           : TSAny := default
def emitStruct        (_ : TSAny)           : TSAny := default
def emitInductive     (_ : TSAny)           : TSAny := default
def emitTypeAlias     (_ : TSAny)           : TSAny := default
def emitNamespace     (_ : TSAny)           : TSAny := default
def emitSection       (_ : TSAny)           : TSAny := default
def emitInstance      (_ : TSAny)           : TSAny := default
def emitClass         (_ : TSAny)           : TSAny := default
def emitTheorem       (_ : TSAny)           : TSAny := default
def emitVarDecl       (_ : TSAny)           : TSAny := default
def emitComment       (_ : String)          : TSAny := default
def fmtExplicitTPs    (_ : Array String)    : String := ""
def trySInterp        (_ : TSAny)           : Option String := none
def flattenConcat     (_ : TSAny)           : Array TSAny := #[]

-- ─── Stdlib functions ───────────────────────────────────────────────────────────

def translateBinOp'   (_ _ : TSAny)         : String := ""
def lookupGlobal'     (_ : String)          : Option String := none
def lookupMethod'     (_ _ : String)        : Option String := none

-- ─── Verification functions ─────────────────────────────────────────────────────

def collectExpr'      (_ : TSAny) (_ : String) : Array String := #[]
def collectExpr       (_ : TSAny) (_ : String) : Array TSAny := #[]
def generateVerification' (_ : TSAny)       : String := ""

-- ─── DO model functions ─────────────────────────────────────────────────────────

def hasDOPattern      (_ : String)          : Bool  := false
def CF_AMBIENT        : String              := ""
def makeAmbientHost   (_ : CompilerHost) (_ : AssocMap String String) : CompilerHost := default
def DO_LEAN_IMPORTS   : List String         := []

-- ─── Project / CLI functions ────────────────────────────────────────────────────

def transpileProject' (_ _ : String)        : IO Unit := pure ()
def toLeanPath'       (_ _ _ : String)      : String := ""
def verify            (_ : TSAny)           : TSAny := default

-- ─── Identifiers used by codegen_index ───────────────────────────────────────────

/-- Recursive AST checker (used in bodyContainsVarRef). -/
def check             (_ : TSAny)           : Bool := false

-- ─── Other identifiers from raw output ──────────────────────────────────────────

def cap               (s : String)          : String :=
  if s.isEmpty then s else String.mk (s.toList.head!.toUpper :: s.toList.tail!)
def relToLean         (_ : String)          : String := ""
def jsdocComment      (_ _ : TSAny)         : Option String := none
def go                (_ : TSAny)           : TSAny := default
def cls               : TSAny              := default
def ns                : TSAny              := default
def state             : TSAny              := default
def __object          : TSAny              := default

end TSLean.Generated.SelfHost.Prelude

-- Re-export into the TSLean namespace so `open TSLean` picks up these stubs.
-- Only the identifiers that don't conflict with real implementations.
namespace TSLean
  export TSLean.Generated.SelfHost.Prelude (
    Boolean ProofObligation
    TyNat TyInt TyFloat TyString TyBool TyUnit TyNever TyRef TyArray TyOption TyMap TySet TyFn TyTuple TyPromise TyVar
    Pure Async IO_
    VariableDeclaration VariableStatement FunctionDeclaration ClassDeclaration
    InterfaceDeclaration TypeAliasDeclaration EnumDeclaration ModuleDeclaration
    ExportDeclaration ImportDeclaration ReturnStatement IfStatement SwitchStatement
    ForOfStatement ForStatement WhileStatement TryStatement ThrowStatement
    ExpressionStatement Block VariableDeclarationKind
    TypeFlags ConditionalType Signature Symbol
    cap relToLean jsdocComment go cls ns state output __object verify parseArgs
    sanitize genExpr genPat needsParens emit
    emitFunc emitStruct emitInductive emitTypeAlias emitNamespace emitSection
    emitInstance emitClass emitTheorem emitVarDecl emitComment
    fmtExplicitTPs trySInterp flattenConcat collectStructInfo
    collectExpr collectExpr' check
    hasDOPattern CF_AMBIENT makeAmbientHost DO_LEAN_IMPORTS
    transpileProject' toLeanPath'
    bodyContainsAwait bodyContainsThrow bodyContainsMutation bodyContainsIO
    isAssignOp isIncrDecr isNestedFnScope leanTypeName getFunctionBody
    mapUnion mapIntersection mapObject mapTypeRef getAliasName typeStr
    detectDiscriminant rewriteDiscCase substituteFieldAccesses
  )
  -- ts.* sub-namespace for TypeFlags/ObjectFlags/SyntaxKind
  namespace ts
    namespace TypeFlags
      def Any            := TSLean.Generated.SelfHost.Prelude.ts.TypeFlags.Any
      def Unknown        := TSLean.Generated.SelfHost.Prelude.ts.TypeFlags.Unknown
      def String         := TSLean.Generated.SelfHost.Prelude.ts.TypeFlags.String
      def Number         := TSLean.Generated.SelfHost.Prelude.ts.TypeFlags.Number
      def Boolean        := TSLean.Generated.SelfHost.Prelude.ts.TypeFlags.Boolean
      def BigInt         := TSLean.Generated.SelfHost.Prelude.ts.TypeFlags.BigInt
      def StringLiteral  := TSLean.Generated.SelfHost.Prelude.ts.TypeFlags.StringLiteral
      def NumberLiteral  := TSLean.Generated.SelfHost.Prelude.ts.TypeFlags.NumberLiteral
      def BooleanLiteral := TSLean.Generated.SelfHost.Prelude.ts.TypeFlags.BooleanLiteral
      def Undefined      := TSLean.Generated.SelfHost.Prelude.ts.TypeFlags.Undefined
      def Null           := TSLean.Generated.SelfHost.Prelude.ts.TypeFlags.Null
      def Void           := TSLean.Generated.SelfHost.Prelude.ts.TypeFlags.Void
      def Never          := TSLean.Generated.SelfHost.Prelude.ts.TypeFlags.Never
      def TypeParameter  := TSLean.Generated.SelfHost.Prelude.ts.TypeFlags.TypeParameter
      def Object         := TSLean.Generated.SelfHost.Prelude.ts.TypeFlags.Object
      def Index          := TSLean.Generated.SelfHost.Prelude.ts.TypeFlags.Index
      def Conditional    := TSLean.Generated.SelfHost.Prelude.ts.TypeFlags.Conditional
    end TypeFlags
    namespace ObjectFlags
      def Reference := TSLean.Generated.SelfHost.Prelude.ts.ObjectFlags.Reference
    end ObjectFlags
    namespace SyntaxKind
      def EqualsToken         := TSLean.Generated.SelfHost.Prelude.ts.SyntaxKind.EqualsToken
      def PlusEqualsToken     := TSLean.Generated.SelfHost.Prelude.ts.SyntaxKind.PlusEqualsToken
      def MinusEqualsToken    := TSLean.Generated.SelfHost.Prelude.ts.SyntaxKind.MinusEqualsToken
      def AsteriskEqualsToken := TSLean.Generated.SelfHost.Prelude.ts.SyntaxKind.AsteriskEqualsToken
      def SlashEqualsToken    := TSLean.Generated.SelfHost.Prelude.ts.SyntaxKind.SlashEqualsToken
      def PercentEqualsToken  := TSLean.Generated.SelfHost.Prelude.ts.SyntaxKind.PercentEqualsToken
      def PlusPlusToken       := TSLean.Generated.SelfHost.Prelude.ts.SyntaxKind.PlusPlusToken
      def MinusMinusToken     := TSLean.Generated.SelfHost.Prelude.ts.SyntaxKind.MinusMinusToken
    end SyntaxKind
  end ts
end TSLean
