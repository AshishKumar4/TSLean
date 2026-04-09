-- TSLean.Generated.SelfHost.Prelude
-- Forward declarations for cross-file references in self-hosting pipeline.
-- Does NOT import IR_Types.lean to avoid cycles.

import TSLean.External.Typescript
import TSLean.Runtime.Basic
import TSLean.Runtime.Coercions
import TSLean.Runtime.Monad
import TSLean.Stdlib.HashMap

open TSLean TSLean.External.Typescript TSLean.Stdlib.HashMap

namespace TSLean.Generated.SelfHost.Prelude

-- IR type stubs (real types in IR_Types.lean)
abbrev IRType'   := Unit
abbrev IRExpr'   := Unit
abbrev IRDecl'   := Unit
abbrev IRModule' := Unit
abbrev Effect'   := Unit

-- Parser
opaque parseFileSync (path : String) : IRModule'

-- Type mapper
opaque mapType (checker : TypeChecker) (tsType : TSType) (depth : Nat := 0) : IRType'
opaque irTypeToLean' (t : IRType') (parens : Bool := false) : String
opaque extractStructFields (checker : TypeChecker) (node : Node) : Array (String × IRType' × Bool)
opaque extractTypeParams (node : Node) : Array String
opaque detectDiscriminatedUnion (fields : Array String) : Option String

-- Effects
opaque inferNodeEffect (node : Node) (checker : TypeChecker) : Effect'
opaque monadString' (effect : Effect') (stateTypeName : String := "σ") : String
opaque doMonadType (stateTypeName : String) : String
opaque joinEffects' (a b : Effect') : Effect'
opaque effectSubsumes' (a b : Effect') : Bool
opaque combineEffects' (effects : Array Effect') : Effect'
opaque getFunctionBody (node : TSAny) : Option TSAny
opaque bodyContainsAwait (node : TSAny) : Bool
opaque bodyContainsThrow (node : TSAny) : Bool
opaque bodyContainsMutation (node : TSAny) : Bool
opaque bodyContainsIO (node : TSAny) : Bool

-- Rewrite
opaque rewriteModule' (mod : IRModule') : IRModule'

-- Codegen
opaque generateLean' (mod : IRModule') : String
opaque sanitize' (name : String) : String
opaque genPattern (p : String) : String

-- Stdlib
opaque translateBinOp' (op : String) (lhsType : IRType') : String
opaque lookupGlobal' (name : String) : Option String
opaque lookupMethod' (kind : String) (method : String) : Option String

-- Verification
opaque collectExpr' (e : IRExpr') (funcName : String) : Array String
opaque generateVerification' (mod : IRModule') : String

-- DO model
opaque hasDOPattern (source : String) : Bool
opaque CF_AMBIENT : String
opaque makeAmbientHost (base : CompilerHost) (virtual : AssocMap String String) : CompilerHost
opaque DO_LEAN_IMPORTS : List String

-- Project
opaque transpileProject' (rootDir outputDir : String) : IO Unit
opaque toLeanPath' (tsFile projectDir outputDir : String) : String

-- TS SyntaxKind aliases used by the codegen
def VariableDeclaration : SyntaxKind := .VariableDeclaration
def VariableStatement : SyntaxKind := .VariableStatement
def FunctionDeclaration : SyntaxKind := .FunctionDeclaration
def ClassDeclaration : SyntaxKind := .ClassDeclaration
def InterfaceDeclaration : SyntaxKind := .InterfaceDeclaration
def TypeAliasDeclaration : SyntaxKind := .TypeAliasDeclaration
def EnumDeclaration : SyntaxKind := .EnumDeclaration
def ModuleDeclaration : SyntaxKind := .ModuleDeclaration
def ExportDeclaration : SyntaxKind := .ExportDeclaration
def ImportDeclaration : SyntaxKind := .ImportDeclaration
def ReturnStatement : SyntaxKind := .ReturnStatement
def IfStatement : SyntaxKind := .IfStatement
def SwitchStatement : SyntaxKind := .SwitchStatement
def ForOfStatement : SyntaxKind := .ForOfStatement
def ForStatement : SyntaxKind := .ForStatement
def WhileStatement : SyntaxKind := .WhileStatement
def TryStatement : SyntaxKind := .TryStatement
def ThrowStatement : SyntaxKind := .ThrowStatement
def ExpressionStatement : SyntaxKind := .ExpressionStatement
def Block : SyntaxKind := .Block

-- IR type constructor aliases (used when raw output references TyNat etc.)
-- These are defined in ir_types.lean; we provide fallbacks here for files
-- that import Prelude but not ir_types.
def TyNat : String := "Nat"
def TyInt : String := "Int"
def TyFloat : String := "Float"
def TyString : String := "String"
def TyBool : String := "Bool"
def TyUnit : String := "Unit"
def TyNever : String := "Never"
def TyRef (name : String) : String := name
def TyArray (elem : String) : String := s!"Array {elem}"
def TyOption (inner : String) : String := s!"Option {inner}"
def TyMap (k v : String) : String := s!"AssocMap {k} {v}"
def TySet (elem : String) : String := s!"AssocSet {elem}"

-- Common constants from the codegen
def Pure : String := "Pure"
def Async : String := "Async"
def IO_ : String := "IO"

end TSLean.Generated.SelfHost.Prelude
