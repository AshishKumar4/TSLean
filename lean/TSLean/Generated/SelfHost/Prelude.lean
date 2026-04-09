-- TSLean.Generated.SelfHost.Prelude
--
-- Forward declarations for cross-file references in the self-hosting pipeline.
-- Does NOT import IR_Types.lean to avoid import cycles when both Prelude
-- and IR_Types are imported by the same file.
-- Instead, provides opaque type stubs for the IR types.

import TSLean.External.Typescript
import TSLean.Runtime.Basic
import TSLean.Runtime.Coercions
import TSLean.Runtime.Monad
import TSLean.Stdlib.HashMap

open TSLean TSLean.External.Typescript TSLean.Stdlib.HashMap

namespace TSLean.Generated.SelfHost.Prelude

-- ─── Opaque IR type stubs ───────────────────────────────────────────────────────
-- These mirror the types in IR_Types.lean without importing them.
-- Any file that needs the REAL types should import IR_Types directly.

-- Minimal IR type stubs (avoids importing IR_Types.lean)
-- Using Unit as placeholder; real types are in IR_Types.lean.
abbrev IRType'   := Unit
abbrev IRExpr'   := Unit
abbrev IRDecl'   := Unit
abbrev IRModule' := Unit
abbrev Effect'   := Unit

-- ─── Parser ─────────────────────────────────────────────────────────────────────

opaque parseFileSync (path : String) : IRModule'

-- ─── Type mapper ────────────────────────────────────────────────────────────────

opaque mapType (checker : TypeChecker) (tsType : TSType) (depth : Nat := 0) : IRType'
opaque irTypeToLean (t : IRType') (parens : Bool := false) : String
opaque extractStructFields (checker : TypeChecker) (node : Node) : Array (String × IRType' × Bool)
opaque extractTypeParams (node : Node) : Array String
opaque detectDiscriminatedUnion (fields : Array String) : Option String

-- ─── Effects ────────────────────────────────────────────────────────────────────

opaque inferNodeEffect (node : Node) (checker : TypeChecker) : Effect'
opaque monadString (effect : Effect') (stateTypeName : String := "σ") : String
opaque doMonadType (stateTypeName : String) : String
opaque joinEffects (a b : Effect') : Effect'
opaque effectSubsumes (a b : Effect') : Bool

-- ─── Rewrite ────────────────────────────────────────────────────────────────────

opaque rewriteModule (mod : IRModule') : IRModule'

-- ─── Codegen ────────────────────────────────────────────────────────────────────

opaque generateLean (mod : IRModule') : String
opaque sanitize (name : String) : String
opaque genPattern (p : String) : String

-- ─── Stdlib ─────────────────────────────────────────────────────────────────────

opaque translateBinOp (op : String) (lhsType : IRType') : String
opaque lookupGlobal (name : String) : Option String

-- ─── Verification ───────────────────────────────────────────────────────────────

opaque collectExpr (e : IRExpr') (funcName : String) : Array String
opaque generateVerification (mod : IRModule') : String

-- ─── DO model ───────────────────────────────────────────────────────────────────

opaque hasDOPattern (source : String) : Bool
opaque CF_AMBIENT : String
opaque makeAmbientHost (base : CompilerHost) (virtual : AssocMap String String) : CompilerHost
opaque DO_LEAN_IMPORTS : List String

-- ─── Project ────────────────────────────────────────────────────────────────────

opaque transpileProject (rootDir outputDir : String) : IO Unit
opaque toLeanPath (tsFile projectDir outputDir : String) : String

end TSLean.Generated.SelfHost.Prelude
