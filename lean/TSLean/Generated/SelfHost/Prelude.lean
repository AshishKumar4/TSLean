-- TSLean.Generated.SelfHost.Prelude
--
-- Forward declarations for cross-file references in the self-hosting pipeline.
-- When the transpiler regenerates SelfHost files, the fresh output may reference
-- functions defined in OTHER SelfHost modules before they are imported.  This
-- prelude provides opaque stubs so every module can see every cross-file symbol.
--
-- Import this file first in any regenerated SelfHost module:
--   import TSLean.Generated.SelfHost.Prelude

import TSLean.Generated.SelfHost.IR_Types
import TSLean.External.Typescript
import TSLean.Runtime.Basic
import TSLean.Runtime.Coercions
import TSLean.Runtime.Monad
import TSLean.Stdlib.HashMap

open TSLean TSLean.Generated.Types TSLean.External.Typescript TSLean.Stdlib.HashMap

namespace TSLean.Generated.SelfHost.Prelude

-- ─── Parser ─────────────────────────────────────────────────────────────────────

/-- Parse a TypeScript source file into an IR module.
    Opaque — the real implementation is in `parser_index.lean`. -/
opaque parseFile (opts : { filePath : String // True }) : IRModule

/-- Parse a file by path (simplified). -/
opaque parseFileSync (path : String) : IRModule

-- ─── Type mapper ────────────────────────────────────────────────────────────────

/-- Map a TypeScript compiler type to an IR type.
    Opaque — the real implementation is in `typemap_index.lean`. -/
opaque mapType (checker : TypeChecker) (tsType : TSType) (depth : Nat := 0) : IRType

/-- Convert an IR type to its Lean 4 syntax string.
    Partial — recursive over the IRType structure. -/
opaque irTypeToLean (t : IRType) (parens : Bool := false) : String

/-- Extract struct fields from a TypeScript interface/class. -/
opaque extractStructFields (checker : TypeChecker) (node : Node) : Array (String × IRType × Bool)

/-- Extract type parameter names from a declaration. -/
opaque extractTypeParams (node : Node) : Array String

/-- Detect a discriminated union in a TypeScript union type. -/
opaque detectDiscriminatedUnion (fields : Array String) : Option String

-- ─── Effects ────────────────────────────────────────────────────────────────────

/-- Infer the algebraic effect of a TypeScript AST node. -/
opaque inferNodeEffect (node : Node) (checker : TypeChecker) : Effect

/-- Convert an Effect to its Lean 4 monad string. -/
opaque monadString (effect : Effect) (stateTypeName : String := "σ") : String

/-- Generate the DOMonad type string. -/
opaque doMonadType (stateTypeName : String) : String

/-- Compute the join of two effects. -/
opaque joinEffects (a b : Effect) : Effect

/-- Test whether effect `a` subsumes effect `b`. -/
opaque effectSubsumes (a b : Effect) : Bool

-- ─── Rewrite ────────────────────────────────────────────────────────────────────

/-- Apply all rewrite transformations to a parsed IR module. -/
opaque rewriteModule (mod : IRModule) : IRModule

-- ─── Codegen ────────────────────────────────────────────────────────────────────

/-- Generate Lean 4 source from an IR module. -/
opaque generateLean (mod : IRModule) : String

/-- Escape Lean 4 keywords and special characters. -/
opaque sanitize (name : String) : String

/-- Render an IR pattern as Lean syntax. -/
opaque genPattern (p : IRPattern) : String

-- ─── Stdlib ─────────────────────────────────────────────────────────────────────

/-- Translate a binary operator to its Lean syntax. -/
opaque translateBinOp (op : BinOp) (lhsType : IRType) : String

/-- Look up a global function translation (e.g. console.log → IO.println). -/
opaque lookupGlobal (name : String) : Option String

-- ─── Verification ───────────────────────────────────────────────────────────────

/-- Collect proof obligations from an expression tree. -/
opaque collectExpr (e : IRExpr) (funcName : String) : Array String

/-- Generate verification obligations for an entire module. -/
opaque generateVerification (mod : IRModule) : String

-- ─── DO model ───────────────────────────────────────────────────────────────────

/-- Check if source text contains Durable Object patterns. -/
opaque hasDOPattern (source : String) : Bool

/-- The ambient type declarations injected for DO compilation. -/
opaque CF_AMBIENT : String

/-- Create an augmented compiler host that overlays virtual files. -/
opaque makeAmbientHost (base : CompilerHost) (virtual : AssocMap String String) : CompilerHost

/-- Standard DO imports for generated Lean files. -/
opaque DO_LEAN_IMPORTS : List String

-- ─── Project ────────────────────────────────────────────────────────────────────

/-- Transpile an entire project directory. -/
opaque transpileProject (rootDir outputDir : String) : IO Unit

/-- Convert a TypeScript path to the corresponding Lean module path. -/
opaque toLeanPath (tsFile projectDir outputDir : String) : String

-- ─── Specification ──────────────────────────────────────────────────────────────

/-- Resolve a specification annotation from a TypeScript comment. -/
opaque resolveSpec (comment : String) : Option String

/-- Convert a specification to Lean theorem syntax. -/
opaque specToLean (spec : String) (funcName : String) : String

end TSLean.Generated.SelfHost.Prelude
