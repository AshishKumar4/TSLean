/-
  TSLean.Proofs.RewritePreservation
  Theorems proving that the rewrite pass preserves IR structure.
-/
import TSLean.Generated.SelfHost.ir_types
import TSLean.Generated.SelfHost.rewrite_index
import TSLean.Stdlib.HashMap

open TSLean.Generated.Types
open TSLean.Generated.SelfHost.RewriteIndex
open TSLean.Stdlib.HashMap

-- ─── rwExpr is the identity ──────────────────────────────────────────────────────

theorem rwExpr_id (ctx : RewriteCtxState) (e : IRExpr) :
    RewriteCtx.rwExpr ctx e = e := by rfl

-- ─── rewriteCase preserves the case ──────────────────────────────────────────────

theorem rewriteCase_id (ctx : RewriteCtxState) (c : IRCase) :
    RewriteCtx.rewriteCase ctx c = c := by rfl

-- ─── rewriteDoStmt preserves the statement ───────────────────────────────────────

theorem rewriteDoStmt_id (ctx : RewriteCtxState) (s : DoStmt) :
    RewriteCtx.rewriteDoStmt ctx s = s := by rfl

-- ─── substituteFieldAccesses is the identity ─────────────────────────────────────

theorem substituteFieldAccesses_id (expr : IRExpr) (name : String)
    (subst : AssocMap String String) :
    substituteFieldAccesses expr name subst = expr := by rfl

-- ─── rewriteStructLit always returns none ────────────────────────────────────────

theorem rewriteStructLit_none (ctx : RewriteCtxState) (e : IRExpr) :
    RewriteCtx.rewriteStructLit ctx e = none := by rfl

-- ─── rewriteFields is the identity ──────────────────────────────────────────────

theorem rewriteFields_id (ctx : RewriteCtxState) (e : IRExpr) :
    RewriteCtx.rewriteFields ctx e = e := by rfl

-- ─── rewriteDecl preserves FuncDef (since rwExpr is id) ─────────────────────────

theorem rewriteDecl_FuncDef_body (ctx : RewriteCtxState) n tp ps rt eff body cm ip w dc :
    RewriteCtx.rewriteDecl ctx (.FuncDef n tp ps rt eff body cm ip w dc) =
    .FuncDef n tp ps rt eff body cm ip w dc := by
  simp [RewriteCtx.rewriteDecl, RewriteCtx.rwExpr]

-- ─── rewriteModule preserves module metadata ─────────────────────────────────────

theorem rewriteModule_preserves_name (mod : IRModule) :
    (rewriteModule mod).name = mod.name := by rfl

theorem rewriteModule_preserves_imports (mod : IRModule) :
    (rewriteModule mod).imports = mod.imports := by rfl

theorem rewriteModule_preserves_comments (mod : IRModule) :
    (rewriteModule mod).comments = mod.comments := by rfl

theorem rewriteModule_preserves_decl_count (mod : IRModule) :
    (rewriteModule mod).decls.size = mod.decls.size := by
  simp [rewriteModule, Array.size_map]

-- ─── collectUnionInfo only modifies on InductiveDef ──────────────────────────────

-- For non-InductiveDef constructors, collectUnionInfo returns ctx unchanged.
-- We prove this by testing specific constructors via native_decide on the tag.

theorem collectUnionInfo_RawLean (ctx : RewriteCtxState) (code : String) :
    RewriteCtx.collectUnionInfo ctx (.RawLean code) = ctx := by rfl

-- ─── detectDiscriminant correctness ──────────────────────────────────────────────

theorem detectDiscriminant_non_field :
    RewriteCtx.detectDiscriminant default { tag := "Var" } = none := by native_decide

theorem detectDiscriminant_field_tag :
    RewriteCtx.detectDiscriminant default { tag := "FieldAccess", field := "tag" } = some "tag" := by
  native_decide

theorem detectDiscriminant_field_kind :
    RewriteCtx.detectDiscriminant default { tag := "FieldAccess", field := "kind" } = some "kind" := by
  native_decide

theorem detectDiscriminant_field_unknown :
    RewriteCtx.detectDiscriminant default { tag := "FieldAccess", field := "foo" } = none := by
  native_decide

-- ─── Type and effect preservation ────────────────────────────────────────────────

theorem rewrite_preserves_expr_type (ctx : RewriteCtxState) (e : IRExpr) :
    (RewriteCtx.rwExpr ctx e).type = e.type := by rfl

theorem rewrite_preserves_expr_effect (ctx : RewriteCtxState) (e : IRExpr) :
    (RewriteCtx.rwExpr ctx e).effect = e.effect := by rfl
