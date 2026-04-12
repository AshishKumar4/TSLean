/**
 * @module rewrite
 *
 * Post-parse IR transformation pass.
 *
 * Primary job: convert **string-discriminant matches** into proper inductive
 * pattern matching — the hallmark transformation of the transpiler.
 *
 * Before (TS idiom):
 * ```ts
 * switch (shape.kind) {
 *   case "circle": return Math.PI * shape.radius ** 2;
 *   case "rect":   return shape.width * shape.height;
 * }
 * ```
 *
 * After (Lean 4 IR):
 * ```lean
 * match shape with
 * | .Circle radius => Float.pi * radius ^ 2
 * | .Rect width height => width * height
 * ```
 *
 * The pass also substitutes field accesses (`s.radius`) with the pattern-bound
 * variable (`radius`) inside rewritten match arms, since the scrutinee becomes
 * an inductive value — not a structure — after matching.
 *
 * Pipeline position:  Parser → IR → **Rewrite** → Codegen → Lean 4
 */

import {
  IRModule, IRDecl, IRExpr, IRType, IRPattern, IRCase, DoStmt,
  TyRef, TyFloat, TyString, TyUnit, Pure,
} from '../ir/types.js';
import { DISCRIMINANT_FIELDS as DISCRIMINANT_FIELDS_LIST } from '../utils.js';

// ─── Public API ─────────────────────────────────────────────────────────────────

/**
 * Apply all rewrite transformations to a parsed IR module.
 *
 * 1. Collects union metadata from `InductiveDef` declarations.
 * 2. Rewrites `Match` nodes that scrutinise discriminant fields.
 * 3. Substitutes `s.field` references with pattern-bound variables.
 *
 * @param mod - The parsed IR module (unmodified).
 * @returns A new IR module with all rewrites applied.
 */
export function rewriteModule(mod: IRModule): IRModule {
  const ctx = new RewriteCtx();
  for (const d of mod.decls) ctx.collectUnionInfo(d);
  return { ...mod, decls: mod.decls.map(d => ctx.rewriteDecl(d)) };
}

// ─── Union registry ─────────────────────────────────────────────────────────────

/** Metadata about a discriminated union type. */
interface UnionInfo {
  typeName: string;
  /** The field name used as discriminant (e.g. "kind", "tag", "type"). */
  discField: string;
  /** Maps lowercase literal → constructor info.  Includes both `circle` and `Circle` keys. */
  variants: Map<string, VariantInfo>;
}

/** Info about one variant (constructor) of a discriminated union. */
interface VariantInfo {
  /** Fully-qualified constructor name: `Shape.Circle`. */
  ctorName: string;
  /** Field names bound by the pattern. */
  fields: string[];
}

/** Set form of DISCRIMINANT_FIELDS for O(1) lookup in the rewrite pass. */
const DISCRIMINANT_FIELDS = new Set(DISCRIMINANT_FIELDS_LIST);

// ─── Rewrite context ────────────────────────────────────────────────────────────

class RewriteCtx {
  private unions = new Map<string, UnionInfo>();

  /** Extract union metadata from an InductiveDef declaration. */
  collectUnionInfo(d: IRDecl): void {
    if (d.tag !== 'InductiveDef') return;
    const variants = new Map<string, VariantInfo>();
    for (const ctor of d.ctors) {
      const lower = ctor.name[0].toLowerCase() + ctor.name.slice(1);
      const info: VariantInfo = {
        ctorName: `${d.name}.${ctor.name}`,
        fields: ctor.fields.map(f => f.name ?? '_').filter(Boolean),
      };
      // Register both camelCase and PascalCase keys so "circle" and "Circle" both match
      variants.set(lower,     info);
      variants.set(ctor.name, info);
    }
    // discField starts empty and is refined when a match scrutinee is analysed
    this.unions.set(d.name, { typeName: d.name, discField: '', variants });
  }

  /** Recursively rewrite all declarations. */
  rewriteDecl(d: IRDecl): IRDecl {
    switch (d.tag) {
      case 'FuncDef':     return { ...d, body: this.rewrite(d.body) };
      case 'Namespace':   return { ...d, decls: d.decls.map(x => this.rewriteDecl(x)) };
      case 'VarDecl':     return { ...d, value: this.rewrite(d.value) };
      case 'InstanceDef': return { ...d, methods: d.methods.map(x => this.rewriteDecl(x)) };
      default:            return d;
    }
  }

  // ─── Expression rewriting ─────────────────────────────────────────────────

  /** Recursively rewrite an IR expression tree. */
  private rewrite(e: IRExpr): IRExpr {
    switch (e.tag) {
      case 'Match':       return this.rewriteMatch(e);
      // Rewrite struct literals that are discriminated union constructor calls.
      // e.g. { type: "left", value: v } → CtorApp("Either.Left", [v])
      case 'StructLit':   return this.rewriteStructLit(e) ?? this.rewriteFields(e);
      case 'IfThenElse':  return { ...e, cond: this.rewrite(e.cond), then: this.rewrite(e.then), else_: this.rewrite(e.else_) };
      case 'Let':         return { ...e, value: this.rewrite(e.value), body: this.rewrite(e.body) };
      case 'Bind':        return { ...e, monad: this.rewrite(e.monad), body: this.rewrite(e.body) };
      case 'Lambda':      return { ...e, body: this.rewrite(e.body) };
      case 'App':         return { ...e, fn: this.rewrite(e.fn), args: e.args.map(a => this.rewrite(a)) };
      case 'Sequence':    return { ...e, stmts: e.stmts.map(s => this.rewrite(s)) };
      case 'ArrayLit':    return { ...e, elems: e.elems.map(x => this.rewrite(x)) };
      case 'TupleLit':    return { ...e, elems: e.elems.map(x => this.rewrite(x)) };
      case 'DoBlock':     return { ...e, stmts: e.stmts.map(s => this.rewriteDoStmt(s)) };
      case 'BinOp':       return { ...e, left: this.rewrite(e.left), right: this.rewrite(e.right) };
      case 'UnOp':        return { ...e, operand: this.rewrite(e.operand) };
      case 'TryCatch':    return { ...e, body: this.rewrite(e.body), handler: this.rewrite(e.handler) };
      case 'Await':       return { ...e, expr: this.rewrite(e.expr) };
      case 'Assign':      return { ...e, target: this.rewrite(e.target), value: this.rewrite(e.value) };
      case 'FieldAccess': return { ...e, obj: this.rewrite(e.obj) };
      case 'IndexAccess': return { ...e, obj: this.rewrite(e.obj), index: this.rewrite(e.index) };
      case 'Cast':        return { ...e, expr: this.rewrite(e.expr) };
      case 'Return':      return { ...e, value: this.rewrite(e.value) };
      case 'Throw':       return { ...e, error: this.rewrite(e.error) };
      case 'CtorApp':     return { ...e, args: e.args.map(a => this.rewrite(a)) };
      case 'Pure_':       return { ...e, value: this.rewrite(e.value) };
      case 'StructUpdate':return { ...e, base: this.rewrite(e.base), fields: e.fields.map(f => ({ ...f, value: this.rewrite(f.value) })) };
      default:            return e;
    }
  }

  private rewriteDoStmt(s: DoStmt): DoStmt {
    switch (s.tag) {
      case 'DoBind':   return { ...s, expr: this.rewrite(s.expr) };
      case 'DoLet':    return { ...s, value: this.rewrite(s.value) };
      case 'DoExpr':   return { ...s, expr: this.rewrite(s.expr) };
      case 'DoReturn': return { ...s, value: this.rewrite(s.value) };
    }
  }

  // ─── Match rewriting (the core transformation) ────────────────────────────

  /**
   * Detect whether a Match scrutinises a discriminant field (`s.kind`, `s.tag`,
   * etc.) and, if so, rewrite the string-literal cases into proper inductive
   * constructor patterns.
   */
  private rewriteMatch(e: Extract<IRExpr, { tag: 'Match' }>): IRExpr {
    const disc = this.detectDiscriminant(e.scrutinee);
    if (!disc?.union) {
      return { ...e, scrutinee: this.rewrite(e.scrutinee), cases: e.cases.map(c => this.rewriteCase(c)) };
    }

    const { obj, union } = disc;
    const scrutineeName = obj.tag === 'Var' ? obj.name : null;
    const newCases = e.cases.map(c => this.rewriteDiscCase(c, union, scrutineeName));
    return { ...e, scrutinee: this.rewrite(obj), cases: newCases };
  }

  /**
   * Detect whether a match scrutinee is `obj.<discriminantField>`.
   *
   * If so, look up the union by the object's type name and refine its
   * `discField` to the actual field observed (handles `tag`, `type`, `ok`, etc.).
   */
  private detectDiscriminant(scrutinee: IRExpr): { obj: IRExpr; field: string; union: UnionInfo | null } | null {
    if (scrutinee.tag !== 'FieldAccess') return null;
    if (!DISCRIMINANT_FIELDS.has(scrutinee.field)) return null;

    const obj   = scrutinee.obj;
    const field = scrutinee.field;
    let union: UnionInfo | null = null;

    if (obj.type.tag === 'TypeRef')   union = this.unions.get(obj.type.name) ?? null;
    if (obj.type.tag === 'Inductive') union = this.unions.get(obj.type.name) ?? null;

    // Refine the discriminant field from the actual FieldAccess observed
    if (union) union.discField = field;

    // Fallback: find a union whose previously-observed discriminant matches
    if (!union) {
      for (const u of this.unions.values()) {
        if (u.discField === field) { union = u; break; }
      }
    }

    return { obj, field, union };
  }

  /**
   * Rewrite a single match case: convert `PString("circle")` to
   * `PCtor("Shape.Circle", [radius])` using the union's variant info.
   *
   * Also substitutes field accesses in the case body: `s.radius` → `radius`,
   * since the scrutinee is now an inductive value, not a structure.
   */
  private rewriteDiscCase(c: IRCase, union: UnionInfo, scrutineeName: string | null): IRCase {
    const p = c.pattern;
    const key = p.tag === 'PString' ? p.value
              : (p.tag === 'PLit' && typeof p.value === 'string') ? p.value
              : null;
    if (key !== null) {
      const info = union.variants.get(key);
      if (info) {
        const args = info.fields.map(f => ({ tag: 'PVar' as const, name: f }));
        const subst: Map<string, string> = new Map(info.fields.map(f => [f, f]));
        const rewrittenBody = scrutineeName !== null
          ? substituteFieldAccesses(this.rewrite(c.body), scrutineeName, subst)
          : this.rewrite(c.body);
        return { pattern: { tag: 'PCtor', ctor: info.ctorName, args }, body: rewrittenBody };
      }
    }
    return this.rewriteCase(c);
  }

  private rewriteCase(c: IRCase): IRCase {
    return { ...c, guard: c.guard ? this.rewrite(c.guard) : undefined, body: this.rewrite(c.body) };
  }

  /**
   * Detect struct literals that match a union discriminant pattern and convert
   * them to constructor applications.
   * e.g. `{ type: "left", value: v }` → `CtorApp("Either.Left", [v])`
   */
  private rewriteStructLit(e: Extract<IRExpr, { tag: 'StructLit' }>): IRExpr | null {
    // Look for a field whose value is a string literal matching a known discriminant
    for (const f of e.fields) {
      if (!DISCRIMINANT_FIELDS.has(f.name)) continue;
      if (f.value.tag !== 'LitString') continue;
      const literal = f.value.value;

      // Search all unions for a variant matching this literal
      for (const union of this.unions.values()) {
        const variant = union.variants.get(literal);
        if (!variant) continue;

        // Found a match! Build a CtorApp with the non-discriminant fields as args.
        const args = e.fields
          .filter(field => field.name !== f.name)
          .map(field => this.rewrite(field.value));

        return {
          tag: 'CtorApp',
          ctor: variant.ctorName,
          args,
          type: e.type,
          effect: e.effect,
        };
      }
    }
    return null;
  }

  /** Rewrite fields of a struct literal (when it's not a union constructor). */
  private rewriteFields(e: Extract<IRExpr, { tag: 'StructLit' }>): IRExpr {
    return { ...e, fields: e.fields.map(f => ({ ...f, value: this.rewrite(f.value) })) };
  }
}

// ─── Field access substitution ──────────────────────────────────────────────────
//
// After `match s with | .Circle radius => ...`, the variable `s` is bound to
// the inductive value — it no longer has structure field accessors.  We
// substitute `s.radius` → `radius` using the pattern-bound variable name.

function substituteFieldAccesses(
  expr: IRExpr,
  scrutineeName: string,
  subst: Map<string, string>,
): IRExpr {
  function go(e: IRExpr): IRExpr {
    // Direct substitution: s.field → patternVar
    if (e.tag === 'FieldAccess' &&
        e.obj.tag === 'Var' &&
        e.obj.name === scrutineeName &&
        subst.has(e.field)) {
      return { tag: 'Var', name: subst.get(e.field)!, type: e.type, effect: e.effect };
    }
    // Recursive traversal
    switch (e.tag) {
      case 'FieldAccess':  return { ...e, obj: go(e.obj) };
      case 'IndexAccess':  return { ...e, obj: go(e.obj), index: go(e.index) };
      case 'App':          return { ...e, fn: go(e.fn), args: e.args.map(go) };
      case 'TypeApp':      return { ...e, fn: go(e.fn) };
      case 'Lambda':       return { ...e, body: go(e.body) };
      case 'Let':          return { ...e, value: go(e.value), body: go(e.body) };
      case 'Bind':         return { ...e, monad: go(e.monad), body: go(e.body) };
      case 'IfThenElse':   return { ...e, cond: go(e.cond), then: go(e.then), else_: go(e.else_) };
      case 'Match':        return { ...e, scrutinee: go(e.scrutinee), cases: e.cases.map(c => ({
        ...c, body: go(c.body), guard: c.guard ? go(c.guard) : undefined,
      })) };
      case 'Sequence':     return { ...e, stmts: e.stmts.map(go) };
      case 'StructLit':    return { ...e, fields: e.fields.map(f => ({ ...f, value: go(f.value) })) };
      case 'ArrayLit':     return { ...e, elems: e.elems.map(go) };
      case 'TupleLit':     return { ...e, elems: e.elems.map(go) };
      case 'BinOp':        return { ...e, left: go(e.left), right: go(e.right) };
      case 'UnOp':         return { ...e, operand: go(e.operand) };
      case 'Assign':       return { ...e, target: go(e.target), value: go(e.value) };
      case 'Throw':        return { ...e, error: go(e.error) };
      case 'TryCatch':     return { ...e, body: go(e.body), handler: go(e.handler) };
      case 'Await':        return { ...e, expr: go(e.expr) };
      case 'Cast':         return { ...e, expr: go(e.expr) };
      case 'Return':       return { ...e, value: go(e.value) };
      case 'CtorApp':      return { ...e, args: e.args.map(go) };
      case 'Pure_':        return { ...e, value: go(e.value) };
      case 'StructUpdate': return { ...e, base: go(e.base), fields: e.fields.map(f => ({ ...f, value: go(f.value) })) };
      case 'DoBlock':      return { ...e, stmts: e.stmts.map(s => {
        switch (s.tag) {
          case 'DoBind':   return { ...s, expr: go(s.expr) };
          case 'DoLet':    return { ...s, value: go(s.value) };
          case 'DoExpr':   return { ...s, expr: go(s.expr) };
          case 'DoReturn': return { ...s, value: go(s.value) };
        }
      })};
      default: return e;
    }
  }
  return go(expr);
}
