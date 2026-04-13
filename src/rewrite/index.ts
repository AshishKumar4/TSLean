// Rewrite pass: post-parse IR transformations.
// Primary job: string-discriminant matches → proper inductive pattern matching.
// e.g. (match s.kind with | "circle" => ...) → (match s with | Shape.Circle r => ...)

import {
  IRModule, IRDecl, IRExpr, IRType, IRPattern, IRCase, DoStmt,
  TyRef, TyFloat, TyString, TyUnit, Pure,
} from '../ir/types.js';

// ─── Public API ───────────────────────────────────────────────────────────────

export function rewriteModule(mod: IRModule): IRModule {
  const ctx = new RewriteCtx();
  for (const d of mod.decls) ctx.collectUnionInfo(d);
  return { ...mod, decls: mod.decls.map(d => ctx.rewriteDecl(d)) };
}

// ─── Union registry ───────────────────────────────────────────────────────────

interface UnionInfo {
  typeName: string;
  discField: string;
  variants: Map<string, VariantInfo>;
}

interface VariantInfo {
  ctorName: string;
  fields: string[];
}

const DISC_FIELDS = new Set(['kind', 'type', 'tag', 'ok', 'hasValue', '_type', '__type']);

// ─── Rewrite context ──────────────────────────────────────────────────────────

class RewriteCtx {
  private unions = new Map<string, UnionInfo>();

  collectUnionInfo(d: IRDecl): void {
    if (d.tag !== 'InductiveDef') return;
    const variants = new Map<string, VariantInfo>();
    for (const ctor of d.ctors) {
      const lower = ctor.name[0].toLowerCase() + ctor.name.slice(1);
      const info: VariantInfo = {
        ctorName: `${d.name}.${ctor.name}`,
        fields: ctor.fields.map(f => f.name ?? '_').filter(Boolean),
      };
      variants.set(lower,    info);
      variants.set(ctor.name, info);
    }
    this.unions.set(d.name, { typeName: d.name, discField: 'kind', variants });
  }

  rewriteDecl(d: IRDecl): IRDecl {
    switch (d.tag) {
      case 'FuncDef':     return { ...d, body: this.rewrite(d.body) };
      case 'Namespace':   return { ...d, decls: d.decls.map(x => this.rewriteDecl(x)) };
      case 'VarDecl':     return { ...d, value: this.rewrite(d.value) };
      case 'InstanceDef': return { ...d, methods: d.methods.map(x => this.rewriteDecl(x)) };
      default:            return d;
    }
  }

  private rewrite(e: IRExpr): IRExpr {
    switch (e.tag) {
      case 'Match':       return this.rewriteMatch(e);
      case 'IfThenElse':  return { ...e, cond: this.rewrite(e.cond), then: this.rewrite(e.then), else_: this.rewrite(e.else_) };
      case 'Let':         return { ...e, value: this.rewrite(e.value), body: this.rewrite(e.body) };
      case 'Bind':        return { ...e, monad: this.rewrite(e.monad), body: this.rewrite(e.body) };
      case 'Lambda':      return { ...e, body: this.rewrite(e.body) };
      case 'App':         return { ...e, fn: this.rewrite(e.fn), args: e.args.map(a => this.rewrite(a)) };
      case 'Sequence':    return { ...e, stmts: e.stmts.map(s => this.rewrite(s)) };
      case 'StructLit':   return { ...e, fields: e.fields.map(f => ({ ...f, value: this.rewrite(f.value) })) };
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

  private rewriteMatch(e: Extract<IRExpr, { tag: 'Match' }>): IRExpr {
    const disc = this.detectDiscriminant(e.scrutinee);
    if (!disc) {
      return { ...e, scrutinee: this.rewrite(e.scrutinee), cases: e.cases.map(c => this.rewriteCase(c)) };
    }

    const { obj, union } = disc;
    if (!union) {
      return { ...e, scrutinee: this.rewrite(e.scrutinee), cases: e.cases.map(c => this.rewriteCase(c)) };
    }

    // Pass the scrutinee variable name so case bodies can substitute s.field → patternVar
    const scrutineeName = obj.tag === 'Var' ? obj.name : null;
    const newCases = e.cases.map(c => this.rewriteDiscCase(c, union, scrutineeName));
    return { ...e, scrutinee: this.rewrite(obj), cases: newCases };
  }

  private detectDiscriminant(scrutinee: IRExpr): { obj: IRExpr; field: string; union: UnionInfo | null } | null {
    if (scrutinee.tag !== 'FieldAccess') return null;
    if (!DISC_FIELDS.has(scrutinee.field)) return null;

    const obj   = scrutinee.obj;
    const field = scrutinee.field;
    let union: UnionInfo | null = null;

    // Try by type name
    if (obj.type.tag === 'TypeRef')   union = this.unions.get(obj.type.name) ?? null;
    if (obj.type.tag === 'Inductive') union = this.unions.get(obj.type.name) ?? null;

    // Try by discriminant field name
    if (!union) {
      for (const u of this.unions.values()) {
        if (u.discField === field) { union = u; break; }
      }
    }

    return { obj, field, union };
  }

  private rewriteDiscCase(c: IRCase, union: UnionInfo, scrutineeName: string | null): IRCase {
    const p = c.pattern;
    const key = p.tag === 'PString' ? p.value : (p.tag === 'PLit' && typeof p.value === 'string') ? p.value : null;
    if (key !== null) {
      const info = union.variants.get(key);
      if (info) {
        const args = info.fields.map(f => ({ tag: 'PVar' as const, name: f }));
        // Build substitution: scrutinee.field → pattern-bound variable for that field.
        // This is critical for inductive types — s.radius is invalid after matching .Circle radius;
        // the correct reference is the pattern variable `radius` directly.
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
}

// ─── Field access substitution ────────────────────────────────────────────────
// After `match s with | .Circle radius =>`, the variable `s` no longer has a `.radius`
// field accessor — it's an inductive, not a structure. We substitute `s.radius` → `radius`
// using the pattern-bound variable name from the PCtor pattern.

function substituteFieldAccesses(
  expr: IRExpr,
  scrutineeName: string,
  subst: Map<string, string>
): IRExpr {
  function go(e: IRExpr): IRExpr {
    if (e.tag === 'FieldAccess' &&
        e.obj.tag === 'Var' &&
        e.obj.name === scrutineeName &&
        subst.has(e.field)) {
      return { tag: 'Var', name: subst.get(e.field)!, type: e.type, effect: e.effect };
    }
    switch (e.tag) {
      case 'FieldAccess':  return { ...e, obj: go(e.obj) };
      case 'IndexAccess':  return { ...e, obj: go(e.obj), index: go(e.index) };
      case 'App':          return { ...e, fn: go(e.fn), args: e.args.map(go) };
      case 'TypeApp':      return { ...e, fn: go(e.fn) };
      case 'Lambda':       return { ...e, body: go(e.body) };
      case 'Let':          return { ...e, value: go(e.value), body: go(e.body) };
      case 'Bind':         return { ...e, monad: go(e.monad), body: go(e.body) };
      case 'IfThenElse':   return { ...e, cond: go(e.cond), then: go(e.then), else_: go(e.else_) };
      case 'Match':        return { ...e, scrutinee: go(e.scrutinee), cases: e.cases.map(c => ({ ...c, body: go(c.body), guard: c.guard ? go(c.guard) : undefined })) };
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
