/**
 * @module codegen/printer
 *
 * Pretty-printer: LeanAST → Lean 4 source text.
 *
 * Design: purely structural — no heuristics, no special cases based on
 * string content. Every LeanAST node maps to exactly one textual form.
 * Indentation is computed from tree depth, not carried as strings.
 *
 * The printer never decides *what* to emit — only *how* to format it.
 * All semantic decisions (do vs pure, partial vs total, sorry vs default)
 * are made in the lowering pass that produces the LeanAST.
 */

import type {
  LeanFile, LeanDecl, LeanExpr, LeanTy, LeanPat,
  LeanTyParam, LeanParam, LeanField, LeanCtor,
  LeanMatchArm, LeanFieldVal, SInterpPart,
} from './lean-ast.js';

// ─── Configuration ──────────────────────────────────────────────────────────────

const INDENT = '  ';

// ─── Lean keywords (for identifier sanitization) ────────────────────────────────

const LEAN_KEYWORDS = new Set([
  'def','fun','let','in','if','then','else','match','with','do','return','where',
  'have','show','from','by','class','instance','structure','inductive','namespace',
  'end','open','import','theorem','lemma','example','variable','universe','abbrev',
  'opaque','partial','mutual','private','protected','section','attribute','and','or',
  'not','true','false','Type','Prop',
  'for','while','repeat','at','try','catch','throw','macro','syntax','tactic',
  'set_option','derive','deriving','extends','override',
]);

/** Wrap a name in «» if it's a Lean keyword. Replace special chars with _. */
function sanitize(name: string): string {
  if (typeof name !== 'string') return String(name ?? '_');
  if (LEAN_KEYWORDS.has(name)) return `«${name}»`;
  return name.replace(/[^a-zA-Z0-9_.!?']/g, '_');
}

// ─── Public API ─────────────────────────────────────────────────────────────────

/** Print a complete Lean 4 file from a LeanFile AST. */
export function printFile(file: LeanFile): string {
  const lines: string[] = [];
  if (file.banner) lines.push(`-- ${file.banner}`);
  if (file.sourcePath) lines.push(`-- Source: ${file.sourcePath}`);
  if (file.banner || file.sourcePath) lines.push('');

  for (const d of file.decls) {
    printDecl(d, 0, lines);
  }

  return lines.join('\n');
}

/** Print a single declaration (useful for testing). */
export function printDeclStr(d: LeanDecl): string {
  const lines: string[] = [];
  printDecl(d, 0, lines);
  return lines.join('\n');
}

/** Print a single expression (useful for testing). */
export function printExprStr(e: LeanExpr, indent = 0): string {
  return printExpr(e, indent);
}

/** Print a type (useful for testing). */
export function printTyStr(t: LeanTy): string {
  return printTy(t);
}

// ─── Declaration printing ───────────────────────────────────────────────────────

function printDecl(d: LeanDecl, depth: number, out: string[]): void {
  const ind = INDENT.repeat(depth);

  switch (d.tag) {
    case 'Blank':
      out.push('');
      return;

    case 'Comment':
      for (const line of d.text.split('\n')) {
        out.push(`${ind}-- ${line}`);
      }
      return;

    case 'Raw':
      for (const line of d.code.split('\n')) {
        out.push(line);
      }
      return;

    case 'Import':
      out.push(`${ind}import ${d.module}`);
      return;

    case 'Open':
      out.push(`${ind}open ${d.namespaces.join(' ')}`);
      return;

    case 'Attribute':
      out.push(`${ind}attribute [${d.attr}] ${d.target}`);
      return;

    case 'Deriving':
      out.push(`${ind}deriving instance ${d.classes.join(', ')} for ${d.typeName}`);
      return;

    case 'StandaloneInstance':
      out.push(`${ind}${d.code}`);
      return;

    case 'Abbrev': {
      if (d.comment) printCommentLines(d.comment, ind, out);
      const tp = fmtTyParams(d.tyParams, false);
      out.push(`${ind}abbrev ${sanitize(d.name)}${tp} := ${printTy(d.body)}`);
      return;
    }

    case 'Structure': {
      if (d.comment) printCommentLines(d.comment, ind, out);
      const tp = fmtTyParams(d.tyParams, true);
      const ext = d.extends_ ? ` extends ${d.extends_}` : '';
      out.push(`${ind}structure ${sanitize(d.name)}${tp}${ext} where`);
      out.push(`${ind}${INDENT}mk ::`);
      for (const f of d.fields) {
        const def = f.default_ !== undefined ? ` := ${printExpr(f.default_, 0)}` : '';
        out.push(`${ind}${INDENT}${sanitize(f.name)} : ${printTy(f.ty)}${def}`);
      }
      if (d.deriving.length > 0) {
        out.push(`${ind}${INDENT}deriving ${d.deriving.join(', ')}`);
      }
      return;
    }

    case 'Inductive': {
      if (d.comment) printCommentLines(d.comment, ind, out);
      const tp = fmtTyParams(d.tyParams, true);
      out.push(`${ind}inductive ${sanitize(d.name)}${tp} where`);
      for (const c of d.ctors) {
        if (c.fields.length === 0) {
          out.push(`${ind}  | ${sanitize(c.name)}`);
        } else {
          const fs = c.fields.map(f =>
            f.name ? `(${sanitize(f.name)} : ${printTy(f.ty)})` : `(${printTy(f.ty)})`
          ).join(' ');
          out.push(`${ind}  | ${sanitize(c.name)} ${fs}`);
        }
      }
      if (d.deriving.length > 0) {
        out.push(`${ind}  deriving ${d.deriving.join(', ')}`);
      }
      return;
    }

    case 'Def': {
      if (d.docComment) {
        out.push(`${ind}/-- ${d.docComment.trim()} -/`);
      } else if (d.comment) {
        printCommentLines(d.comment, ind, out);
      }
      const kw = d.partial ? 'partial def' : 'def';
      const tp = fmtTyParamsForDef(d.tyParams);
      const ps = d.params.map(p => printParam(p)).join(' ');
      const psStr = ps ? ` ${ps}` : '';
      const retStr = printTy(d.retTy);
      // Check if body is simple enough to inline on the same line
      const bodyInline = printExprInline(d.body);
      const isSimpleBody = !bodyInline.includes('\n') && bodyInline.length < 80 &&
        d.body.tag !== 'Do' && d.body.tag !== 'If' && d.body.tag !== 'Match' &&
        d.body.tag !== 'Seq' && d.body.tag !== 'LineComment' && d.body.tag !== 'Let' &&
        d.body.tag !== 'Bind';
      if (isSimpleBody) {
        out.push(`${ind}${kw} ${sanitize(d.name)}${tp}${psStr} : ${retStr} := ${bodyInline}`);
      } else {
        out.push(`${ind}${kw} ${sanitize(d.name)}${tp}${psStr} : ${retStr} :=`);
        const bodyStr = printExpr(d.body, depth + 1);
        for (const line of bodyStr.split('\n')) {
          out.push(line);
        }
      }

      // Where clause
      if (d.where_ && d.where_.length > 0) {
        out.push(`${ind}where`);
        for (const w of d.where_) {
          printDecl(w, depth + 1, out);
        }
      }
      return;
    }

    case 'Instance': {
      const tArgs = d.args.map(t => printTy(t)).join(' ');
      out.push(`${ind}instance : ${d.typeClass} ${tArgs} where`);
      for (const m of d.methods) {
        const ps = m.params.map(p => printParam(p)).join(' ');
        const psStr = ps ? ` ${ps}` : '';
        out.push(`${ind}${INDENT}${sanitize(m.name)}${psStr} := ${printExpr(m.body, 0)}`);
      }
      return;
    }

    case 'Theorem': {
      if (d.comment) printCommentLines(d.comment, ind, out);
      out.push(`${ind}theorem ${sanitize(d.name)} : ${d.statement} := by`);
      out.push(`${ind}${INDENT}${d.proof}`);
      return;
    }

    case 'Class': {
      if (d.comment) printCommentLines(d.comment, ind, out);
      const tp = fmtTyParams(d.tyParams, false);
      out.push(`${ind}class ${sanitize(d.name)}${tp} where`);
      for (const m of d.methods) {
        out.push(`${ind}${INDENT}${sanitize(m.name)} : ${printTy(m.ty)}`);
      }
      return;
    }

    case 'Mutual':
      out.push(`${ind}mutual`);
      out.push('');
      for (const inner of d.decls) {
        printDecl(inner, depth, out);
        out.push('');
      }
      out.push(`${ind}end`);
      return;

    case 'Namespace':
      out.push(`${ind}namespace ${d.name}`);
      out.push('');
      for (const inner of d.decls) {
        printDecl(inner, depth, out);
      }
      out.push(`${ind}end ${d.name}`);
      return;

    case 'Section': {
      if (d.name) out.push(`${ind}section ${d.name}`);
      else out.push(`${ind}section`);
      out.push('');
      for (const inner of d.decls) {
        printDecl(inner, depth, out);
        out.push('');
      }
      if (d.name) out.push(`${ind}end ${d.name}`);
      else out.push(`${ind}end`);
      return;
    }
  }
}

// ─── Expression printing ────────────────────────────────────────────────────────

/**
 * Print an expression. Returns a (possibly multi-line) string.
 * Multi-line expressions use `ind` as the prefix for continuation lines.
 * The first line is indented to `depth` by the caller.
 */
function printExpr(e: LeanExpr, depth: number): string {
  const ind = INDENT.repeat(depth);

  switch (e.tag) {
    case 'Lit':
      return `${ind}${e.value}`;

    case 'Var':
      return `${ind}${sanitize(e.name)}`;

    case 'None':
      return `${ind}none`;

    case 'Default':
      if (e.ty) return `${ind}(default : ${printTy(e.ty)})`;
      return `${ind}default`;

    case 'Sorry':
      if (e.ty && e.reason) return `${ind}(sorry : ${printTy(e.ty)}) /- ${e.reason} -/`;
      if (e.ty) return `${ind}(sorry : ${printTy(e.ty)})`;
      if (e.reason) return `${ind}sorry /- ${e.reason} -/`;
      return `${ind}sorry`;

    case 'ArrayLit':
      if (e.elems.length === 0) return `${ind}#[]`;
      return `${ind}#[${e.elems.map(x => printExprInline(x)).join(', ')}]`;

    case 'ListLit':
      if (e.elems.length === 0) return `${ind}[]`;
      return `${ind}[${e.elems.map(x => printExprInline(x)).join(', ')}]`;

    case 'TupleLit':
      return `${ind}(${e.elems.map(x => printExprInline(x)).join(', ')})`;

    case 'Paren':
      return `${ind}(${printExprInline(e.inner)})`;

    case 'TypeAnnot':
      return `${ind}(${printExprInline(e.expr)} : ${printTy(e.ty)})`;

    case 'App': {
      const fn = printExprInline(e.fn);
      if (e.args.length === 0) return `${ind}${fn}`;
      const args = e.args.map(a => parenIfCompound(a));
      return `${ind}${fn} ${args.join(' ')}`;
    }

    case 'Lam': {
      const ps = e.params.length > 0 ? e.params.join(' ') : '_';
      const bodyStr = printExprInline(e.body);
      // Multi-line body: put on next line
      if (bodyStr.includes('\n')) {
        const bodyLines = printExpr(e.body, depth + 1);
        return `${ind}fun ${ps} =>\n${bodyLines}`;
      }
      return `${ind}fun ${ps} => ${bodyStr}`;
    }

    case 'Let': {
      const kw = e.rec ? 'let rec' : 'let';
      const ann = e.ty ? ` : ${printTy(e.ty)}` : '';
      const val = printExprInline(e.value);
      const body = printExpr(e.body, depth);
      return `${ind}${kw} ${sanitize(e.name)}${ann} := ${val}\n${body}`;
    }

    case 'Bind': {
      const val = printExprInline(e.value);
      const body = printExpr(e.body, depth);
      return `${ind}let ${sanitize(e.name)} ← ${val}\n${body}`;
    }

    case 'If': {
      const cond = printExprInline(e.cond);
      const thenStr = printExpr(e.then_, depth + 1);
      const elseStr = printExpr(e.else_, depth + 1);
      return `${ind}if ${cond} then\n${thenStr}\n${ind}else\n${elseStr}`;
    }

    case 'Match': {
      const scrut = printExprInline(e.scrutinee);
      const arms = e.arms.map(arm => {
        const pat = printPat(arm.pat);
        const guard = arm.guard ? ` if ${printExprInline(arm.guard)}` : '';
        const body = printExprInline(arm.body);
        return `${ind}${INDENT}| ${pat}${guard} => ${body}`;
      });
      return `${ind}match ${scrut} with\n${arms.join('\n')}`;
    }

    case 'Do': {
      const body = printExpr(e.body, depth + 1);
      return `${ind}do\n${body}`;
    }

    case 'Pure':
      return `${ind}pure ${parenIfCompound(e.value)}`;

    case 'Return':
      return `${ind}return ${parenIfCompound(e.value)}`;

    case 'Throw':
      return `${ind}throw ${parenIfCompound(e.value)}`;

    case 'TryCatch': {
      const body = parenIfCompound(e.body);
      const handler = printExprInline(e.handler);
      return `${ind}tryCatch ${body} (fun ${sanitize(e.errName)} => ${handler})`;
    }

    case 'Modify':
      return `${ind}modify ${parenIfCompound(e.fn)}`;

    case 'BinOp': {
      const l = printExprInline(e.left);
      const r = printExprInline(e.right);
      return `${ind}${l} ${e.op} ${r}`;
    }

    case 'UnOp':
      return `${ind}${e.op}${printExprInline(e.operand)}`;

    case 'FieldAccess': {
      const obj = printExprInline(e.obj);
      const field = sanitize(e.field);
      // For simple objects (Var, another FieldAccess), use dot notation: obj.field
      // For complex objects (App, Paren), use explicit call to avoid Lean parser issues
      if (e.obj.tag === 'Var' || e.obj.tag === 'FieldAccess') {
        return `${ind}${obj}.${field}`;
      }
      // Complex expression: field access on result → explicit form
      return `${ind}(${obj}).${field}`;
    }

    case 'StructLit': {
      if (e.fields.length === 0) return `${ind}{}`;
      const fs = e.fields.map(f => `${sanitize(f.name)} := ${printExprInline(f.value)}`).join(', ');
      return `${ind}{ ${fs} }`;
    }

    case 'StructUpdate': {
      const base = printExprInline(e.base);
      if (e.fields.length === 0) return `${ind}${base}`;
      const fs = e.fields.map(f => `${sanitize(f.name)} := ${printExprInline(f.value)}`).join(', ');
      // If base is sorry/default/sorryAx, emit struct literal without `with`
      if (base === 'sorry' || base === 'default' || base.includes('sorry')) {
        return `${ind}{ ${fs} }`;
      }
      return `${ind}{ ${base} with ${fs} }`;
    }

    case 'SInterp': {
      const inner = e.parts.map(p =>
        p.tag === 'Str' ? p.value : `{${printExprInline(p.expr)}}`
      ).join('');
      return `${ind}s!"${inner}"`;
    }

    case 'Seq': {
      if (e.stmts.length === 0) return `${ind}()`;
      if (e.stmts.length === 1) return printExpr(e.stmts[0], depth);
      return e.stmts.map(s => printExpr(s, depth)).join('\n');
    }

    case 'LineComment': {
      const expr = printExpr(e.expr, depth);
      return `${ind}-- ${e.text}\n${expr}`;
    }

    case 'Panic':
      return `${ind}panic! ${JSON.stringify(e.msg)}`;
  }
}

/**
 * Print an expression without leading indentation — for use inline
 * (inside function arguments, struct fields, array elements, etc.)
 */
function printExprInline(e: LeanExpr): string {
  switch (e.tag) {
    case 'Lit':         return e.value;
    case 'Var':         return sanitize(e.name);
    case 'None':        return 'none';
    case 'Default':     return e.ty ? `(default : ${printTy(e.ty)})` : 'default';
    case 'Sorry':
      if (e.ty && e.reason) return `(sorry : ${printTy(e.ty)}) /- ${e.reason} -/`;
      if (e.ty)    return `(sorry : ${printTy(e.ty)})`;
      if (e.reason) return `sorry /- ${e.reason} -/`;
      return 'sorry';
    case 'ArrayLit':
      if (e.elems.length === 0) return '#[]';
      return `#[${e.elems.map(x => printExprInline(x)).join(', ')}]`;
    case 'ListLit':
      if (e.elems.length === 0) return '[]';
      return `[${e.elems.map(x => printExprInline(x)).join(', ')}]`;
    case 'TupleLit':
      return `(${e.elems.map(x => printExprInline(x)).join(', ')})`;
    case 'Paren':
      return `(${printExprInline(e.inner)})`;
    case 'TypeAnnot':
      return `(${printExprInline(e.expr)} : ${printTy(e.ty)})`;
    case 'App': {
      const fn = printExprInline(e.fn);
      if (e.args.length === 0) return fn;
      return `${fn} ${e.args.map(a => parenIfCompound(a)).join(' ')}`;
    }
    case 'Lam': {
      const ps = e.params.length > 0 ? e.params.join(' ') : '_';
      return `fun ${ps} => ${printExprInline(e.body)}`;
    }
    case 'Let': {
      const kw = e.rec ? 'let rec' : 'let';
      const ann = e.ty ? ` : ${printTy(e.ty)}` : '';
      return `${kw} ${sanitize(e.name)}${ann} := ${printExprInline(e.value)}; ${printExprInline(e.body)}`;
    }
    case 'Bind':
      return `let ${sanitize(e.name)} ← ${printExprInline(e.value)}; ${printExprInline(e.body)}`;
    case 'If': {
      const cond = printExprInline(e.cond);
      return `if ${cond} then ${printExprInline(e.then_)} else ${printExprInline(e.else_)}`;
    }
    case 'Match': {
      // Inline matches are rare — fall back to block form
      const scrut = printExprInline(e.scrutinee);
      const arms = e.arms.map(arm => {
        const pat = printPat(arm.pat);
        const guard = arm.guard ? ` if ${printExprInline(arm.guard)}` : '';
        return `| ${pat}${guard} => ${printExprInline(arm.body)}`;
      });
      return `match ${scrut} with ${arms.join(' ')}`;
    }
    case 'Do':
      return `do ${printExprInline(e.body)}`;
    case 'Pure':
      return `pure ${parenIfCompound(e.value)}`;
    case 'Return':
      return `return ${parenIfCompound(e.value)}`;
    case 'Throw':
      return `throw ${printExprInline(e.value)}`;
    case 'TryCatch':
      return `tryCatch ${printExprInline(e.body)} (fun ${sanitize(e.errName)} => ${printExprInline(e.handler)})`;
    case 'Modify':
      return `modify ${parenIfCompound(e.fn)}`;
    case 'BinOp':
      return `${printExprInline(e.left)} ${e.op} ${printExprInline(e.right)}`;
    case 'UnOp':
      return `${e.op}${printExprInline(e.operand)}`;
    case 'FieldAccess': {
      const obj = printExprInline(e.obj);
      const field = sanitize(e.field);
      // Simple objects use dot notation directly; complex ones need parens
      if (e.obj.tag === 'Var' || e.obj.tag === 'FieldAccess' || e.obj.tag === 'Paren')
        return `${obj}.${field}`;
      return `(${obj}).${field}`;
    }
    case 'StructLit': {
      if (e.fields.length === 0) return '{}';
      const fs = e.fields.map(f => `${sanitize(f.name)} := ${printExprInline(f.value)}`).join(', ');
      return `{ ${fs} }`;
    }
    case 'StructUpdate': {
      const base = printExprInline(e.base);
      if (e.fields.length === 0) return base;
      const fs = e.fields.map(f => `${sanitize(f.name)} := ${printExprInline(f.value)}`).join(', ');
      return `{ ${base} with ${fs} }`;
    }
    case 'SInterp': {
      const inner = e.parts.map(p =>
        p.tag === 'Str' ? p.value : `{${printExprInline(p.expr)}}`
      ).join('');
      return `s!"${inner}"`;
    }
    case 'Seq': {
      if (e.stmts.length === 0) return '()';
      if (e.stmts.length === 1) return printExprInline(e.stmts[0]);
      // Multi-statement inline — wrap in do block for valid Lean syntax
      return 'do ' + e.stmts.map(s => printExprInline(s)).join('; ');
    }
    case 'LineComment':
      return printExprInline(e.expr);
    case 'Panic':
      return `panic! ${JSON.stringify(e.msg)}`;
  }
}

// ─── Type printing ──────────────────────────────────────────────────────────────

function printTy(t: LeanTy): string {
  switch (t.tag) {
    case 'TyName':
      return t.name;
    case 'TyApp': {
      const fn = printTy(t.fn);
      const args = t.args.map(a => printTyAtom(a));
      return `${fn} ${args.join(' ')}`;
    }
    case 'TyArrow': {
      const parts = [...t.params.map(p => printTyAtom(p)), printTy(t.ret)];
      return parts.join(' → ');
    }
    case 'TyTuple': {
      if (t.elems.length === 0) return 'Unit';
      if (t.elems.length === 1) return printTy(t.elems[0]);
      return '(' + t.elems.map(e => printTy(e)).join(' × ') + ')';
    }
    case 'TyParen':
      return `(${printTy(t.inner)})`;
  }
}

/** Print a type as an "atom" — parenthesized if it contains spaces. */
function printTyAtom(t: LeanTy): string {
  const s = printTy(t);
  if (t.tag === 'TyArrow' || t.tag === 'TyTuple' || (t.tag === 'TyApp' && t.args.length > 0)) {
    return `(${s})`;
  }
  return s;
}

/** Wrap an inline expression in parens if it's compound (lambda, if, match, let, bind). */
function parenIfCompound(e: LeanExpr): string {
  const s = printExprInline(e);
  switch (e.tag) {
    case 'Lam': case 'If': case 'Match': case 'Let': case 'Bind':
    case 'BinOp': case 'Do': case 'Seq': case 'App':
      return `(${s})`;
    default:
      return s;
  }
}

// ─── Pattern printing ───────────────────────────────────────────────────────────

function printPat(p: LeanPat): string {
  switch (p.tag) {
    case 'PVar':   return sanitize(p.name);
    case 'PWild':  return '_';
    case 'PLit':   return p.value;
    case 'PNone':  return '.none';
    case 'PSome':  return `.some ${printPat(p.inner)}`;
    case 'PCtor': {
      const args = p.args.map(a => printPat(a));
      return args.length === 0 ? `.${sanitize(p.name)}` : `.${sanitize(p.name)} ${args.join(' ')}`;
    }
    case 'PTuple':
      return `(${p.elems.map(x => printPat(x)).join(', ')})`;
    case 'PStruct':
      return `{ ${p.fields.map(f => `${sanitize(f.name)} := ${printPat(f.pat)}`).join(', ')} }`;
    case 'POr':
      return p.pats.map(x => printPat(x)).join(' | ');
    case 'PAs':
      return `${printPat(p.pattern)} as ${sanitize(p.name)}`;
  }
}

// ─── Helpers ────────────────────────────────────────────────────────────────────

function printParam(p: LeanParam): string {
  const ty = printTy(p.ty);
  const name = sanitize(p.name);
  if (p.implicit) return `{${name} : ${ty}}`;
  if (p.default_) return `(${name} : ${ty} := ${printExprInline(p.default_)})`;
  return `(${name} : ${ty})`;
}

/**
 * Format type parameters for structures/inductives (explicit: (T : Type))
 * or for class/abbrev (implicit: {T : Type}).
 */
function fmtTyParams(params: LeanTyParam[], explicit: boolean): string {
  if (params.length === 0) return '';
  return ' ' + params.map(p => {
    const wrap = explicit ? ['(', ')'] : ['{', '}'];
    return `${wrap[0]}${p.name} : Type${wrap[1]}`;
  }).join(' ');
}

/**
 * Format type parameters for def declarations — implicit by default,
 * with optional constraints.
 */
function fmtTyParamsForDef(params: LeanTyParam[]): string {
  if (params.length === 0) return '';
  return ' ' + params.map(p => {
    let s = `{${p.name} : Type}`;
    if (p.constraints) {
      for (const c of p.constraints) {
        s += ` [${c} ${p.name}]`;
      }
    }
    return s;
  }).join(' ');
}

function printCommentLines(text: string, ind: string, out: string[]): void {
  for (const line of text.split('\n')) {
    const stripped = line.replace(/^\/\*+\s*/, '').replace(/\*+\/$/, '').replace(/^\s*\*\s?/, '').trim();
    if (!stripped) continue;
    if (stripped.startsWith('@')) continue;
    out.push(`${ind}-- ${stripped}`);
  }
}
