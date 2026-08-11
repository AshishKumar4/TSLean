/**
 * @module codegen/degradation
 *
 * Degradation scan: which placeholders does the emitted artifact contain?
 *
 * The lowering tracker records *why* a degradation happened, but only at the
 * few sites that remember to call it — it cannot answer whether the output is
 * degraded. This module answers that question from the LeanAST the printer is
 * about to render: the printer is structural, so the AST is the artifact.
 *
 * Two placeholder forms are reported: `sorry` (an axiom — blocks proofs) and
 * `default` (an Inhabited value standing in for one the lowerer could not
 * produce). Comments and string literals are never reported, so a source
 * program mentioning "sorry" cannot fake a finding.
 *
 * Pipeline position:  IR → Rewrite → Lower → **Scan** / Print → Lean 4 source
 */

import type { LeanDecl, LeanExpr, LeanFile, LeanParam } from './lean-ast.js';
import type { DegradationLevel } from '../sorry-tracker.js';

/** One placeholder in the emitted artifact. */
export interface DegradationMarker {
  level: DegradationLevel;
  /** Declaration carrying the marker, e.g. `def area` or `structure IRExpr.type`. */
  site: string;
}

/** Every `sorry`/`default` placeholder the printed file will contain. */
export function scanDegradation(file: LeanFile): DegradationMarker[] {
  const markers: DegradationMarker[] = [];
  for (const d of file.decls) scanDecl(d, markers);
  return markers;
}

/** Count the markers of one level. */
export function countLevel(markers: readonly DegradationMarker[], level: DegradationLevel): number {
  return markers.filter(m => m.level === level).length;
}

/** Human-readable counts, e.g. `2 default placeholder(s), 1 sorry axiom(s)`. */
export function describeDegradation(markers: readonly DegradationMarker[]): string {
  const sorrys = countLevel(markers, 'sorry');
  const defaults = markers.length - sorrys;
  const parts: string[] = [];
  if (defaults > 0) parts.push(`${defaults} default placeholder(s)`);
  if (sorrys > 0) parts.push(`${sorrys} sorry axiom(s)`);
  return parts.join(', ');
}

/** One line per distinct site, most-degraded first, capped at `limit`. */
export function degradationSites(markers: readonly DegradationMarker[], limit = 10): string[] {
  const counts = new Map<string, number>();
  for (const m of markers) {
    const key = `${m.level} at ${m.site}`;
    counts.set(key, (counts.get(key) ?? 0) + 1);
  }
  const sorted = [...counts].sort((a, b) => b[1] - a[1]);
  const lines = sorted.slice(0, limit).map(([key, n]) => (n > 1 ? `${key} (×${n})` : key));
  if (sorted.length > limit) lines.push(`… and ${sorted.length - limit} more site(s)`);
  return lines;
}

// ─── Declarations ───────────────────────────────────────────────────────────────

function scanDecl(d: LeanDecl, out: DegradationMarker[]): void {
  switch (d.tag) {
    case 'Def': {
      const site = `def ${d.name}`;
      for (const p of d.params) scanParam(p, site, out);
      scanExpr(d.body, site, out);
      for (const w of d.where_ ?? []) scanDecl(w, out);
      return;
    }

    case 'Structure':
      for (const f of d.fields) {
        if (f.default_) scanExpr(f.default_, `structure ${d.name}.${f.name}`, out);
      }
      return;

    case 'Instance': {
      const site = `instance ${d.typeClass}`;
      for (const m of d.methods) {
        for (const p of m.params) scanParam(p, site, out);
        scanExpr(m.body, site, out);
      }
      return;
    }

    case 'Theorem':
      scanSource(d.statement, `theorem ${d.name}`, out);
      scanSource(d.proof, `theorem ${d.name}`, out);
      return;

    // Escape hatches: text that never passed through the AST.
    case 'Raw':
    case 'StandaloneInstance':
      scanSource(d.code, firstLine(d.code), out);
      return;

    case 'Mutual':
    case 'Namespace':
    case 'Section':
      for (const inner of d.decls) scanDecl(inner, out);
      return;

    // No expression or code payload.
    case 'Inductive':
    case 'Abbrev':
    case 'Class':
    case 'Import':
    case 'Open':
    case 'Attribute':
    case 'Deriving':
    case 'Comment':
    case 'Blank':
      return;
  }
  unhandled(d);
}

function scanParam(p: LeanParam, site: string, out: DegradationMarker[]): void {
  if (p.default_) scanExpr(p.default_, site, out);
}

// ─── Expressions ────────────────────────────────────────────────────────────────

function scanExpr(e: LeanExpr, site: string, out: DegradationMarker[]): void {
  switch (e.tag) {
    case 'Default':
      out.push({ level: 'default', site });
      return;

    case 'Sorry':
      out.push({ level: 'sorry', site });
      return;

    // Leaves. `Lit`, `SInterp` text and `Panic` messages are quoted, not code.
    case 'Lit':
    case 'Var':
    case 'None':
    case 'Panic':
      return;

    case 'ArrayLit':
    case 'ListLit':
    case 'TupleLit':
      for (const x of e.elems) scanExpr(x, site, out);
      return;

    case 'Seq':
      for (const s of e.stmts) scanExpr(s, site, out);
      return;

    case 'App':
      scanExpr(e.fn, site, out);
      for (const a of e.args) scanExpr(a, site, out);
      return;

    case 'Paren':
      scanExpr(e.inner, site, out);
      return;

    case 'Lam':
    case 'Do':
      scanExpr(e.body, site, out);
      return;

    case 'Let':
    case 'Bind':
      scanExpr(e.value, site, out);
      scanExpr(e.body, site, out);
      return;

    case 'If':
      scanExpr(e.cond, site, out);
      scanExpr(e.then_, site, out);
      scanExpr(e.else_, site, out);
      return;

    case 'Match':
      scanExpr(e.scrutinee, site, out);
      for (const arm of e.arms) {
        if (arm.guard) scanExpr(arm.guard, site, out);
        scanExpr(arm.body, site, out);
      }
      return;

    case 'Pure':
    case 'Return':
    case 'Throw':
      scanExpr(e.value, site, out);
      return;

    case 'TryCatch':
      scanExpr(e.body, site, out);
      scanExpr(e.handler, site, out);
      return;

    case 'Modify':
      scanExpr(e.fn, site, out);
      return;

    case 'BinOp':
      scanExpr(e.left, site, out);
      scanExpr(e.right, site, out);
      return;

    case 'UnOp':
      scanExpr(e.operand, site, out);
      return;

    case 'FieldAccess':
      scanExpr(e.obj, site, out);
      return;

    case 'StructLit':
      for (const f of e.fields) scanExpr(f.value, site, out);
      return;

    case 'StructUpdate':
      scanExpr(e.base, site, out);
      for (const f of e.fields) scanExpr(f.value, site, out);
      return;

    case 'SInterp':
      for (const part of e.parts) {
        if (part.tag === 'Expr') scanExpr(part.expr, site, out);
      }
      return;

    case 'TypeAnnot':
      scanExpr(e.expr, site, out);
      return;

    case 'LineComment':
      scanExpr(e.expr, site, out);
      return;
  }
  unhandled(e);
}

// ─── Raw Lean text ──────────────────────────────────────────────────────────────

/** Identifier characters, so `Inhabited.default` and `sorryish` are single tokens. */
const IDENTIFIER = /[A-Za-z0-9_.'!?]/;

/**
 * Report placeholder tokens in raw Lean text.
 *
 * `Raw`, `StandaloneInstance` and `Theorem` carry source the AST never saw, so
 * their markers have to be found in the text — that is how `⟨sorry⟩` reaches
 * the output. Line comments, block comments (nested) and string literals are
 * skipped, so only code positions are reported. An interpolation inside a
 * string is skipped with the string.
 */
function scanSource(code: string, site: string, out: DegradationMarker[]): void {
  let i = 0;
  let blockComment = 0;

  while (i < code.length) {
    const pair = code.substring(i, i + 2);

    if (pair === '/-') { blockComment++; i += 2; continue; }
    if (blockComment > 0) {
      if (pair === '-/') { blockComment--; i += 2; } else { i++; }
      continue;
    }
    if (pair === '--') {
      const newline = code.indexOf('\n', i);
      i = newline < 0 ? code.length : newline + 1;
      continue;
    }
    if (code[i] === '"') { i = endOfString(code, i); continue; }

    if (IDENTIFIER.test(code[i])) {
      const start = i;
      while (i < code.length && IDENTIFIER.test(code[i])) i++;
      const level = tokenLevel(code.slice(start, i));
      if (level) out.push({ level, site });
      continue;
    }
    i++;
  }
}

/** Index just past the string literal opening at `quote`. */
function endOfString(code: string, quote: number): number {
  for (let i = quote + 1; i < code.length; i++) {
    if (code[i] === '\\') { i++; continue; }
    if (code[i] === '"') return i + 1;
  }
  return code.length;
}

function tokenLevel(token: string): DegradationLevel | null {
  if (token === 'sorry' || token === 'sorryAx') return 'sorry';
  if (token === 'default') return 'default';
  return null;
}

// ─── Helpers ────────────────────────────────────────────────────────────────────

const SITE_WIDTH = 72;

function firstLine(code: string): string {
  const line = code.split('\n').find(l => l.trim().length > 0)?.trim() ?? 'raw Lean';
  return line.length > SITE_WIDTH ? `${line.slice(0, SITE_WIDTH - 1)}…` : line;
}

/** Compile-time exhaustiveness guard: a new AST node has to be handled above. */
function unhandled(node: never): never {
  throw new Error(`degradation scan: unhandled Lean AST node ${JSON.stringify(node)}`);
}
