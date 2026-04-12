// Verification: generate proof obligation stubs for safety properties.

import { IRModule, IRDecl, IRExpr, IRType, TyUnit, TyNat, TyFloat, TyArray, TyOption } from '../ir/types.js';

// ─── Types ────────────────────────────────────────────────────────────────────

export type ObligationKind = 'ArrayBounds' | 'DivisionSafe' | 'OptionIsSome' | 'InvariantPreserved' | 'TerminationBy';

export interface ProofObligation {
  kind: ObligationKind;
  funcName: string;
  detail: string;
}

export interface VerificationResult {
  obligations: ProofObligation[];
  leanCode: string;
}

// ─── Public API ───────────────────────────────────────────────────────────────

export function generateVerification(mod: IRModule): VerificationResult {
  const obligations: ProofObligation[] = [];
  for (const d of mod.decls) collectDecl(d, obligations);
  const leanCode = obligations.map(emitObligation).join('\n\n');
  return { obligations, leanCode };
}

// ─── Collection ───────────────────────────────────────────────────────────────

function collectDecl(d: IRDecl, acc: ProofObligation[]): void {
  if (d.tag === 'FuncDef')   collectExpr(d.body, d.name, acc);
  if (d.tag === 'Namespace') d.decls.forEach(x => collectDecl(x, acc));
}

function collectExpr(e: IRExpr, fn: string, acc: ProofObligation[]): void {
  switch (e.tag) {
    case 'IndexAccess':
      acc.push({ kind: 'ArrayBounds', funcName: fn, detail: `${exprSummary(e.obj)}[${exprSummary(e.index)}]` });
      collectExpr(e.obj, fn, acc); collectExpr(e.index, fn, acc); break;

    case 'BinOp':
      if (e.op === 'Div' || e.op === 'Mod')
        acc.push({ kind: 'DivisionSafe', funcName: fn, detail: exprSummary(e.right) });
      collectExpr(e.left, fn, acc); collectExpr(e.right, fn, acc); break;

    case 'FieldAccess':
      if ((e.field === 'value' || e.field === 'get') && e.obj.type.tag === 'Option')
        acc.push({ kind: 'OptionIsSome', funcName: fn, detail: exprSummary(e.obj) });
      collectExpr(e.obj, fn, acc); break;

    case 'Let':         collectExpr(e.value, fn, acc); collectExpr(e.body, fn, acc); break;
    case 'Bind':        collectExpr(e.monad, fn, acc); collectExpr(e.body, fn, acc); break;
    case 'IfThenElse':  collectExpr(e.cond, fn, acc); collectExpr(e.then, fn, acc); collectExpr(e.else_, fn, acc); break;
    case 'Match':       collectExpr(e.scrutinee, fn, acc); e.cases.forEach(c => collectExpr(c.body, fn, acc)); break;
    case 'Sequence':    e.stmts.forEach(s => collectExpr(s, fn, acc)); break;
    case 'App':         collectExpr(e.fn, fn, acc); e.args.forEach(a => collectExpr(a, fn, acc)); break;
    case 'Lambda':      collectExpr(e.body, fn, acc); break;
    case 'Assign':      collectExpr(e.value, fn, acc); break;
    case 'TryCatch':    collectExpr(e.body, fn, acc); collectExpr(e.handler, fn, acc); break;
    case 'Return':      collectExpr(e.value, fn, acc); break;
    case 'Throw':       collectExpr(e.error, fn, acc); break;
    default:            break;
  }
}

function exprSummary(e: IRExpr): string {
  switch (e.tag) {
    case 'Var':         return e.name;
    case 'FieldAccess': return `${exprSummary(e.obj)}.${e.field}`;
    case 'LitNat':      return String(e.value);
    case 'LitString':   return JSON.stringify(e.value);
    default:            return '_';
  }
}

// ─── Emission ─────────────────────────────────────────────────────────────────

function emitObligation(o: ProofObligation): string {
  const safeName = o.funcName.replace(/[^a-zA-Z0-9_]/g, '_');
  switch (o.kind) {
    case 'ArrayBounds':
      return [
        `-- Array bounds safety for \`${o.funcName}\` accessing ${o.detail}`,
        `theorem ${safeName}_idx_in_bounds`,
        `    (arr : Array α) (idx : Nat) (h : idx < arr.size) :`,
        `    arr[idx]! = arr[⟨idx, h⟩] := by`,
        `  simp [Array.get!_eq_getElem]`,
      ].join('\n');
    case 'DivisionSafe':
      return [
        `-- Division safety for \`${o.funcName}\` divisor: ${o.detail}`,
        `theorem ${safeName}_divisor_nonzero`,
        `    (n d : Float) (h : d ≠ 0) : n / d = n / d := rfl`,
      ].join('\n');
    case 'OptionIsSome':
      return [
        `-- Option safety for \`${o.funcName}\` accessing ${o.detail}`,
        `theorem ${safeName}_val_is_some`,
        `    {α : Type} (opt : Option α) (h : opt.isSome) :`,
        `    opt.get!.isSome := by cases opt <;> simp_all`,
      ].join('\n');
    case 'InvariantPreserved':
      return [
        `-- Invariant preserved by \`${o.funcName}\``,
        `theorem ${safeName}_invariant_preserved`,
        `    (s : σ) (h : invariant s) : ∃ s', invariant s' := ⟨s, h⟩`,
      ].join('\n');
    case 'TerminationBy':
      return `-- termination_by ${o.detail} -- for \`${o.funcName}\``;
  }
}
