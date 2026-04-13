// Veil transition system stub generator.
// Given a transpiled DO module, generates a Lean file with:
//   - State type alias
//   - initState, assumptions predicates
//   - Per-method action relations (veil_relation)
//   - next = nextN combinator
//   - safety/invariant stubs (sorry)
//   - Proof obligation theorems (sorry)

import { IRModule, IRDecl, IRExpr, IRType, IRParam, Effect } from '../ir/types.js';

export interface VeilResult {
  leanCode: string;
  actions: string[];
  stateType: string;
}

/**
 * Generate a Veil transition system stub for a DO class.
 * @param mod       - The parsed+rewritten IR module
 * @param doName    - The Durable Object class name (e.g., "Counter")
 * @param leanModule - The Lean module path for the transpiled code
 */
export function generateVeilStub(mod: IRModule, doName: string, leanModule: string): VeilResult | null {
  const stateType = `${doName}State`;
  const ns = findNamespace(mod, doName);
  if (!ns) return null;

  const methods = extractPublicMethods(ns);
  if (methods.length === 0) return null;

  const actions = methods.map(m => `action_${m.name}`);
  const n = actions.length;
  const nextCombinator = n <= 5 ? `next${n}` : null;

  const lines: string[] = [];
  lines.push(`-- Auto-generated Veil transition system for ${doName}`);
  lines.push(`-- Fill in sorry placeholders to complete verification.`);
  lines.push('');
  lines.push('import TSLean.Veil.DSL');
  lines.push('import TSLean.Veil.Core');
  lines.push(`import ${leanModule}`);
  lines.push('');
  lines.push('open TSLean.Veil TransitionSystem TSLean.Veil.DSL');
  lines.push('');
  lines.push(`namespace ${doName}.Veil`);
  lines.push('');

  // State alias
  lines.push(`-- Reuse the transpiled state type`);
  lines.push(`abbrev State := ${stateType}`);
  lines.push('');

  // Init predicate
  lines.push('-- Initial state predicate (extracted from constructor/blockConcurrencyWhile)');
  const initFields = extractInitFields(ns, stateType);
  if (initFields.length > 0) {
    lines.push(`def initState (s : State) : Prop :=`);
    lines.push(`  ${initFields.join(' ∧\n  ')}`);
  } else {
    lines.push('def initState (s : State) : Prop :=');
    lines.push('  sorry -- TODO: specify initial state');
  }
  lines.push('');

  // Assumptions
  lines.push('-- Environment assumptions (constraints on reachable states)');
  lines.push('def assumptions (_ : State) : Prop := True');
  lines.push('');

  // Per-method actions
  for (const m of methods) {
    const actionName = `action_${m.name}`;
    lines.push(`-- Action: ${doName}.${m.name}`);
    const body = inferActionBody(m);
    lines.push(`veil_relation ${actionName} (pre post : State) where`);
    lines.push(`  ${body}`);
    lines.push('');
  }

  // Next relation
  if (nextCombinator && n > 0) {
    lines.push(`-- Transition relation: disjunction of all actions`);
    lines.push(`def next_ := ${nextCombinator} ${actions.join(' ')}`);
  } else if (n > 0) {
    lines.push('-- Transition relation (>5 actions, manual disjunction)');
    lines.push('def next_ (pre post : State) : Prop :=');
    lines.push(`  ${actions.map(a => `${a} pre post`).join(' ∨\n  ')}`);
  }
  lines.push('');

  // Safety property
  lines.push('-- Safety property to verify');
  lines.push('veil_safety safe (s : State) where');
  lines.push('  sorry -- TODO: specify safety property');
  lines.push('');

  // Invariant
  lines.push('-- Inductive invariant (must imply safe)');
  lines.push('def inv (s : State) : Prop :=');
  lines.push('  sorry -- TODO: specify invariant');
  lines.push('');

  // TransitionSystem instance
  lines.push('instance : TransitionSystem State where');
  lines.push('  init := initState');
  lines.push('  assumptions := assumptions');
  lines.push('  next := next_');
  lines.push('  safe := safe');
  lines.push('  inv := inv');
  lines.push('');

  // Proof obligations
  lines.push('-- ═══ Proof obligations ═══');
  lines.push('');
  lines.push('theorem inv_implies_safe : invSafe (σ := State) :=');
  lines.push('  sorry -- Prove: inv s → assumptions s → safe s');
  lines.push('');
  lines.push('theorem init_establishes_inv : invInit (σ := State) :=');
  lines.push('  sorry -- Prove: assumptions s → init s → inv s');
  lines.push('');

  // Per-action preservation
  for (const m of methods) {
    const actionName = `action_${m.name}`;
    lines.push(`theorem ${m.name}_preserves_inv (pre post : State)`);
    lines.push(`    (ha : assumptions pre) (hi : inv pre)`);
    lines.push(`    (h : ${actionName} pre post) : inv post :=`);
    lines.push('  sorry');
    lines.push('');
  }

  // Consecution
  if (nextCombinator && n > 0) {
    lines.push('theorem inv_consecution : invConsecution (σ := State) :=');
    lines.push('  sorry -- Use ' + nextCombinator + '_preserves with per-action theorems');
  } else {
    lines.push('theorem inv_consecution : invConsecution (σ := State) :=');
    lines.push('  sorry');
  }
  lines.push('');

  // Main safety theorem
  lines.push('-- Main safety theorem');
  lines.push('theorem safety_holds : isInvariant (σ := State) safe :=');
  lines.push('  sorry -- Use safety_of_inv_inductive');
  lines.push('');

  lines.push(`end ${doName}.Veil`);

  return {
    leanCode: lines.join('\n'),
    actions,
    stateType,
  };
}

// ─── Helpers ──────────────────────────────────────────────────────────────────

function findNamespace(mod: IRModule, name: string): Extract<IRDecl, { tag: 'Namespace' }> | null {
  for (const d of mod.decls) {
    if (d.tag === 'Namespace' && d.name === name)
      return d as Extract<IRDecl, { tag: 'Namespace' }>;
  }
  return null;
}

interface MethodInfo {
  name: string;
  params: IRParam[];
  effect: Effect;
  body: IRExpr;
}

function extractPublicMethods(ns: Extract<IRDecl, { tag: 'Namespace' }>): MethodInfo[] {
  const methods: MethodInfo[] = [];
  for (const d of ns.decls) {
    if (d.tag === 'FuncDef') {
      const shortName = d.name.includes('.') ? d.name.split('.').pop()! : d.name;
      // Skip init (constructor) and private methods
      if (shortName === 'init' || shortName.startsWith('_')) continue;
      methods.push({
        name: shortName,
        params: d.params,
        effect: d.effect,
        body: d.body,
      });
    }
  }
  return methods;
}

function extractInitFields(ns: Extract<IRDecl, { tag: 'Namespace' }>, stateType: string): string[] {
  for (const d of ns.decls) {
    if (d.tag === 'FuncDef' && d.name.endsWith('.init')) {
      return extractFieldAssignments(d.body);
    }
  }
  return [];
}

function extractFieldAssignments(expr: IRExpr): string[] {
  if (expr.tag === 'StructLit') {
    return expr.fields
      .filter(f => f.name !== '_base')
      .map(f => {
        const val = exprToLeanLiteral(f.value);
        return val ? `s.${f.name} = ${val}` : `True`;
      })
      .filter(s => s !== 'True');
  }
  return [];
}

function exprToLeanLiteral(e: IRExpr): string | null {
  switch (e.tag) {
    case 'LitNat': return String(e.value);
    case 'LitInt': return String(e.value);
    case 'LitFloat': return String(e.value);
    case 'LitString': return JSON.stringify(e.value);
    case 'LitBool': return e.value ? 'true' : 'false';
    case 'LitUnit': return '()';
    case 'ArrayLit': return '#[]';
    case 'Hole': return null;
    default: return null;
  }
}

function inferActionBody(m: MethodInfo): string {
  // For simple methods, try to infer the relational predicate.
  // For complex methods, emit sorry.
  const assignments = collectStateAssignments(m.body);
  if (assignments.length > 0) {
    const parts = assignments.map(a => `post.${a.field} = ${a.expr}`);
    // Preserve unchanged fields
    return parts.join(' ∧\n  ') + ' -- TODO: add frame conditions for unchanged fields';
  }
  return `sorry -- TODO: specify pre/post for ${m.name}`;
}

interface StateAssignment { field: string; expr: string }

function collectStateAssignments(e: IRExpr): StateAssignment[] {
  const out: StateAssignment[] = [];
  walkExpr(e, node => {
    if (node.tag === 'Assign' && node.target.tag === 'FieldAccess' &&
        node.target.obj.tag === 'Var' && node.target.obj.name === 'self') {
      const field = node.target.field;
      const val = exprToLeanLiteral(node.value);
      if (val) out.push({ field, expr: val });
      else out.push({ field, expr: 'sorry' });
    }
  });
  return out;
}

function walkExpr(e: IRExpr, cb: (e: IRExpr) => void): void {
  if (!e) return;
  cb(e);
  switch (e.tag) {
    case 'Let': walkExpr(e.value, cb); walkExpr(e.body, cb); break;
    case 'Bind': walkExpr(e.monad, cb); walkExpr(e.body, cb); break;
    case 'App': walkExpr(e.fn, cb); e.args.forEach(a => walkExpr(a, cb)); break;
    case 'Lambda': walkExpr(e.body, cb); break;
    case 'IfThenElse': walkExpr(e.cond, cb); walkExpr(e.then, cb); walkExpr(e.else_, cb); break;
    case 'Match': walkExpr(e.scrutinee, cb); e.cases.forEach(c => walkExpr(c.body, cb)); break;
    case 'Sequence': e.stmts.forEach(s => walkExpr(s, cb)); break;
    case 'Assign': walkExpr(e.value, cb); break;
    case 'Return': walkExpr(e.value, cb); break;
    case 'TryCatch': walkExpr(e.body, cb); walkExpr(e.handler, cb); break;
    case 'BinOp': walkExpr(e.left, cb); walkExpr(e.right, cb); break;
    case 'FieldAccess': walkExpr(e.obj, cb); break;
    case 'StructLit': e.fields.forEach(f => walkExpr(f.value, cb)); break;
  }
}
