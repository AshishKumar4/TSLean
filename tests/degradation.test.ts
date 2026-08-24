// Output-based strictness: what the emitted artifact carries, not what the
// lowerer happened to record.

import * as fs from 'node:fs';
import * as os from 'node:os';
import * as path from 'node:path';
import { afterEach, describe, expect, it } from 'vitest';
import {
  degradationSites,
  describeDegradation,
  scanDegradation,
  type DegradationMarker,
} from '../src/codegen/degradation.js';
import type { LeanDecl, LeanExpr, LeanFile } from '../src/codegen/lean-ast.js';
import { generateLeanTracked } from '../src/codegen/index.js';
import { parseFile } from '../src/parser/index.js';
import { rewriteModule } from '../src/rewrite/index.js';
import { spawnCli } from './helpers/run-cli.js';

const ROOT = process.cwd();
const FIX = path.join(ROOT, 'tests/fixtures');

const Unit: LeanExpr = { tag: 'Lit', value: '()' };

function file(...decls: LeanDecl[]): LeanFile {
  return { decls };
}

function def(name: string, body: LeanExpr): Extract<LeanDecl, { tag: 'Def' }> {
  return {
    tag: 'Def',
    partial: false,
    name,
    tyParams: [],
    params: [],
    retTy: { tag: 'TyName', name: 'Unit' },
    body,
  };
}

function scanned(...decls: LeanDecl[]): DegradationMarker[] {
  return scanDegradation(file(...decls));
}

function markersFor(source: string): DegradationMarker[] {
  return generateLeanTracked(rewriteModule(parseFile({ fileName: 'test.ts', sourceText: source }))).degradations;
}

const MUTUAL_INTERFACES = `
export interface Node1 { name: string; child: Node2 }
export interface Node2 { value: number; parent: Node1 }
`;

const temporary: string[] = [];
afterEach(() => {
  for (const p of temporary) fs.rmSync(p, { recursive: true, force: true });
  temporary.length = 0;
});

function tmpDir(prefix: string): string {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), prefix));
  temporary.push(dir);
  return dir;
}

// ─── Scanning the AST ─────────────────────────────────────────────────────────

describe('degradation scan: AST placeholders', () => {
  it('reports a sorry in a definition body', () => {
    expect(scanned(def('f', { tag: 'Sorry' }))).toEqual([{ level: 'sorry', site: 'def f' }]);
  });

  it('reports a default in a definition body', () => {
    expect(scanned(def('f', { tag: 'Default' }))).toEqual([{ level: 'default', site: 'def f' }]);
  });

  it('reports placeholders nested in expressions', () => {
    const body: LeanExpr = {
      tag: 'App',
      fn: { tag: 'Var', name: 'g' },
      args: [{ tag: 'Default' }, { tag: 'Paren', inner: { tag: 'Sorry' } }],
    };
    expect(scanned(def('f', body)).map((m) => m.level)).toEqual(['default', 'sorry']);
  });

  it('reports a structure field default against the field', () => {
    expect(
      scanned({
        tag: 'Structure',
        name: 'IRExpr',
        tyParams: [],
        deriving: [],
        fields: [{ name: 'type', ty: { tag: 'TyName', name: 'IRType' }, default_: { tag: 'Default' } }],
      }),
    ).toEqual([{ level: 'default', site: 'structure IRExpr.type' }]);
  });

  it('reports placeholders inside namespaces, mutual blocks and where clauses', () => {
    const helper: LeanDecl = def('helper', { tag: 'Sorry' });
    const outer: LeanDecl = {
      ...def('outer', Unit),
      where_: [helper],
    };
    const markers = scanned({
      tag: 'Namespace',
      name: 'N',
      decls: [{ tag: 'Mutual', decls: [def('a', { tag: 'Default' })] }, outer],
    });
    expect(markers).toEqual([
      { level: 'default', site: 'def a' },
      { level: 'sorry', site: 'def helper' },
    ]);
  });

  it('reports the sorry that mutual interfaces smuggle through a standalone instance', () => {
    expect(
      scanned({
        tag: 'StandaloneInstance',
        code: 'instance : Inhabited Node1 := ⟨sorry⟩',
      }),
    ).toEqual([{ level: 'sorry', site: 'instance : Inhabited Node1 := ⟨sorry⟩' }]);
  });

  it('reports raw Lean and unproven theorems', () => {
    expect(scanned({ tag: 'Raw', code: 'def x : Nat := default' }).map((m) => m.level)).toEqual(['default']);
    expect(
      scanned({
        tag: 'Theorem',
        name: 't',
        statement: 'True',
        proof: 'sorry',
      }),
    ).toEqual([{ level: 'sorry', site: 'theorem t' }]);
  });
});

describe('degradation scan: no false positives', () => {
  it('ignores string literals, interpolations and panics', () => {
    expect(scanned(def('f', { tag: 'Lit', value: '"sorry"' }))).toEqual([]);
    expect(
      scanned(
        def('f', {
          tag: 'SInterp',
          parts: [
            { tag: 'Str', value: 'default' },
            { tag: 'Expr', expr: { tag: 'Var', name: 'x' } },
          ],
        }),
      ),
    ).toEqual([]);
    expect(scanned(def('f', { tag: 'Panic', msg: 'sorry: default' }))).toEqual([]);
  });

  it('ignores comments, doc comments and the reason attached to a sorry', () => {
    expect(scanned({ tag: 'Comment', text: 'sorry, no default here' })).toEqual([]);
    expect(scanned({ ...def('f', Unit), docComment: 'returns a default', comment: 'sorry' })).toEqual([]);
    expect(scanned(def('f', { tag: 'LineComment', text: 'default', expr: Unit }))).toEqual([]);
  });

  it('ignores markers inside raw Lean comments and strings', () => {
    expect(scanned({ tag: 'Raw', code: '-- sorry, uses default\ndef x : String := "sorry default"' })).toEqual([]);
    expect(scanned({ tag: 'Raw', code: '/- sorry /- default -/ still commented -/\ndef x : Nat := 0' })).toEqual([]);
  });

  it('ignores identifiers that merely contain a marker', () => {
    expect(scanned({ tag: 'Raw', code: 'def f := Inhabited.default sorryish defaultValue' })).toEqual([]);
  });
});

describe('degradation scan: reporting', () => {
  const markers: readonly DegradationMarker[] = [
    { level: 'default', site: 'def a' },
    { level: 'default', site: 'def a' },
    { level: 'sorry', site: 'def b' },
  ];

  it('counts each level', () => {
    expect(describeDegradation(markers)).toBe('2 default placeholder(s), 1 sorry axiom(s)');
    expect(describeDegradation([])).toBe('');
  });

  it('groups sites and caps the list', () => {
    expect(degradationSites(markers)).toEqual(['default at def a (×2)', 'sorry at def b']);
    expect(degradationSites(markers, 1)).toEqual(['default at def a (×2)', '… and 1 more site(s)']);
  });
});

// ─── Scanning real output ─────────────────────────────────────────────────────

describe('degradation scan: transpiler output', () => {
  it('finds the untracked sorry emitted for mutually recursive interfaces', () => {
    const markers = markersFor(MUTUAL_INTERFACES);
    expect(markers.filter((m) => m.level === 'sorry')).toHaveLength(2);
    expect(markers.map((m) => m.site)).toContain('instance : Inhabited Node1 := ⟨sorry⟩');
  });

  it('finds the defaults an anonymous object parameter leaves behind', () => {
    const source = fs.readFileSync(path.join(FIX, 'advanced/anonymous-object.ts'), 'utf8');
    expect(markersFor(source).every((m) => m.level === 'default')).toBe(true);
    expect(markersFor(source).length).toBeGreaterThan(0);
  });

  it('reports nothing for output that carries no placeholder', () => {
    expect(markersFor('export function add(a: number, b: number): number { return a + b; }')).toEqual([]);
  });

  it('degrades visibly for a carrier reached through a struct field', () => {
    // `DurableObjectNamespace` is an opaque stub with no `Inhabited` instance, so neither `Rooms`
    // nor the `Registry` that holds one has a value to stand in for. Both the derive clause and the
    // placeholder used to look at the struct's own fields only: `Registry` got `deriving Inhabited`
    // and `(default : Registry)`, which Lean rejects, and the scan reported the weaker marker for a
    // file that did not elaborate at all.
    const source = fs.readFileSync(path.join(FIX, 'do-workers/nested-carrier.ts'), 'utf8');
    const generated = generateLeanTracked(rewriteModule(parseFile({ fileName: 'nested.ts', sourceText: source })));
    expect(generated.degradations).toEqual([{ level: 'sorry', site: 'def chosen' }]);
    expect(generated.code).toContain('(sorry : Registry)');
    // The union asks the same question at the other `deriving` site, which never asked it: Lean
    // builds `Inhabited` from one constructor, so only a union whose every constructor carries a
    // carrier loses it.
    for (const declaration of ['structure Rooms where', 'structure Registry where', 'inductive Binding where']) {
      const body = generated.code.slice(generated.code.indexOf(declaration));
      expect(body.slice(0, body.indexOf('\n\n'))).toContain('deriving Repr, BEq');
      expect(body.slice(0, body.indexOf('\n\n'))).not.toContain('Inhabited');
    }
  });
});

// ─── --strict ─────────────────────────────────────────────────────────────────

describe('CLI --strict', () => {
  function withMutualSource(): { dir: string; file: string } {
    const dir = tmpDir('tslean-strict-');
    const file = path.join(dir, 'mutual.ts');
    fs.writeFileSync(file, MUTUAL_INTERFACES, 'utf8');
    return { dir, file };
  }

  it('rejects a generated sorry in single-file mode', () => {
    const { dir, file } = withMutualSource();
    const output = path.join(dir, 'out.lean');
    const run = spawnCli(['ts-to-lean', file, '-o', output, '--strict']);
    expect(run.status).toBe(1);
    expect(run.stderr).toContain('--strict: 2 sorry axiom(s) in generated Lean');
    expect(run.stderr).toContain('instance : Inhabited Node1 := ⟨sorry⟩');
    expect(fs.existsSync(output)).toBe(false);
  });

  it('rejects a generated sorry in project mode', () => {
    const { dir } = withMutualSource();
    const output = path.join(dir, 'out');
    const run = spawnCli(['ts-to-lean', dir, '-o', output, '--no-lakefile', '--strict']);
    expect(run.status).toBe(1);
    expect(run.stderr).toContain('--strict: 2 sorry axiom(s) in generated Lean');
    expect(run.stderr).toContain('mutual.ts: instance : Inhabited Node1 := ⟨sorry⟩');
    expect(fs.existsSync(output)).toBe(false);
  });

  it('rejects a default placeholder that stands in for a value', () => {
    const dir = tmpDir('tslean-strict-default-');
    const run = spawnCli([
      'ts-to-lean',
      path.join(FIX, 'advanced/anonymous-object.ts'),
      '-o',
      path.join(dir, 'out.lean'),
      '--strict',
    ]);
    expect(run.status).toBe(1);
    expect(run.stderr).toContain('default placeholder(s) in generated Lean');
    expect(run.stderr).toContain('default at def area');
  });

  it('rejects the sorry a struct field carrying an uninhabited type leaves behind', () => {
    const dir = tmpDir('tslean-strict-carrier-');
    const run = spawnCli([
      'ts-to-lean',
      path.join(FIX, 'do-workers/nested-carrier.ts'),
      '-o',
      path.join(dir, 'out.lean'),
      '--strict',
    ]);
    expect(run.status).toBe(1);
    expect(run.stderr).toContain('--strict: 1 sorry axiom(s) in generated Lean');
    expect(run.stderr).toContain('sorry at def chosen');
  });

  it('accepts output that carries no placeholder', () => {
    const dir = tmpDir('tslean-strict-clean-');
    const run = spawnCli([
      'ts-to-lean',
      path.join(FIX, 'basic/hello.ts'),
      '-o',
      path.join(dir, 'out.lean'),
      '--strict',
    ]);
    expect(run.status).toBe(0);
    expect(run.stdout).toContain('→');
  });

  it('emits the same degraded output without --strict', () => {
    const { dir, file } = withMutualSource();
    const out = path.join(dir, 'out.lean');
    const run = spawnCli(['ts-to-lean', file, '-o', out]);
    expect(run.status).toBe(0);
    expect(fs.readFileSync(out, 'utf8')).toContain('⟨sorry⟩');
  });
});
