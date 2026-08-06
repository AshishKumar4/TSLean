import * as fs from 'node:fs';
import * as os from 'node:os';
import * as path from 'node:path';
import { execFileSync } from 'node:child_process';
import { describe, expect, it } from 'vitest';
import { printDeclStr, printExprStr } from '../src/codegen/printer.js';
import { extractDtsStubs, generateLeanStub } from '../src/stubs/dts-reader.js';

function withDtsFiles(files: Record<string, string>, run: (entry: string) => void): void {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'tslean-dts-'));
  try {
    for (const [name, source] of Object.entries(files)) {
      fs.writeFileSync(path.join(dir, name), source);
    }
    run(path.join(dir, 'index.d.ts'));
  } finally {
    fs.rmSync(dir, { recursive: true, force: true });
  }
}

describe('d.ts reader', () => {
  it('fails clearly when the entry file is missing', () => {
    withDtsFiles({}, entry => {
      expect(() => extractDtsStubs(entry)).toThrow(
        `Unable to read .d.ts entry "${entry}". Check that the file exists and is readable.`,
      );
    });
  });

  it('fails clearly when the entry file is unreadable', () => {
    withDtsFiles({ 'index.d.ts': 'export interface Request {}' }, entry => {
      fs.chmodSync(entry, 0o000);

      expect(() => extractDtsStubs(entry)).toThrow(
        `Unable to read .d.ts entry "${entry}". Check that the file exists and is readable.`,
      );
    });
  });

  it('extracts direct, indirect, default, re-exported, and namespace declarations once', () => {
    withDtsFiles({
      'index.d.ts': `
        /** Direct documentation. */
        export function direct(value: string): string;
        /** The overload documentation. */
        export function overloaded(value: string): string;
        export function overloaded(value: number): number;
        /** Public alias documentation. */
        interface Internal { value: string }
        export { Internal as PublicType };
        /** Default documentation. */
        export default class Client {}
        export * from './more.js';
        /** Tools documentation. */
        export namespace Tools {
          /** Run documentation. */
          export function run(): void;
          function hidden(): void;
          export { hidden as exposed };
        }
      `,
      'more.d.ts': `/** Re-export documentation. */ export declare const reexported: boolean;`,
    }, entry => {
      const declarations = extractDtsStubs(entry);

      expect(declarations.map(declaration => declaration.name)).toEqual([
        'direct', 'overloaded', 'PublicType', 'Client', 'Tools', 'reexported',
      ]);
      expect(declarations.find(declaration => declaration.name === 'direct')?.doc).toBe('Direct documentation.');
      expect(declarations.find(declaration => declaration.name === 'PublicType')?.doc).toBe('Public alias documentation.');
      expect(declarations.filter(declaration => declaration.name === 'overloaded')).toHaveLength(1);
      const tools = declarations.find(declaration => declaration.name === 'Tools');
      expect(tools?.members?.map(member => member.name)).toEqual(['run', 'exposed']);
      expect(tools?.members?.find(member => member.name === 'run')?.doc).toBe('Run documentation.');
    });
  });

  it('extracts ambient module exports and safely renders JSDoc', () => {
    withDtsFiles({
      'index.d.ts': `
        declare module "ambient" {
          /** Text containing /- and -/ must stay in the comment. */
          export interface Request {}
        }
      `,
    }, entry => {
      const declarations = extractDtsStubs(entry);
      expect(declarations).toMatchObject([{
        kind: 'namespace',
        name: 'ambient',
        members: [{ kind: 'opaque-type', name: 'Request', doc: 'Text containing /- and -/ must stay in the comment.' }],
      }]);

      const lean = generateLeanStub({ packageName: 'ambient', leanModule: 'Test', decls: declarations });
      expect(lean).toContain('/-- Text containing / - and - / must stay in the comment. -/');
      expect(lean).not.toContain('/-- Text containing /- and -/ must stay in the comment. -/');
    });
  });

  it('escapes all generated Lean block-comment content', () => {
    expect(printDeclStr({
      tag: 'Def',
      partial: false,
      name: 'safe',
      tyParams: [],
      params: [],
      retTy: { tag: 'TyName', name: 'Unit' },
      body: { tag: 'Default' },
      docComment: 'before /- middle -/ after',
    })).toContain('/-- before / - middle - / after -/');
    expect(printExprStr({ tag: 'Sorry', reason: 'before /- middle -/ after' }))
      .toBe('sorry /- before / - middle - / after -/');
  });

  it('emits compilable generic class stubs with method documentation', () => {
    withDtsFiles({
      'index.d.ts': `
        /** A boxed value. */
        export class Box<T> {
          /** Returns the boxed value. */
          get(): T;
        }
      `,
    }, entry => {
      const lean = generateLeanStub({
        packageName: 'generic-box',
        leanModule: 'Test',
        decls: extractDtsStubs(entry),
      });

      expect(lean).toBe(`-- Test
-- Auto-generated Lean stubs for npm package: generic-box
-- These are axiomatized declarations for verification purposes.

namespace Test

/-- A boxed value. -/
opaque Box (T : Type) : Type
instance {T : Type} : Inhabited (Box T) := ⟨sorry⟩

/-- Returns the boxed value. -/
axiom Box.get {T : Type} (self : Box T) : T


end Test`);

      const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'tslean-lean-stub-'));
      const leanFile = path.join(dir, 'GenericStub.lean');
      try {
        fs.writeFileSync(leanFile, `import TSLean.Runtime.Basic\n\n${lean}\n\nexample {T : Type} : Inhabited (Test.Box T) := inferInstance\n`);
        execFileSync('lake', ['env', 'lean', leanFile], {
          cwd: path.resolve('lean'),
          encoding: 'utf8',
          stdio: 'pipe',
        });
      } finally {
        fs.rmSync(dir, { recursive: true, force: true });
      }
    });
  });

  it('diagnoses generic constraints that cannot be safely translated', () => {
    withDtsFiles({
      'index.d.ts': 'export interface Box<T extends string> {}',
    }, entry => {
      expect(() => extractDtsStubs(entry)).toThrow(
        'Unsupported generic constraint on "Box.T": string',
      );
    });
  });
});
