// Tests for multi-file project mode.

import { describe, it, expect, beforeAll } from 'vitest';
import * as path from 'path';
import * as fs from 'fs';
import * as os from 'os';
import { transpileProject, writeProjectOutputs } from '../src/project/index.js';

const FP_DIR = path.join(process.cwd(), 'tests/fixtures/full-project');
const BASIC = path.join(process.cwd(), 'tests/fixtures/basic');

describe('transpileProject – full-project fixture', () => {
  let result: ReturnType<typeof transpileProject>;
  let outDir: string;

  beforeAll(() => {
    outDir = fs.mkdtempSync(path.join(os.tmpdir(), 'tslean-fp-'));
    result = transpileProject({ projectDir: FP_DIR, outputDir: outDir });
  });

  it('produces files', () => expect(result.files.length).toBeGreaterThan(0));
  it('0 errors', () => {
    if (result.errors.length) console.warn(result.errors);
    expect(result.errors.length).toBe(0);
  });
  it('all files are .lean', () => result.files.forEach((f) => expect(f.leanFile).toMatch(/\.lean$/)));
  it('all content is non-empty', () => result.files.forEach((f) => expect(f.content.length).toBeGreaterThan(0)));
  it('has Shared/Types.lean', () => expect(result.files.some((f) => f.leanFile.includes('Types.lean'))).toBe(true));
  it('has Shared/Validators.lean', () =>
    expect(result.files.some((f) => f.leanFile.includes('Validators.lean'))).toBe(true));
  it('has Backend/AuthDo.lean', () => expect(result.files.some((f) => f.leanFile.includes('AuthDo.lean'))).toBe(true));
  it('has Backend/Router.lean', () => expect(result.files.some((f) => f.leanFile.includes('Router.lean'))).toBe(true));

  it('AuthDo.lean imports TSLean.Generated.Shared.Types (not .js)', () => {
    const auth = result.files.find((f) => f.leanFile.includes('AuthDo.lean'));
    if (!auth) return;
    expect(auth.content).toContain('import TSLean.Generated.Shared.Types');
    expect(auth.content).not.toContain('import TSLean.Generated.Shared.Types.js');
  });

  it('AuthDo.lean imports TSLean.Generated.Shared.Validators', () => {
    const auth = result.files.find((f) => f.leanFile.includes('AuthDo.lean'));
    if (!auth) return;
    expect(auth.content).toContain('import TSLean.Generated.Shared.Validators');
  });

  it('all files have open TSLean', () => result.files.forEach((f) => expect(f.content).toContain('open TSLean')));

  it('no duplicate imports in any file', () => {
    for (const { content } of result.files) {
      const lines = content.split('\n').filter((l) => l.startsWith('import '));
      const unique = new Set(lines);
      expect(unique.size).toBe(lines.length);
    }
  });
});

describe('transpileProject – basic fixture', () => {
  it('transpiles all 3 basic files', () => {
    const outDir = fs.mkdtempSync(path.join(os.tmpdir(), 'tslean-basic-'));
    const result = transpileProject({ projectDir: BASIC, outputDir: outDir });
    expect(result.files.length).toBe(3);
    expect(result.errors.length).toBe(0);
  });
});

describe('transpileProject planning boundary', () => {
  it('writes no project artifact before explicit publication', () => {
    const outDir = fs.mkdtempSync(path.join(os.tmpdir(), 'tslean-plan-'));
    const result = transpileProject({ projectDir: BASIC, outputDir: outDir });

    expect(result.errors).toEqual([]);
    expect(result.build).toBeDefined();
    expect(fs.readdirSync(outDir)).toEqual([]);

    writeProjectOutputs(result);
    expect(fs.existsSync(path.join(outDir, 'lakefile.toml'))).toBe(true);
    expect(fs.existsSync(path.join(outDir, 'lean-toolchain'))).toBe(true);
    expect(result.files.every((file) => fs.existsSync(file.leanFile))).toBe(true);
    fs.rmSync(outDir, { force: true, recursive: true });
  });
});

describe('transpileProject – empty directory', () => {
  it('returns error for empty dir', () => {
    const emptyDir = fs.mkdtempSync(path.join(os.tmpdir(), 'tslean-empty-'));
    const result = transpileProject({ projectDir: emptyDir, outputDir: os.tmpdir() });
    expect(result.errors.length).toBeGreaterThan(0);
    expect(result.files).toHaveLength(0);
  });
});
