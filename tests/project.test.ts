// Tests for multi-file project mode.

import { describe, it, expect, beforeAll } from 'vitest';
import * as path from 'path';
import * as fs from 'fs';
import * as os from 'os';
import { transpileProject, toLeanPath, toModuleName } from '../src/project/index.js';

const FP_DIR = path.join(process.cwd(), 'tests/fixtures/full-project');
const BASIC  = path.join(process.cwd(), 'tests/fixtures/basic');

describe('toLeanPath / toModuleName', () => {
  it('simple file → lean path',          () => expect(toLeanPath('/p/src/foo.ts', '/p/src', '/out')).toBe('/out/Foo.lean'));
  it('nested file',                       () => expect(toLeanPath('/p/src/shared/types.ts', '/p/src', '/out')).toBe('/out/Shared/Types.lean'));
  it('kebab-case → PascalCase',           () => expect(toLeanPath('/p/src/chat-room.ts', '/p/src', '/out')).toBe('/out/ChatRoom.lean'));
  it('underscore_case → PascalCase',      () => expect(toLeanPath('/p/src/rate_limiter.ts', '/p/src', '/out')).toBe('/out/RateLimiter.lean'));
  it('toModuleName simple',               () => expect(toModuleName('/p/src/foo.ts', '/p/src')).toBe('TSLean.Generated.Foo'));
  it('toModuleName nested',               () => expect(toModuleName('/p/src/shared/types.ts', '/p/src')).toBe('TSLean.Generated.Shared.Types'));
  it('toModuleName custom rootNS',        () => expect(toModuleName('/p/src/foo.ts', '/p/src', 'My')).toBe('My.Foo'));
});

describe('transpileProject – full-project fixture', () => {
  let result: ReturnType<typeof transpileProject>;
  let outDir: string;

  beforeAll(() => {
    outDir = fs.mkdtempSync(path.join(os.tmpdir(), 'tslean-fp-'));
    result = transpileProject({ projectDir: FP_DIR, outputDir: outDir });
  });

  it('produces files',                  () => expect(result.files.length).toBeGreaterThan(0));
  it('0 errors',                        () => { if (result.errors.length) console.warn(result.errors); expect(result.errors.length).toBe(0); });
  it('all files are .lean',             () => result.files.forEach(f => expect(f.leanFile).toMatch(/\.lean$/)));
  it('all content is non-empty',        () => result.files.forEach(f => expect(f.content.length).toBeGreaterThan(0)));
  it('has Shared/Types.lean',           () => expect(result.files.some(f => f.leanFile.includes('Types.lean'))).toBe(true));
  it('has Shared/Validators.lean',      () => expect(result.files.some(f => f.leanFile.includes('Validators.lean'))).toBe(true));
  it('has Backend/AuthDo.lean',         () => expect(result.files.some(f => f.leanFile.includes('AuthDo.lean'))).toBe(true));
  it('has Backend/Router.lean',         () => expect(result.files.some(f => f.leanFile.includes('Router.lean'))).toBe(true));

  it('AuthDo.lean imports TSLean.Generated.Shared.Types (not .js)', () => {
    const auth = result.files.find(f => f.leanFile.includes('AuthDo.lean'));
    if (!auth) return;
    expect(auth.content).toContain('import TSLean.Generated.Shared.Types');
    expect(auth.content).not.toContain('import TSLean.Generated.Shared.Types.js');
  });

  it('AuthDo.lean imports TSLean.Generated.Shared.Validators', () => {
    const auth = result.files.find(f => f.leanFile.includes('AuthDo.lean'));
    if (!auth) return;
    expect(auth.content).toContain('import TSLean.Generated.Shared.Validators');
  });

  it('all files have open TSLean', () =>
    result.files.forEach(f => expect(f.content).toContain('open TSLean')));

  it('no duplicate imports in any file', () => {
    for (const { content } of result.files) {
      const lines  = content.split('\n').filter(l => l.startsWith('import '));
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

describe('transpileProject – empty directory', () => {
  it('returns error for empty dir', () => {
    const emptyDir = fs.mkdtempSync(path.join(os.tmpdir(), 'tslean-empty-'));
    const result = transpileProject({ projectDir: emptyDir, outputDir: os.tmpdir() });
    expect(result.errors.length).toBeGreaterThan(0);
    expect(result.files).toHaveLength(0);
  });
});

describe('transpileProject – with verify', () => {
  it('produces output with --verify', () => {
    const outDir = fs.mkdtempSync(path.join(os.tmpdir(), 'tslean-verify-'));
    const result = transpileProject({ projectDir: BASIC, outputDir: outDir, verify: true });
    expect(result.files.length).toBeGreaterThan(0);
  });
});
