// V3 project mode tests: multi-file transpilation with full content verification.

import { describe, it, expect, beforeAll } from 'vitest';
import { execSync } from 'child_process';
import * as fs from 'fs';
import * as os from 'os';
import * as path from 'path';
import { transpileProject, toLeanPath, toModuleName } from '../src/project/index.js';

const ROOT   = process.cwd();
const CLI    = path.join(ROOT, 'src/cli.ts');
const FP_DIR = path.join(ROOT, 'tests/fixtures/full-project');

// ─── File content verification ─────────────────────────────────────────────────

describe('Project v3: content quality', () => {
  let outDir: string;
  let files: Record<string, string> = {};

  beforeAll(() => {
    outDir = fs.mkdtempSync(path.join(os.tmpdir(), 'tslean-v3-'));
    execSync(`npx tsx ${CLI} --project ${FP_DIR} -o ${outDir}`, { stdio: 'pipe' });
    function read(dir: string) {
      for (const e of fs.readdirSync(dir, { withFileTypes: true })) {
        const full = path.join(dir, e.name);
        if (e.isDirectory()) { read(full); continue; }
        if (e.name.endsWith('.lean')) files[path.relative(outDir, full)] = fs.readFileSync(full, 'utf8');
      }
    }
    read(outDir);
  });

  it('all files non-empty (>10 lines)', () => {
    for (const [n, content] of Object.entries(files)) {
      expect(content.split('\n').length, `${n} is too thin`).toBeGreaterThan(10);
    }
  });

  it('Router.lean has def fetch (from export default)', () => {
    const router = files[Object.keys(files).find(k => k.includes('Router.lean'))!];
    expect(router).toBeDefined();
    expect(router).toMatch(/def fetch/);
  });

  it('Router.lean has RouterEnv structure', () => {
    const router = files[Object.keys(files).find(k => k.includes('Router.lean'))!];
    expect(router).toContain('structure RouterEnv');
  });

  it('Router.lean has extends in structure', () => {
    const router = files[Object.keys(files).find(k => k.includes('Router.lean'))!];
    // RouterEnv extends Env
    expect(router).toMatch(/extends/);
  });

  it('AuthDo.lean has real function bodies (not just sorry)', () => {
    const auth = files[Object.keys(files).find(k => k.includes('AuthDo.lean'))!];
    expect(auth).toBeDefined();
    // Should have def register, login, verify with actual bodies
    expect(auth).toMatch(/def register/);
    expect(auth).toMatch(/def login/);
    expect(auth).toMatch(/def verify/);
    // Verify there are actual expressions, not just `sorry` everywhere
    const lines = auth.split('\n').filter(l => l.trim().length > 0);
    const sorrys = lines.filter(l => l.trim() === 'sorry').length;
    expect(sorrys).toBeLessThan(lines.length * 0.3);  // Less than 30% sorry
  });

  it('ChatRoomDo.lean has Message structure and fetch', () => {
    const chat = files[Object.keys(files).find(k => k.includes('ChatRoomDo.lean'))!];
    expect(chat).toBeDefined();
    expect(chat).toContain('structure Message');
    expect(chat).toMatch(/def fetch/);
  });

  it('Types.lean has UserId and User structures', () => {
    const types = files[Object.keys(files).find(k => k.includes('Types.lean'))!];
    expect(types).toBeDefined();
    expect(types).toContain('structure UserId');
    expect(types).toContain('structure User');
  });

  it('Validators.lean has validateEmail function', () => {
    const val = files[Object.keys(files).find(k => k.includes('Validators.lean'))!];
    expect(val).toBeDefined();
    expect(val).toMatch(/def validateEmail/);
  });
});

// ─── Cross-file imports ───────────────────────────────────────────────────────

describe('Project v3: cross-file imports (no .js suffix)', () => {
  let files: Record<string, string> = {};
  beforeAll(() => {
    const outDir = fs.mkdtempSync(path.join(os.tmpdir(), 'tslean-v3-imp-'));
    execSync(`npx tsx ${CLI} --project ${FP_DIR} -o ${outDir}`, { stdio: 'pipe' });
    function read(dir: string) {
      for (const e of fs.readdirSync(dir, { withFileTypes: true })) {
        const full = path.join(dir, e.name);
        if (e.isDirectory()) { read(full); continue; }
        if (e.name.endsWith('.lean')) files[path.relative(outDir, full)] = fs.readFileSync(full, 'utf8');
      }
    }
    read(outDir);
  });

  it('AuthDo imports Types (no .js in import lines)', () => {
    const auth = files[Object.keys(files).find(k => k.includes('AuthDo.lean'))!];
    if (auth) {
      expect(auth).toContain('import TSLean.Generated.Shared.Types');
      // Check import lines specifically (not all content — json method contains .js substring)
      const importLines = auth.split('\n').filter(l => l.startsWith('import '));
      for (const line of importLines) {
        expect(line).not.toContain('.js');
      }
    }
  });

  it('AuthDo imports Validators (no .js)', () => {
    const auth = files[Object.keys(files).find(k => k.includes('AuthDo.lean'))!];
    if (auth) expect(auth).toContain('import TSLean.Generated.Shared.Validators');
  });

  it('no import has .js extension', () => {
    for (const [n, content] of Object.entries(files)) {
      const importLines = content.split('\n').filter(l => l.startsWith('import '));
      for (const line of importLines) {
        expect(line, `${n}: ${line}`).not.toContain('.js');
      }
    }
  });
});

// ─── --project flag with various options ──────────────────────────────────────

describe('Project v3: CLI project mode', () => {
  it('--project on basic/ transpiles 3 files', () => {
    const outDir = fs.mkdtempSync(path.join(os.tmpdir(), 'tslean-v3-basic-'));
    execSync(`npx tsx ${CLI} --project ${path.join(ROOT, 'tests/fixtures/basic')} -o ${outDir}`, { stdio: 'pipe' });
    const leans = fs.readdirSync(outDir).filter(f => f.endsWith('.lean'));
    expect(leans.length).toBe(3);
    fs.rmSync(outDir, { recursive: true });
  });

  it('--project on advanced/ transpiles fixtures', () => {
    const outDir = fs.mkdtempSync(path.join(os.tmpdir(), 'tslean-v3-adv-'));
    execSync(`npx tsx ${CLI} --project ${path.join(ROOT, 'tests/fixtures/advanced')} -o ${outDir}`, { stdio: 'pipe' });
    const leans = fs.readdirSync(outDir).filter(f => f.endsWith('.lean'));
    expect(leans.length).toBeGreaterThan(0);
    fs.rmSync(outDir, { recursive: true });
  });

  it('--project with --verify adds obligations', () => {
    const outDir = fs.mkdtempSync(path.join(os.tmpdir(), 'tslean-v3-verify-'));
    execSync(`npx tsx ${CLI} --project ${path.join(ROOT, 'tests/fixtures/basic')} -o ${outDir} --verify`, { stdio: 'pipe' });
    const leans = fs.readdirSync(outDir).filter(f => f.endsWith('.lean'));
    expect(leans.length).toBe(3);
    // At least one file should have verification content
    const contents = leans.map(f => fs.readFileSync(path.join(outDir, f), 'utf8'));
    expect(contents.some(c => c.includes('open TSLean'))).toBe(true);
    fs.rmSync(outDir, { recursive: true });
  });
});

// ─── Single-file mode ─────────────────────────────────────────────────────────

describe('Project v3: single-file CLI', () => {
  it('hello.ts generates correct output', () => {
    const out = path.join(os.tmpdir(), 'hello_v3.lean');
    execSync(`npx tsx ${CLI} ${path.join(ROOT, 'tests/fixtures/basic/hello.ts')} -o ${out}`, { stdio: 'pipe' });
    const content = fs.readFileSync(out, 'utf8');
    expect(content).toContain('partial def factorial');
    expect(content).toContain('def greet');
    fs.unlinkSync(out);
  });

  it('counter DO generates DO imports', () => {
    const out = path.join(os.tmpdir(), 'counter_v3.lean');
    execSync(`npx tsx ${CLI} ${path.join(ROOT, 'tests/fixtures/durable-objects/counter.ts')} -o ${out}`, { stdio: 'pipe' });
    const content = fs.readFileSync(out, 'utf8');
    expect(content).toContain('import TSLean.DurableObjects.Http');
    expect(content).toContain('import TSLean.Runtime.Monad');
    fs.unlinkSync(out);
  });

  it('export-patterns.ts generates def createConfig', () => {
    const out = path.join(os.tmpdir(), 'exports_v3.lean');
    execSync(`npx tsx ${CLI} ${path.join(ROOT, 'tests/fixtures/advanced/export-patterns.ts')} -o ${out}`, { stdio: 'pipe' });
    const content = fs.readFileSync(out, 'utf8');
    expect(content).toMatch(/def createConfig/);
    fs.unlinkSync(out);
  });
});

// ─── toModuleName and toLeanPath ───────────────────────────────────────────────

describe('Project v3: path utilities', () => {
  it('toModuleName converts paths correctly', () => {
    expect(toModuleName('/p/src/foo.ts', '/p/src')).toBe('TSLean.Generated.Foo');
    expect(toModuleName('/p/src/shared/types.ts', '/p/src')).toBe('TSLean.Generated.Shared.Types');
    expect(toModuleName('/p/src/chat-room.ts', '/p/src')).toBe('TSLean.Generated.ChatRoom');
  });

  it('toLeanPath converts paths correctly', () => {
    expect(toLeanPath('/p/src/foo.ts', '/p/src', '/out')).toBe('/out/Foo.lean');
    expect(toLeanPath('/p/src/shared/types.ts', '/p/src', '/out')).toBe('/out/Shared/Types.lean');
  });

  it('custom rootNS works', () => {
    expect(toModuleName('/p/src/foo.ts', '/p/src', 'MyApp')).toBe('MyApp.Foo');
  });
});

// ─── transpileProject API ─────────────────────────────────────────────────────

describe('Project v3: transpileProject API', () => {
  it('returns errors for non-existent dir', () => {
    const result = transpileProject({ projectDir: '/nonexistent/path', outputDir: '/tmp' });
    expect(result.errors.length).toBeGreaterThan(0);
  });

  it('returns files array for valid dir', () => {
    const outDir = fs.mkdtempSync(path.join(os.tmpdir(), 'tslean-api-'));
    const result = transpileProject({ projectDir: path.join(ROOT, 'tests/fixtures/basic'), outputDir: outDir });
    expect(result.files.length).toBe(3);
    expect(result.errors.length).toBe(0);
    result.files.forEach(f => {
      expect(f.leanFile).toMatch(/\.lean$/);
      expect(f.content.length).toBeGreaterThan(0);
    });
    fs.rmSync(outDir, { recursive: true });
  });
});
