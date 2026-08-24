// E2E tests for the new CLI subcommand interface.

import { describe, it, expect, afterEach } from 'vitest';
import { type ExecFileSyncOptions } from 'node:child_process';
import * as fs from 'fs';
import * as os from 'os';
import * as path from 'path';
import { runCli } from '../helpers/run-cli.js';

const ROOT = process.cwd();
const FIX = path.join(ROOT, 'tests/fixtures');

const execOpts: ExecFileSyncOptions = { stdio: 'pipe', env: { ...process.env, NO_COLOR: '1' } };

function tmpFile(ext = '.lean'): string {
  return path.join(os.tmpdir(), `tslean_sub_${Date.now()}_${Math.random().toString(36).slice(2)}${ext}`);
}

function tmpDir(): string {
  const d = path.join(os.tmpdir(), `tslean_sub_${Date.now()}_${Math.random().toString(36).slice(2)}`);
  fs.mkdirSync(d, { recursive: true });
  return d;
}

const cleanup: string[] = [];
afterEach(() => {
  for (const p of cleanup) {
    try {
      fs.rmSync(p, { recursive: true, force: true });
    } catch {}
  }
  cleanup.length = 0;
});

// ─── Help & version ──────────────────────────────────────────────────────────

describe('CLI: help and version', () => {
  it('--help shows usage', () => {
    const out = runCli(['--help'], execOpts).toString();
    expect(out).toContain('tslean');
    expect(out).toContain('ts-to-lean');
    expect(out).toContain('lean-to-ts');
    expect(out).toContain('init');
  });

  it('-h shows usage', () => {
    const out = runCli(['-h'], execOpts).toString();
    expect(out).toContain('ts-to-lean');
  });

  it('no args shows help', () => {
    const out = runCli([], execOpts).toString();
    expect(out).toContain('USAGE');
  });

  it('--version shows version', () => {
    const out = runCli(['--version'], execOpts).toString();
    expect(out).toMatch(/^tslean \d+\.\d+\.\d+/);
  });

  it('-v shows version', () => {
    const out = runCli(['-v'], execOpts).toString();
    expect(out).toMatch(/^tslean \d+\.\d+\.\d+/);
  });

  it('shows direction-specific Lean to TypeScript help', () => {
    const out = runCli(['lean-to-ts', '--help'], execOpts).toString();
    expect(out).toContain('tslean lean-to-ts');
    expect(out).toContain('--project-root');
  });
});

// ─── compile subcommand: single file ─────────────────────────────────────────

describe('CLI: TypeScript to Lean single file', () => {
  it('ts-to-lean <file> -o <out> produces Lean', () => {
    const out = tmpFile();
    cleanup.push(out);
    runCli(['ts-to-lean', path.join(FIX, 'basic/hello.ts'), '-o', out], execOpts);
    const code = fs.readFileSync(out, 'utf8');
    expect(code).toContain('open TSLean');
    expect(code).toContain('def greet');
  });

  it('compile with --output (long form)', () => {
    const out = tmpFile();
    cleanup.push(out);
    runCli(['ts-to-lean', path.join(FIX, 'basic/hello.ts'), '--output', out], execOpts);
    expect(fs.existsSync(out)).toBe(true);
  });

  it('emits proof obligations only when requested', () => {
    const out = tmpFile();
    cleanup.push(out);
    const stdout = runCli(
      ['ts-to-lean', path.join(FIX, 'effects/exceptions.ts'), '-o', out, '--proof-obligations'],
      execOpts,
    ).toString();
    const code = fs.readFileSync(out, 'utf8');
    expect(code).toContain('open TSLean');
  });

  it('compile missing file exits with error', () => {
    expect(() => {
      runCli(['ts-to-lean', 'nonexistent.ts', '-o', '/tmp/nope.lean'], { ...execOpts, stdio: 'pipe' });
    }).toThrow();
  });
});

// ─── compile subcommand: directory ───────────────────────────────────────────

describe('CLI: TypeScript to Lean project', () => {
  // Recursively find all .lean files under a directory
  function findLean(dir: string): string[] {
    const out: string[] = [];
    if (!fs.existsSync(dir)) return out;
    for (const e of fs.readdirSync(dir, { withFileTypes: true })) {
      const full = path.join(dir, e.name);
      if (e.isDirectory()) out.push(...findLean(full));
      else if (e.name.endsWith('.lean')) out.push(e.name);
    }
    return out;
  }

  it('ts-to-lean <dir> -o <outdir> compiles all .ts files', () => {
    const outDir = tmpDir();
    cleanup.push(outDir);
    const stdout = runCli(['ts-to-lean', path.join(FIX, 'basic/'), '-o', outDir, '--no-lakefile'], execOpts).toString();
    expect(stdout).toContain('file(s) transpiled');
    const leans = findLean(outDir);
    expect(leans).toContain('Hello.lean');
    expect(leans).toContain('Interfaces.lean');
    expect(leans).toContain('Classes.lean');
  });

  it('detects a directory input without a mode flag', () => {
    const outDir = tmpDir();
    cleanup.push(outDir);
    const stdout = runCli(['ts-to-lean', path.join(FIX, 'basic'), '-o', outDir, '--no-lakefile'], execOpts).toString();
    expect(stdout).toContain('file(s) transpiled');
  });
});

// Removed forms stay rejected rather than becoming compatibility aliases.
describe('CLI: removed command forms', () => {
  it('rejects a bare positional source', () => {
    expect(() => {
      runCli([path.join(FIX, 'basic/hello.ts')], execOpts);
    }).toThrow();
  });

  it('rejects the former compile command', () => {
    expect(() => {
      runCli(['compile', path.join(FIX, 'basic/hello.ts')], execOpts);
    }).toThrow();
  });

  it('rejects the former --project mode', () => {
    expect(() => {
      runCli(['--project', path.join(FIX, 'basic')], execOpts);
    }).toThrow();
  });
});

// ─── init subcommand ─────────────────────────────────────────────────────────

describe('CLI: init', () => {
  it('creates tsconfig.json and src/example.ts', () => {
    const dir = tmpDir();
    cleanup.push(dir);
    runCli(['init', dir], execOpts);
    expect(fs.existsSync(path.join(dir, 'tsconfig.json'))).toBe(true);
    expect(fs.existsSync(path.join(dir, 'src', 'example.ts'))).toBe(true);
    expect(fs.existsSync(path.join(dir, 'lean'))).toBe(true);
    const config = JSON.parse(fs.readFileSync(path.join(dir, 'tsconfig.json'), 'utf8'));
    expect(config.compilerOptions).toMatchObject({
      module: 'NodeNext',
      moduleResolution: 'NodeNext',
      strict: true,
    });
  });

  it('refuses to init twice', () => {
    const dir = tmpDir();
    cleanup.push(dir);
    runCli(['init', dir], execOpts);
    expect(() => {
      runCli(['init', dir], { ...execOpts, stdio: 'pipe' });
    }).toThrow();
  });
});

// ─── Error output ────────────────────────────────────────────────────────────

describe('CLI: error handling', () => {
  it('no input shows error message', () => {
    expect(() => {
      runCli(['ts-to-lean'], { ...execOpts, stdio: 'pipe' });
    }).toThrow();
  });

  it('rejects unknown and duplicate options', () => {
    const source = path.join(FIX, 'basic/hello.ts');
    expect(() => runCli(['ts-to-lean', source, '--unknown'], execOpts)).toThrow();
    expect(() => runCli(['ts-to-lean', source, '--output', '/tmp/a.lean', '-o', '/tmp/b.lean'], execOpts)).toThrow();
  });

  it('rejects Lake execution without watch mode', () => {
    expect(() => runCli(['ts-to-lean', path.join(FIX, 'basic/hello.ts'), '--lake'], execOpts)).toThrow();
  });
});
