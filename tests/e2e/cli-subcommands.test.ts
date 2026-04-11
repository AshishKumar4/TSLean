// E2E tests for the new CLI subcommand interface.

import { describe, it, expect, afterEach } from 'vitest';
import { execSync, ExecSyncOptions } from 'child_process';
import * as fs from 'fs';
import * as os from 'os';
import * as path from 'path';

const ROOT = process.cwd();
const CLI  = path.join(ROOT, 'src/cli.ts');
const FIX  = path.join(ROOT, 'tests/fixtures');

const execOpts: ExecSyncOptions = { stdio: 'pipe', env: { ...process.env, NO_COLOR: '1' } };

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
    try { fs.rmSync(p, { recursive: true, force: true }); } catch {}
  }
  cleanup.length = 0;
});

// ─── Help & version ──────────────────────────────────────────────────────────

describe('CLI: help and version', () => {
  it('--help shows usage', () => {
    const out = execSync(`npx tsx ${CLI} --help`, execOpts).toString();
    expect(out).toContain('tslean');
    expect(out).toContain('compile');
    expect(out).toContain('self-host');
    expect(out).toContain('verify');
    expect(out).toContain('init');
  });

  it('-h shows usage', () => {
    const out = execSync(`npx tsx ${CLI} -h`, execOpts).toString();
    expect(out).toContain('compile');
  });

  it('no args shows help', () => {
    const out = execSync(`npx tsx ${CLI}`, execOpts).toString();
    expect(out).toContain('USAGE');
  });

  it('--version shows version', () => {
    const out = execSync(`npx tsx ${CLI} --version`, execOpts).toString();
    expect(out).toMatch(/^tslean \d+\.\d+\.\d+/);
  });

  it('-v shows version', () => {
    const out = execSync(`npx tsx ${CLI} -v`, execOpts).toString();
    expect(out).toMatch(/^tslean \d+\.\d+\.\d+/);
  });
});

// ─── compile subcommand: single file ─────────────────────────────────────────

describe('CLI: compile single file', () => {
  it('compile <file> -o <out> produces Lean', () => {
    const out = tmpFile();
    cleanup.push(out);
    execSync(`npx tsx ${CLI} compile ${FIX}/basic/hello.ts -o ${out}`, execOpts);
    const code = fs.readFileSync(out, 'utf8');
    expect(code).toContain('open TSLean');
    expect(code).toContain('def greet');
  });

  it('compile with --output (long form)', () => {
    const out = tmpFile();
    cleanup.push(out);
    execSync(`npx tsx ${CLI} compile ${FIX}/basic/hello.ts --output ${out}`, execOpts);
    expect(fs.existsSync(out)).toBe(true);
  });

  it('compile with --verify adds obligations', () => {
    const out = tmpFile();
    cleanup.push(out);
    const stdout = execSync(`npx tsx ${CLI} compile ${FIX}/effects/exceptions.ts -o ${out} --verify`, execOpts).toString();
    const code = fs.readFileSync(out, 'utf8');
    expect(code).toContain('open TSLean');
  });

  it('compile missing file exits with error', () => {
    expect(() => {
      execSync(`npx tsx ${CLI} compile nonexistent.ts -o /tmp/nope.lean`, { ...execOpts, stdio: 'pipe' });
    }).toThrow();
  });
});

// ─── compile subcommand: directory ───────────────────────────────────────────

describe('CLI: compile directory', () => {
  it('compile <dir> -o <outdir> transpiles all .ts files', () => {
    const outDir = tmpDir();
    cleanup.push(outDir);
    const stdout = execSync(
      `npx tsx ${CLI} compile ${FIX}/basic/ -o ${outDir}`, execOpts
    ).toString();
    expect(stdout).toContain('file(s) transpiled');
    expect(fs.existsSync(path.join(outDir, 'Hello.lean'))).toBe(true);
    expect(fs.existsSync(path.join(outDir, 'Interfaces.lean'))).toBe(true);
    expect(fs.existsSync(path.join(outDir, 'Classes.lean'))).toBe(true);
  });

  it('compile detects directory input without --project flag', () => {
    const outDir = tmpDir();
    cleanup.push(outDir);
    const stdout = execSync(
      `npx tsx ${CLI} compile ${FIX}/basic -o ${outDir}`, execOpts
    ).toString();
    expect(stdout).toContain('file(s) transpiled');
  });
});

// ─── Legacy mode (backward compat) ──────────────────────────────────────────

describe('CLI: legacy mode', () => {
  it('positional <file> -o <out> still works', () => {
    const out = tmpFile();
    cleanup.push(out);
    execSync(`npx tsx ${CLI} ${FIX}/basic/hello.ts -o ${out}`, execOpts);
    const code = fs.readFileSync(out, 'utf8');
    expect(code).toContain('open TSLean');
  });

  it('--project <dir> -o <out> still works', () => {
    const outDir = tmpDir();
    cleanup.push(outDir);
    execSync(`npx tsx ${CLI} --project ${FIX}/basic/ -o ${outDir}`, execOpts);
    expect(fs.existsSync(path.join(outDir, 'Hello.lean'))).toBe(true);
  });
});

// ─── init subcommand ─────────────────────────────────────────────────────────

describe('CLI: init', () => {
  it('creates tslean.json and src/example.ts', () => {
    const dir = tmpDir();
    cleanup.push(dir);
    execSync(`npx tsx ${CLI} init ${dir}`, execOpts);
    expect(fs.existsSync(path.join(dir, 'tslean.json'))).toBe(true);
    expect(fs.existsSync(path.join(dir, 'src', 'example.ts'))).toBe(true);
    expect(fs.existsSync(path.join(dir, 'lean'))).toBe(true);
    const config = JSON.parse(fs.readFileSync(path.join(dir, 'tslean.json'), 'utf8'));
    expect(config.compilerOptions.namespace).toBe('TSLean.Generated');
  });

  it('refuses to init twice', () => {
    const dir = tmpDir();
    cleanup.push(dir);
    execSync(`npx tsx ${CLI} init ${dir}`, execOpts);
    expect(() => {
      execSync(`npx tsx ${CLI} init ${dir}`, { ...execOpts, stdio: 'pipe' });
    }).toThrow();
  });
});

// ─── Error output ────────────────────────────────────────────────────────────

describe('CLI: error handling', () => {
  it('no input shows error message', () => {
    expect(() => {
      execSync(`npx tsx ${CLI} compile`, { ...execOpts, stdio: 'pipe' });
    }).toThrow();
  });
});
