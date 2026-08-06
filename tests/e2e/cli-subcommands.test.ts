// E2E tests for the new CLI subcommand interface.

import { describe, it, expect, afterEach } from 'vitest';
import { execFileSync, type ExecFileSyncOptions } from 'node:child_process';
import { createRequire } from 'node:module';
import * as fs from 'fs';
import * as os from 'os';
import * as path from 'path';
import { runCli } from '../helpers/run-cli.js';

const ROOT = process.cwd();
const FIX  = path.join(ROOT, 'tests/fixtures');
const TSX_CLI = createRequire(import.meta.url).resolve('tsx/cli');

const execOpts: ExecFileSyncOptions = { stdio: 'pipe', env: { ...process.env, NO_COLOR: '1' } };

function tmpFile(ext = '.lean'): string {
  return path.join(os.tmpdir(), `tslean_sub_${Date.now()}_${Math.random().toString(36).slice(2)}${ext}`);
}

function tmpDir(): string {
  const d = path.join(os.tmpdir(), `tslean_sub_${Date.now()}_${Math.random().toString(36).slice(2)}`);
  fs.mkdirSync(d, { recursive: true });
  return d;
}

function runScriptSubcommand(command: 'self-host' | 'verify', scriptName: string): string {
  const parent = tmpDir();
  cleanup.push(parent);
  const checkout = path.join(parent, 'checkout space $(printf injected) ; literal');
  const scripts = path.join(checkout, 'scripts');
  fs.mkdirSync(scripts, { recursive: true });
  fs.cpSync(path.join(ROOT, 'src'), path.join(checkout, 'src'), { recursive: true });
  fs.symlinkSync(path.join(ROOT, 'node_modules'), path.join(checkout, 'node_modules'), 'dir');
  fs.writeFileSync(path.join(checkout, 'package.json'), '{"type":"module"}\n');
  fs.writeFileSync(path.join(scripts, scriptName), `printf 'script cwd: %s\\n' "$PWD"\n`);

  return execFileSync(
    process.execPath,
    [TSX_CLI, path.join(checkout, 'src', 'cli.ts'), command],
    execOpts,
  ).toString();
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
    const out = runCli(['--help'], execOpts).toString();
    expect(out).toContain('tslean');
    expect(out).toContain('compile');
    expect(out).toContain('self-host');
    expect(out).toContain('verify');
    expect(out).toContain('init');
  });

  it('-h shows usage', () => {
    const out = runCli(['-h'], execOpts).toString();
    expect(out).toContain('compile');
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
});

describe('CLI: script subcommands', () => {
  it('runs the self-host script from a checkout path with shell metacharacters', () => {
    const out = runScriptSubcommand('self-host', 'self-host.sh');
    expect(out).toContain('script cwd: ');
    expect(out).toContain('checkout space $(printf injected) ; literal');
  });

  it('runs the fixpoint script from a checkout path with shell metacharacters', () => {
    const out = runScriptSubcommand('verify', 'fixpoint-verify.sh');
    expect(out).toContain('script cwd: ');
    expect(out).toContain('checkout space $(printf injected) ; literal');
  });
});

// ─── compile subcommand: single file ─────────────────────────────────────────

describe('CLI: compile single file', () => {
  it('compile <file> -o <out> produces Lean', () => {
    const out = tmpFile();
    cleanup.push(out);
    runCli(['compile', path.join(FIX, 'basic/hello.ts'), '-o', out], execOpts);
    const code = fs.readFileSync(out, 'utf8');
    expect(code).toContain('open TSLean');
    expect(code).toContain('def greet');
  });

  it('compile with --output (long form)', () => {
    const out = tmpFile();
    cleanup.push(out);
    runCli(['compile', path.join(FIX, 'basic/hello.ts'), '--output', out], execOpts);
    expect(fs.existsSync(out)).toBe(true);
  });

  it('compile with --verify adds obligations', () => {
    const out = tmpFile();
    cleanup.push(out);
    const stdout = runCli(['compile', path.join(FIX, 'effects/exceptions.ts'), '-o', out, '--verify'], execOpts).toString();
    const code = fs.readFileSync(out, 'utf8');
    expect(code).toContain('open TSLean');
  });

  it('compile missing file exits with error', () => {
    expect(() => {
      runCli(['compile', 'nonexistent.ts', '-o', '/tmp/nope.lean'], { ...execOpts, stdio: 'pipe' });
    }).toThrow();
  });
});

// ─── compile subcommand: directory ───────────────────────────────────────────

describe('CLI: compile directory', () => {
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

  it('compile <dir> -o <outdir> transpiles all .ts files', () => {
    const outDir = tmpDir();
    cleanup.push(outDir);
    const stdout = runCli(
      ['compile', path.join(FIX, 'basic/'), '-o', outDir, '--no-lakefile'], execOpts
    ).toString();
    expect(stdout).toContain('file(s) transpiled');
    const leans = findLean(outDir);
    expect(leans).toContain('Hello.lean');
    expect(leans).toContain('Interfaces.lean');
    expect(leans).toContain('Classes.lean');
  });

  it('compile detects directory input without --project flag', () => {
    const outDir = tmpDir();
    cleanup.push(outDir);
    const stdout = runCli(
      ['compile', path.join(FIX, 'basic'), '-o', outDir, '--no-lakefile'], execOpts
    ).toString();
    expect(stdout).toContain('file(s) transpiled');
  });
});

// ─── Legacy mode (backward compat) ──────────────────────────────────────────

describe('CLI: legacy mode', () => {
  it('positional <file> -o <out> still works', () => {
    const out = tmpFile();
    cleanup.push(out);
    runCli([path.join(FIX, 'basic/hello.ts'), '-o', out], execOpts);
    const code = fs.readFileSync(out, 'utf8');
    expect(code).toContain('open TSLean');
  });

  it('--project <dir> -o <out> still works', () => {
    const outDir = tmpDir();
    cleanup.push(outDir);
    runCli(['--project', path.join(FIX, 'basic/'), '-o', outDir, '--no-lakefile'], execOpts);
    // Files are in hierarchical module structure
    const findLean = (dir: string): string[] => {
      const out: string[] = [];
      if (!fs.existsSync(dir)) return out;
      for (const e of fs.readdirSync(dir, { withFileTypes: true })) {
        if (e.isDirectory()) out.push(...findLean(path.join(dir, e.name)));
        else if (e.name.endsWith('.lean')) out.push(e.name);
      }
      return out;
    };
    expect(findLean(outDir)).toContain('Hello.lean');
  });
});

// ─── init subcommand ─────────────────────────────────────────────────────────

describe('CLI: init', () => {
  it('creates tslean.json and src/example.ts', () => {
    const dir = tmpDir();
    cleanup.push(dir);
    runCli(['init', dir], execOpts);
    expect(fs.existsSync(path.join(dir, 'tslean.json'))).toBe(true);
    expect(fs.existsSync(path.join(dir, 'src', 'example.ts'))).toBe(true);
    expect(fs.existsSync(path.join(dir, 'lean'))).toBe(true);
    const config = JSON.parse(fs.readFileSync(path.join(dir, 'tslean.json'), 'utf8'));
    expect(config.compilerOptions.namespace).toBe('TSLean.Generated');
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
      runCli(['compile'], { ...execOpts, stdio: 'pipe' });
    }).toThrow();
  });
});
