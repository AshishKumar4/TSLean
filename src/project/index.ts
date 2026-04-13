// Project mode: multi-file transpilation.
// Discovers all .ts files, creates a single ts.Program, resolves the import
// graph, and emits one .lean file per source file with correct cross-file imports.

import * as ts from 'typescript';
import * as path from 'path';
import * as fs from 'fs';
import { parseFile } from '../parser/index.js';
import { rewriteModule } from '../rewrite/index.js';
import { generateLean } from '../codegen/index.js';
import { generateVerification } from '../verification/index.js';
import { IRModule, IRImport } from '../ir/types.js';
import { hasDOPattern, CF_AMBIENT, makeAmbientHost } from '../do-model/ambient.js';

// ─── Public API ───────────────────────────────────────────────────────────────

export interface ProjectOpts {
  projectDir: string;
  outputDir: string;
  verify?: boolean;
  rootNS?: string;
}

export interface ProjectResult {
  files: Array<{ tsFile: string; leanFile: string; content: string }>;
  errors: string[];
}

export function transpileProject(opts: ProjectOpts): ProjectResult {
  const { projectDir, outputDir, verify = false, rootNS = 'TSLean.Generated' } = opts;
  if (!fs.existsSync(projectDir)) {
    return { files: [], errors: [`Directory not found: ${projectDir}`] };
  }
  const tsFiles = discoverTs(projectDir);
  if (tsFiles.length === 0) return { files: [], errors: [`No .ts files in ${projectDir}`] };

  const results: ProjectResult['files'] = [];
  const errors: string[] = [];

  for (const f of tsFiles) {
    try {
      const src = fs.readFileSync(f, 'utf-8');
      const mod = parseFile({ fileName: f, sourceText: src });
      const rw  = rewriteModule(fixImports(mod, f, projectDir, rootNS));
      let code  = generateLean(rw);
      if (verify) {
        const { leanCode } = generateVerification(rw);
        if (leanCode) code += '\n\n-- Verification\n' + leanCode;
      }
      const lf = toLeanPath(f, projectDir, outputDir, rootNS);
      results.push({ tsFile: f, leanFile: lf, content: code });
    } catch (err) {
      errors.push(`${f}: ${(err as Error).message}`);
    }
  }

  return { files: results, errors };
}

export function writeProjectOutputs(result: ProjectResult): void {
  for (const { leanFile, content } of result.files) {
    fs.mkdirSync(path.dirname(leanFile), { recursive: true });
    fs.writeFileSync(leanFile, content, 'utf-8');
  }
}

// ─── File discovery ───────────────────────────────────────────────────────────

const IGNORED = new Set(['node_modules', '.git', 'dist', 'build', 'out', '.next']);

function discoverTs(dir: string): string[] {
  const out: string[] = [];
  for (const e of fs.readdirSync(dir, { withFileTypes: true })) {
    const full = path.join(dir, e.name);
    if (e.isDirectory() && !IGNORED.has(e.name)) out.push(...discoverTs(full));
    else if (e.isFile() && e.name.endsWith('.ts') && !e.name.endsWith('.d.ts')) out.push(full);
  }
  return out.sort();
}

// ─── Import resolution ────────────────────────────────────────────────────────

function fixImports(mod: IRModule, tsFile: string, rootDir: string, rootNS: string): IRModule {
  const fixed: IRImport[] = mod.imports.map(imp => {
    if (imp.module.startsWith('TSLean.') || imp.module.startsWith('Lean')) return imp;
    return { ...imp, module: relToLean(imp.module, tsFile, rootDir, rootNS) };
  });
  return { ...mod, imports: fixed };
}

function relToLean(spec: string, fromFile: string, rootDir: string, rootNS: string): string {
  const resolved = resolveSpec(spec, fromFile);
  if (!resolved) return specToLean(spec, rootNS);
  const rel = path.relative(rootDir, resolved);
  const parts = rel.replace(/\.ts$/, '').split(path.sep).filter(Boolean)
    .map(p => p.replace(/\.js$/, '').split(/[-_]/).map(cap).join(''));
  return `${rootNS}.${parts.join('.')}`;
}

function resolveSpec(spec: string, fromFile: string): string | null {
  const dir = path.dirname(fromFile);
  const clean = spec.replace(/\.js$/, '').replace(/\.ts$/, '');
  for (const c of [
    path.resolve(dir, clean + '.ts'),
    path.resolve(dir, clean, 'index.ts'),
    path.resolve(dir, spec),
  ]) { if (fs.existsSync(c)) return c; }
  return null;
}

function specToLean(spec: string, rootNS: string): string {
  const parts = spec.replace(/^[./]+/, '').replace(/\.(ts|js)$/, '')
    .split('/').filter(Boolean).map(p => p.split(/[-_]/).map(cap).join(''));
  return `${rootNS}.${parts.join('.')}`;
}

// ─── Path helpers ─────────────────────────────────────────────────────────────

export function toLeanPath(tsFile: string, projectDir: string, outputDir: string, rootNS = 'TSLean.Generated'): string {
  const rel   = path.relative(projectDir, tsFile);
  const parts = rel.replace(/\.ts$/, '').split(path.sep).map(p => p.split(/[-_]/).map(cap).join(''));
  return path.join(outputDir, ...parts) + '.lean';
}

export function toModuleName(tsFile: string, projectDir: string, rootNS = 'TSLean.Generated'): string {
  const rel   = path.relative(projectDir, tsFile);
  const parts = rel.replace(/\.ts$/, '').split(path.sep).filter(Boolean)
    .map(p => p.split(/[-_]/).map(cap).join(''));
  return `${rootNS}.${parts.join('.')}`;
}

function cap(s: string): string { return s ? s[0].toUpperCase() + s.slice(1) : s; }
