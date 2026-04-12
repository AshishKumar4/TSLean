// Project configuration reader: parse tsconfig.json, discover files, create shared TypeChecker.
// Uses the TS compiler API for correct include/exclude/paths resolution.

import * as ts from 'typescript';
import * as path from 'path';
import * as fs from 'fs';
import type { ModuleResolverOpts } from './module-resolver.js';

// ─── Types ──────────────────────────────────────────────────────────────────────

export interface ProjectConfig {
  rootDir: string;               // absolute path to project root
  sourceDir: string;             // rootDir from tsconfig (for module path computation)
  outDir: string;                // Lean output directory
  baseUrl?: string;              // for path alias resolution
  pathAliases?: Record<string, string[]>;
  files: string[];               // discovered source files (absolute paths)
  leanNamespace: string;         // root Lean namespace
}

export interface SharedCompiler {
  program: ts.Program;
  checker: ts.TypeChecker;
  sourceFiles: Map<string, ts.SourceFile>;
}

// ─── tsconfig.json parsing ──────────────────────────────────────────────────────

/** Read and resolve a tsconfig.json, discovering all included source files. */
export function readProjectConfig(
  tsconfigPath: string,
  opts: { outDir?: string; namespace?: string } = {},
): ProjectConfig {
  const configPath = path.resolve(tsconfigPath);
  if (!fs.existsSync(configPath)) {
    throw new Error(`tsconfig.json not found: ${configPath}`);
  }

  const configDir = path.dirname(configPath);
  const configText = fs.readFileSync(configPath, 'utf-8');
  const { config, error } = ts.parseConfigFileTextToJson(configPath, configText);
  if (error) {
    throw new Error(`Failed to parse ${configPath}: ${ts.flattenDiagnosticMessageText(error.messageText, '\n')}`);
  }

  const parsed = ts.parseJsonConfigFileContent(config, ts.sys, configDir, undefined, configPath);
  if (parsed.errors.length > 0) {
    const msgs = parsed.errors.map(d => ts.flattenDiagnosticMessageText(d.messageText, '\n'));
    throw new Error(`tsconfig.json errors:\n${msgs.join('\n')}`);
  }

  // Determine rootDir: explicit in tsconfig or inferred from configDir
  const sourceDir = parsed.options.rootDir
    ? path.resolve(configDir, parsed.options.rootDir)
    : configDir;

  // Filter to .ts/.tsx files, exclude .d.ts and node_modules
  const files = parsed.fileNames.filter(f =>
    (f.endsWith('.ts') || f.endsWith('.tsx')) &&
    !f.endsWith('.d.ts') &&
    !f.includes('node_modules'),
  );

  // Extract path aliases
  const pathAliases = parsed.options.paths;
  const baseUrl = parsed.options.baseUrl
    ? path.resolve(configDir, parsed.options.baseUrl)
    : undefined;

  // Determine namespace: from package.json name, or explicit option
  const leanNamespace = opts.namespace ?? inferNamespace(configDir);

  return {
    rootDir: configDir,
    sourceDir,
    outDir: opts.outDir ?? path.join(configDir, 'lean', 'Generated'),
    baseUrl,
    pathAliases,
    files: files.map(f => path.resolve(f)),
    leanNamespace,
  };
}

/** Read project config from a directory (auto-discover tsconfig.json). */
export function readProjectDir(
  projectDir: string,
  opts: { outDir?: string; namespace?: string } = {},
): ProjectConfig {
  const dir = path.resolve(projectDir);
  const tsconfigPath = path.join(dir, 'tsconfig.json');

  if (fs.existsSync(tsconfigPath)) {
    return readProjectConfig(tsconfigPath, opts);
  }

  // Fallback: discover .ts files manually (no tsconfig)
  if (!fs.existsSync(dir)) return {
    rootDir: dir, sourceDir: dir,
    outDir: opts.outDir ?? path.join(dir, 'lean', 'Generated'),
    files: [], leanNamespace: opts.namespace ?? 'Project',
  };
  const files = discoverTsFiles(dir);
  return {
    rootDir: dir,
    sourceDir: dir,
    outDir: opts.outDir ?? path.join(dir, 'lean', 'Generated'),
    files,
    leanNamespace: opts.namespace ?? inferNamespace(dir),
  };
}

// ─── Shared TypeChecker ─────────────────────────────────────────────────────────

/** Create a single ts.Program for all project files, enabling cross-file type resolution. */
export function createSharedCompiler(config: ProjectConfig): SharedCompiler {
  const compilerOpts: ts.CompilerOptions = {
    target: ts.ScriptTarget.ES2022,
    module: ts.ModuleKind.NodeNext,
    moduleResolution: ts.ModuleResolutionKind.NodeNext,
    strict: true,
    skipLibCheck: true,
    rootDir: config.sourceDir,
    baseUrl: config.baseUrl,
    paths: config.pathAliases,
  };

  const host = ts.createCompilerHost(compilerOpts);
  const program = ts.createProgram(config.files, compilerOpts, host);
  const checker = program.getTypeChecker();

  const sourceFiles = new Map<string, ts.SourceFile>();
  for (const f of config.files) {
    const sf = program.getSourceFile(f);
    if (sf) sourceFiles.set(f, sf);
  }

  return { program, checker, sourceFiles };
}

/** Convert a ProjectConfig to ModuleResolverOpts. */
export function toResolverOpts(config: ProjectConfig): ModuleResolverOpts {
  return {
    rootDir: config.sourceDir,
    rootNS: config.leanNamespace,
    pathAliases: config.pathAliases,
    baseUrl: config.baseUrl,
  };
}

// ─── Helpers ────────────────────────────────────────────────────────────────────

const IGNORED_DIRS = new Set(['node_modules', '.git', 'dist', 'build', 'out', '.next', '.tslean-cache']);

function discoverTsFiles(dir: string): string[] {
  const out: string[] = [];
  for (const e of fs.readdirSync(dir, { withFileTypes: true })) {
    const full = path.join(dir, e.name);
    if (e.isDirectory() && !IGNORED_DIRS.has(e.name)) out.push(...discoverTsFiles(full));
    else if (e.isFile() && e.name.endsWith('.ts') && !e.name.endsWith('.d.ts')) out.push(full);
  }
  return out.sort();
}

function inferNamespace(projectDir: string): string {
  const pkgPath = path.join(projectDir, 'package.json');
  if (fs.existsSync(pkgPath)) {
    try {
      const pkg = JSON.parse(fs.readFileSync(pkgPath, 'utf-8'));
      if (pkg.name) {
        // @scope/name → ScopeName, my-project → MyProject
        const clean = pkg.name.replace(/^@/, '').replace(/[^a-zA-Z0-9/]/g, ' ');
        const parts = clean.split(/[\s/]+/).filter(Boolean);
        return parts.map((p: string) => p.charAt(0).toUpperCase() + p.slice(1)).join('');
      }
    } catch { /* ignore parse errors */ }
  }
  // Fallback: directory name
  const base = path.basename(projectDir);
  return base.charAt(0).toUpperCase() + base.slice(1).replace(/[-_]/g, '');
}
