// Project configuration reader: parse tsconfig.json, discover files, open the shared checker.
// Uses the TS compiler session for correct include/exclude/paths resolution.

import * as path from 'path';
import * as fs from 'fs';
import type { Checker, Program, SourceFile } from '../typescript-api/index.js';
import { configuration, openProject, renderDiagnostics } from '../typescript-api/session.js';
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
  program: Program;
  checker: Checker;
  sourceFiles: Map<string, SourceFile>;
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
  // The compiler resolves the configuration and reports what it objected to, and both a malformed
  // file and a bad option arrive through that one channel: the session answers with resolved
  // options either way, so a truncated `tsconfig.json` reads as "no options at all" rather than as
  // a failure, and these objections are what stands between a broken configuration and a build
  // that silently used defaults.
  const parsed = configuration(configPath);
  if (parsed.diagnostics.length > 0) {
    throw new Error(`tsconfig.json errors:\n${renderDiagnostics(parsed.diagnostics, '\n')}`);
  }

  // Determine rootDir: explicit in tsconfig or inferred from configDir
  const rootDirOption = parsed.options['rootDir'];
  if (rootDirOption !== undefined && typeof rootDirOption !== 'string') {
    throw new Error(`tsconfig.json rootDir must be a directory path: ${configPath}`);
  }
  const sourceDir = rootDirOption ? path.resolve(configDir, rootDirOption) : configDir;

  // Filter to .ts/.tsx files, exclude .d.ts and node_modules
  const files = parsed.fileNames.filter(f =>
    (f.endsWith('.ts') || f.endsWith('.tsx')) &&
    !f.endsWith('.d.ts') &&
    !f.includes('node_modules'),
  );

  // Extract path aliases
  const pathAliases = readPathAliases(parsed.options, configPath);
  const baseUrlOption = parsed.options['baseUrl'];
  if (baseUrlOption !== undefined && typeof baseUrlOption !== 'string') {
    throw new Error(`tsconfig.json baseUrl must be a directory path: ${configPath}`);
  }
  const baseUrl = baseUrlOption ? path.resolve(configDir, baseUrlOption) : undefined;

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

// ─── Shared checker ─────────────────────────────────────────────────────────────

/**
 * Open one project over all project files, enabling cross-file type resolution. The project stays
 * open for the caller's lifetime: the program, the checker and every source file below are read
 * through it, so it is the caller's own scope that decides when the reading is done.
 */
export function createSharedCompiler(config: ProjectConfig): SharedCompiler {
  const project = openProject({
    files: config.files,
    settings: {
      target: 'es2022',
      module: 'nodenext',
      moduleResolution: 'nodenext',
      strict: true,
      skipLibCheck: true,
      rootDir: config.sourceDir,
      baseUrl: config.baseUrl,
      paths: config.pathAliases,
    },
  });

  const sourceFiles = new Map<string, SourceFile>();
  for (const f of config.files) {
    const sf = project.sourceFile(f);
    if (sf) sourceFiles.set(f, sf);
  }

  return { program: project.program, checker: project.checker, sourceFiles };
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

/**
 * The `paths` table the compiler resolved. The session answers with the configuration's own values
 * as unknowns, so the shape is checked here rather than assumed: an alias that is not a list of
 * strings is a configuration the module resolver cannot honour, and refusing it beats resolving an
 * import against something that is not a path.
 */
function readPathAliases(
  options: Readonly<Record<string, unknown>>,
  configPath: string,
): Record<string, string[]> | undefined {
  const configured = options['paths'];
  if (configured === undefined) return undefined;
  if (typeof configured !== 'object' || configured === null || Array.isArray(configured)) {
    throw new Error(`tsconfig.json paths must be an object: ${configPath}`);
  }
  const entries: readonly (readonly [string, unknown])[] = Object.entries(configured);
  const aliases: Record<string, string[]> = {};
  for (const [pattern, targets] of entries) {
    if (!Array.isArray(targets)) {
      throw new Error(`tsconfig.json paths entry ${pattern} must be a list of paths: ${configPath}`);
    }
    aliases[pattern] = targets.map((target: unknown) => {
      if (typeof target !== 'string') {
        throw new Error(`tsconfig.json paths entry ${pattern} must be a list of paths: ${configPath}`);
      }
      return target;
    });
  }
  return aliases;
}

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
