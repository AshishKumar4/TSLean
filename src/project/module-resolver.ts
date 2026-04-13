// Unified file path → Lean module name resolution.
// Single source of truth for all module naming across the transpiler.

import * as path from 'path';
import * as fs from 'fs';
import { capitalize } from '../utils.js';

// Lean 4 reserved words that would collide with module/namespace names.
const LEAN_RESERVED = new Set([
  'String', 'Nat', 'Int', 'Float', 'Bool', 'Unit', 'IO', 'Type', 'Prop',
  'Array', 'List', 'Option', 'Except', 'True', 'False', 'And', 'Or', 'Not',
  'Set', 'Map', 'Monad', 'Functor', 'Pure', 'Bind',
]);

/** Convert a kebab-or-snake-cased path segment to PascalCase.
 *  `auth-service` → `AuthService`, `counter_do` → `CounterDo` */
function segmentToPascal(seg: string): string {
  return seg.split(/[-_]/).map(capitalize).join('');
}

/** Escape a Lean module name segment that collides with a reserved word. */
function escapeLeanSegment(seg: string): string {
  return LEAN_RESERVED.has(seg) ? seg + '_' : seg;
}

/** Options for module resolution. */
export interface ModuleResolverOpts {
  rootDir: string;       // absolute path to project root (e.g., the dir containing tsconfig.json)
  rootNS: string;        // root Lean namespace (e.g., 'MyProject')
  pathAliases?: Record<string, string[]>;  // from tsconfig.json paths
  baseUrl?: string;      // from tsconfig.json baseUrl
}

/**
 * Convert a TypeScript file path to a Lean module name.
 *
 *   src/components/Button.tsx → MyProject.Components.Button
 *   src/utils/index.ts        → MyProject.Utils
 *   src/auth-service.ts       → MyProject.AuthService
 */
export function fileToLeanModule(filePath: string, opts: ModuleResolverOpts): string {
  const rel = path.relative(opts.rootDir, filePath);
  const stripped = rel
    .replace(/\.(ts|tsx|js|jsx)$/, '')
    .replace(/(^|[/\\])index$/, '$1')  // index files → parent directory name
    .replace(/[/\\]$/, '');            // remove trailing separator

  if (!stripped) return opts.rootNS;  // rootDir/index.ts → root module

  const segments = stripped.split(path.sep)
    .filter(Boolean)
    .map(s => escapeLeanSegment(segmentToPascal(s)));

  return `${opts.rootNS}.${segments.join('.')}`;
}

/**
 * Convert a Lean module name to a filesystem path (relative to output dir).
 *
 *   MyProject.Components.Button → MyProject/Components/Button.lean
 */
export function leanModuleToPath(mod: string): string {
  return mod.split('.').join(path.sep) + '.lean';
}

/**
 * Convert a TypeScript file path to its output Lean file path.
 */
export function fileToLeanPath(filePath: string, opts: ModuleResolverOpts, outDir: string): string {
  const mod = fileToLeanModule(filePath, opts);
  return path.join(outDir, leanModuleToPath(mod));
}

/**
 * Resolve a TypeScript import specifier to a Lean module name.
 *
 * Handles:
 * - Relative: `'./utils'` → resolve against importer, then fileToLeanModule
 * - Absolute with path aliases: `'@/components/Button'` → resolve alias, then fileToLeanModule
 * - External packages: `'zod'` → `TSLean.Runtime.Validation` (known), `'foo'` → `TSLean.External.Foo`
 */
export function resolveImportModule(
  specifier: string,
  importerPath: string,
  opts: ModuleResolverOpts,
): string | null {
  // Relative imports
  if (specifier.startsWith('.')) {
    const resolved = resolveRelativeImport(specifier, importerPath);
    if (resolved) return fileToLeanModule(resolved, opts);
    return null;
  }

  // Path alias resolution
  if (opts.pathAliases && opts.baseUrl) {
    const resolved = resolvePathAlias(specifier, opts.pathAliases, opts.baseUrl);
    if (resolved) return fileToLeanModule(resolved, opts);
  }

  // External package → TSLean.External namespace
  return externalModuleName(specifier);
}

/** Resolve a relative import specifier to an absolute file path. */
function resolveRelativeImport(specifier: string, importerPath: string): string | null {
  const dir = path.dirname(importerPath);
  const clean = specifier.replace(/\.(js|ts|tsx|jsx)$/, '');
  const candidates = [
    path.resolve(dir, clean + '.ts'),
    path.resolve(dir, clean + '.tsx'),
    path.resolve(dir, clean, 'index.ts'),
    path.resolve(dir, clean, 'index.tsx'),
  ];
  for (const c of candidates) {
    if (fs.existsSync(c)) return c;
  }
  return null;
}

/** Resolve a path alias (e.g. `@/components/Button` → absolute path). */
function resolvePathAlias(specifier: string, aliases: Record<string, string[]>, baseUrl: string): string | null {
  for (const [pattern, targets] of Object.entries(aliases)) {
    const prefix = pattern.replace(/\*$/, '');
    if (!specifier.startsWith(prefix)) continue;
    const rest = specifier.slice(prefix.length);
    for (const target of targets) {
      const targetPrefix = target.replace(/\*$/, '');
      const resolved = resolveRelativeImport(
        './' + targetPrefix + rest,
        path.join(baseUrl, '__alias_anchor__.ts'),
      );
      if (resolved) return resolved;
    }
  }
  return null;
}

// Well-known npm packages with TSLean runtime equivalents.
const KNOWN_EXTERNALS: Record<string, string> = {
  'zod': 'TSLean.Runtime.Validation',
  'uuid': 'TSLean.Stdlib.Uuid',
  'hono': 'TSLean.External.Hono',
};

/** Map an external npm package to a Lean module name. */
function externalModuleName(specifier: string): string {
  if (KNOWN_EXTERNALS[specifier]) return KNOWN_EXTERNALS[specifier];
  const parts = specifier
    .replace(/^@/, '')
    .split('/')
    .map(s => escapeLeanSegment(segmentToPascal(s)));
  return `TSLean.External.${parts.join('.')}`;
}

/** Check if a module name refers to an external (non-project) module. */
export function isExternalModule(leanModule: string): boolean {
  return leanModule.startsWith('TSLean.External.');
}
