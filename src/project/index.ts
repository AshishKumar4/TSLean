// Project mode: multi-file transpilation with dependency graph and shared type checker.
// Reads tsconfig.json or discovers files, builds the import graph, topologically sorts,
// and emits one .lean file per source with correct cross-file imports and a lakefile.

import * as path from 'path';
import * as fs from 'fs';
import { parseFile } from '../parser/index.js';
import { rewriteModule } from '../rewrite/index.js';
import { generateLean } from '../codegen/index.js';
import { generateVerification } from '../verification/index.js';
import type { IRModule } from '../ir/types.js';
import { capitalize } from '../utils.js';
import { fileToLeanModule, fileToLeanPath, type ModuleResolverOpts } from './module-resolver.js';
import { buildDependencyGraph, formatCycles, type DependencyGraph } from './dependency-graph.js';
import { readProjectDir, readProjectConfig, toResolverOpts, type ProjectConfig } from './reader.js';
import { writeLakefiles, type LakefileOpts } from './lakefile-gen.js';

// ─── Public API ───────────────────────────────────────────────────────────────

export interface ProjectOpts {
  projectDir: string;
  outputDir?: string;
  tsconfigPath?: string;
  verify?: boolean;
  rootNS?: string;
  generateLakefile?: boolean;
  leanVersion?: string;
  onProgress?: (step: string, current: number, total: number) => void;
}

export interface ProjectResult {
  files: Array<{ tsFile: string; leanFile: string; module: string; content: string }>;
  errors: string[];
  warnings: string[];
  graph: DependencyGraph;
  config: ProjectConfig;
}

export function transpileProject(opts: ProjectOpts): ProjectResult {
  const { projectDir, verify = false, generateLakefile: genLake = true, leanVersion = 'v4.29.0' } = opts;
  const progress = opts.onProgress ?? (() => {});

  // Phase 1: Read configuration
  progress('Reading project configuration', 0, 0);
  const config = opts.tsconfigPath
    ? readProjectConfig(opts.tsconfigPath, { outDir: opts.outputDir, namespace: opts.rootNS })
    : readProjectDir(projectDir, { outDir: opts.outputDir, namespace: opts.rootNS });

  if (config.files.length === 0) {
    return { files: [], errors: [`No .ts files found in ${projectDir}`], warnings: [], graph: { nodes: new Map(), order: [], cycles: [] }, config };
  }

  // Phase 2: Build dependency graph
  progress('Building dependency graph', 1, config.files.length + 3);
  const resolverOpts = toResolverOpts(config);
  const graph = buildDependencyGraph(config.files, resolverOpts);

  const warnings: string[] = [];
  if (graph.cycles.length > 0) {
    warnings.push(...formatCycles(graph.cycles));
  }

  // Phase 3: Transpile files in topological order
  const results: ProjectResult['files'] = [];
  const errors: string[] = [];
  const total = graph.order.length;

  for (let i = 0; i < total; i++) {
    const mod = graph.order[i];
    const node = graph.nodes.get(mod);
    if (!node) continue;

    progress(`Transpiling ${path.basename(node.filePath)}`, i + 2, total + 3);

    try {
      const src = fs.readFileSync(node.filePath, 'utf-8');
      const parsed = parseFile({ fileName: node.filePath, sourceText: src });
      // Use project-level module name instead of parser's basename-only version
      const fixed = fixModuleName(parsed, node.leanModule, resolverOpts);
      const rw = rewriteModule(fixed);
      let code = generateLean(rw);
      if (verify) {
        const { leanCode } = generateVerification(rw);
        if (leanCode) code += '\n\n-- Verification\n' + leanCode;
      }
      const leanFile = fileToLeanPath(node.filePath, resolverOpts, config.outDir);
      results.push({ tsFile: node.filePath, leanFile, module: node.leanModule, content: code });
    } catch (err) {
      errors.push(`${node.filePath}: ${(err as Error).message}`);
    }
  }

  // Phase 4: Generate lakefile
  if (genLake && results.length > 0) {
    progress('Generating lakefile', total + 2, total + 3);
    const lakeOpts: LakefileOpts = {
      name: config.leanNamespace,
      rootNS: config.leanNamespace,
      modules: results.map(r => r.module),
      outDir: config.outDir,
      leanVersion,
    };
    writeLakefiles(lakeOpts);
  }

  progress('Done', total + 3, total + 3);
  return { files: results, errors, warnings, graph, config };
}

export function writeProjectOutputs(result: ProjectResult): void {
  for (const { leanFile, content } of result.files) {
    fs.mkdirSync(path.dirname(leanFile), { recursive: true });
    fs.writeFileSync(leanFile, content, 'utf-8');
  }
}

// ─── Helpers ──────────────────────────────────────────────────────────────────

function fixModuleName(mod: IRModule, leanModule: string, resolverOpts: ModuleResolverOpts): IRModule {
  const fixedImports = mod.imports.map(imp => {
    if (imp.module.startsWith('TSLean.') || imp.module.startsWith('Lean')) return imp;
    // External packages stay as TSLean.External.*
    if (imp.module.startsWith('TSLean.External.')) return imp;
    return imp;
  });
  return { ...mod, name: leanModule, imports: fixedImports };
}

// Legacy exports for backwards compatibility
export { fileToLeanModule, fileToLeanPath } from './module-resolver.js';
export { buildDependencyGraph, formatCycles } from './dependency-graph.js';
export { readProjectDir, readProjectConfig } from './reader.js';
export { writeLakefiles } from './lakefile-gen.js';

// Legacy helpers used by old project mode
export function toLeanPath(tsFile: string, projectDir: string, outputDir: string, rootNS = 'TSLean.Generated'): string {
  const rel = path.relative(projectDir, tsFile);
  const parts = rel.replace(/\.ts$/, '').split(path.sep).map(p => p.split(/[-_]/).map(capitalize).join(''));
  return path.join(outputDir, ...parts) + '.lean';
}

export function toModuleName(tsFile: string, projectDir: string, rootNS = 'TSLean.Generated'): string {
  const rel = path.relative(projectDir, tsFile);
  const parts = rel.replace(/\.ts$/, '').split(path.sep).filter(Boolean)
    .map(p => p.split(/[-_]/).map(capitalize).join(''));
  return `${rootNS}.${parts.join('.')}`;
}
