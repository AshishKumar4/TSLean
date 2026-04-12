// Build and validate the module dependency graph.
// Implements Tarjan's SCC algorithm for cycle detection and Kahn's algorithm for topological sort.

import * as ts from 'typescript';
import * as path from 'path';
import { fileToLeanModule, resolveImportModule, isExternalModule, type ModuleResolverOpts } from './module-resolver.js';

// ─── Types ──────────────────────────────────────────────────────────────────────

export interface ModuleNode {
  filePath: string;          // absolute path to .ts file
  leanModule: string;        // Lean module name (e.g., "MyProject.Components.Button")
  imports: string[];         // Lean module names of dependencies (within the project)
  importedBy: string[];      // reverse dependencies
  isBarrel: boolean;         // true for index.ts files
  isTypeOnly: Set<string>;   // imports that are type-only
}

export interface DependencyGraph {
  nodes: Map<string, ModuleNode>;   // keyed by leanModule
  order: string[];                  // topological order (dependencies first)
  cycles: string[][];               // detected cycles
}

// ─── Graph construction ─────────────────────────────────────────────────────────

/** Build the dependency graph from a set of TypeScript source files. */
export function buildDependencyGraph(
  files: string[],
  opts: ModuleResolverOpts,
): DependencyGraph {
  const nodes = new Map<string, ModuleNode>();
  const projectModules = new Set<string>();

  // Phase 1: register all project files
  for (const f of files) {
    const mod = fileToLeanModule(f, opts);
    projectModules.add(mod);
    nodes.set(mod, {
      filePath: f,
      leanModule: mod,
      imports: [],
      importedBy: [],
      isBarrel: path.basename(f).replace(/\.(ts|tsx)$/, '') === 'index',
      isTypeOnly: new Set(),
    });
  }

  // Phase 2: extract imports from each file using TS compiler
  for (const f of files) {
    const mod = fileToLeanModule(f, opts);
    const node = nodes.get(mod)!;
    const imports = extractImports(f, opts);

    for (const imp of imports) {
      if (!projectModules.has(imp.module)) continue;  // skip external
      if (!node.imports.includes(imp.module) && imp.module !== mod) {
        node.imports.push(imp.module);
        if (imp.isTypeOnly) node.isTypeOnly.add(imp.module);
        const target = nodes.get(imp.module);
        if (target && !target.importedBy.includes(mod)) {
          target.importedBy.push(mod);
        }
      }
    }
  }

  // Phase 3: detect cycles and compute topological order
  const cycles = findCycles(nodes);
  const order = topologicalSort(nodes);

  return { nodes, order, cycles };
}

// ─── Import extraction ──────────────────────────────────────────────────────────

interface RawImport {
  module: string;
  isTypeOnly: boolean;
}

/** Extract import module specifiers from a TS file using the compiler API. */
function extractImports(filePath: string, opts: ModuleResolverOpts): RawImport[] {
  const sourceText = ts.sys.readFile(filePath) ?? '';
  const sf = ts.createSourceFile(filePath, sourceText, ts.ScriptTarget.ES2022, true);
  const result: RawImport[] = [];

  for (const stmt of sf.statements) {
    if (ts.isImportDeclaration(stmt) && ts.isStringLiteral(stmt.moduleSpecifier)) {
      const spec = stmt.moduleSpecifier.text;
      const isTypeOnly = !!(stmt.importClause?.isTypeOnly);
      const resolved = resolveImportModule(spec, filePath, opts);
      if (resolved && !isExternalModule(resolved)) {
        result.push({ module: resolved, isTypeOnly });
      }
    }

    // export { X } from './mod' and export * from './mod'
    if (ts.isExportDeclaration(stmt) && stmt.moduleSpecifier && ts.isStringLiteral(stmt.moduleSpecifier)) {
      const spec = stmt.moduleSpecifier.text;
      const isTypeOnly = !!stmt.isTypeOnly;
      const resolved = resolveImportModule(spec, filePath, opts);
      if (resolved && !isExternalModule(resolved)) {
        result.push({ module: resolved, isTypeOnly });
      }
    }
  }

  return result;
}

// ─── Cycle detection (Tarjan's SCC) ─────────────────────────────────────────────

function findCycles(nodes: Map<string, ModuleNode>): string[][] {
  let index = 0;
  const stack: string[] = [];
  const onStack = new Set<string>();
  const indices = new Map<string, number>();
  const lowlinks = new Map<string, number>();
  const sccs: string[][] = [];

  function strongConnect(v: string) {
    indices.set(v, index);
    lowlinks.set(v, index);
    index++;
    stack.push(v);
    onStack.add(v);

    const node = nodes.get(v);
    if (node) {
      for (const w of node.imports) {
        if (!indices.has(w)) {
          strongConnect(w);
          lowlinks.set(v, Math.min(lowlinks.get(v)!, lowlinks.get(w)!));
        } else if (onStack.has(w)) {
          lowlinks.set(v, Math.min(lowlinks.get(v)!, indices.get(w)!));
        }
      }
    }

    if (lowlinks.get(v) === indices.get(v)) {
      const scc: string[] = [];
      let w: string;
      do {
        w = stack.pop()!;
        onStack.delete(w);
        scc.push(w);
      } while (w !== v);
      if (scc.length > 1) sccs.push(scc);
    }
  }

  for (const v of nodes.keys()) {
    if (!indices.has(v)) strongConnect(v);
  }

  return sccs;
}

// ─── Topological sort (Kahn's algorithm) ────────────────────────────────────────

function topologicalSort(nodes: Map<string, ModuleNode>): string[] {
  const inDegree = new Map<string, number>();
  for (const [mod, node] of nodes) {
    if (!inDegree.has(mod)) inDegree.set(mod, 0);
    for (const dep of node.imports) {
      inDegree.set(dep, (inDegree.get(dep) ?? 0) + 1);
    }
  }

  // Note: inDegree counts how many modules IMPORT each module.
  // We want dependencies first, so we start with modules nobody imports FROM.
  // Actually for Kahn's: inDegree = number of dependencies a module has.
  // Let me recompute correctly.
  const depCount = new Map<string, number>();
  for (const [mod, node] of nodes) {
    depCount.set(mod, node.imports.length);
  }

  const queue: string[] = [];
  for (const [mod, count] of depCount) {
    if (count === 0) queue.push(mod);
  }

  const order: string[] = [];
  while (queue.length > 0) {
    queue.sort(); // deterministic ordering for reproducibility
    const mod = queue.shift()!;
    order.push(mod);
    const node = nodes.get(mod);
    if (node) {
      for (const dependent of node.importedBy) {
        const newCount = depCount.get(dependent)! - 1;
        depCount.set(dependent, newCount);
        if (newCount === 0) queue.push(dependent);
      }
    }
  }

  // If order doesn't contain all nodes, there are cycles (already detected by Tarjan)
  // Include remaining nodes at the end to avoid losing them
  for (const mod of nodes.keys()) {
    if (!order.includes(mod)) order.push(mod);
  }

  return order;
}

/** Format cycle information for error reporting. */
export function formatCycles(cycles: string[][]): string[] {
  return cycles.map(cycle => {
    const display = [...cycle, cycle[0]].join(' → ');
    return `Circular dependency: ${display}`;
  });
}
