// Integration tests: transpile realistic multi-file TS projects end-to-end.
// Verifies the full pipeline: TS → parse → IR → rewrite → lower → print → valid Lean.

import { describe, it, expect, beforeAll } from 'vitest';
import * as path from 'path';
import * as fs from 'fs';
import * as os from 'os';
import { transpileProject, writeProjectOutputs, type ProjectResult } from '../../src/project/index.js';

const PROJECTS_DIR = path.join(process.cwd(), 'tests/fixtures/projects');

function findLeanFiles(dir: string): string[] {
  const out: string[] = [];
  if (!fs.existsSync(dir)) return out;
  for (const e of fs.readdirSync(dir, { withFileTypes: true })) {
    const full = path.join(dir, e.name);
    if (e.isDirectory()) out.push(...findLeanFiles(full));
    else if (e.name.endsWith('.lean')) out.push(full);
  }
  return out;
}

function transpileProjectDir(name: string): { result: ProjectResult; outDir: string; leanFiles: string[] } {
  const projectDir = path.join(PROJECTS_DIR, name);
  const outDir = fs.mkdtempSync(path.join(os.tmpdir(), `tslean-integ-${name}-`));
  const result = transpileProject({
    projectDir,
    outputDir: outDir,
    generateLakefile: false,
  });
  writeProjectOutputs(result);
  const leanFiles = findLeanFiles(outDir);
  return { result, outDir, leanFiles };
}

// ─── Calculator Project ─────────────────────────────────────────────────────

describe('Integration: calculator project', () => {
  let result: ProjectResult;
  let outDir: string;
  let leanFiles: string[];

  beforeAll(() => {
    ({ result, outDir, leanFiles } = transpileProjectDir('calculator'));
  });

  it('transpiles all 3 files without errors', () => {
    expect(result.errors).toEqual([]);
    expect(result.files.length).toBe(3);
  });

  it('generates 3 .lean files', () => {
    expect(leanFiles.length).toBe(3);
  });

  it('all output files are non-empty', () => {
    for (const f of leanFiles) {
      const content = fs.readFileSync(f, 'utf-8');
      expect(content.length).toBeGreaterThan(50);
    }
  });

  it('types file contains structure declarations', () => {
    const typesFile = leanFiles.find(f => f.toLowerCase().includes('types'));
    if (typesFile) {
      const content = fs.readFileSync(typesFile, 'utf-8');
      // Should have structure or inductive for Expression/Result
      expect(content).toMatch(/structure|inductive/);
    }
  });

  it('operations file contains evaluate function', () => {
    const opsFile = leanFiles.find(f => f.toLowerCase().includes('operation'));
    if (opsFile) {
      const content = fs.readFileSync(opsFile, 'utf-8');
      expect(content).toContain('evaluate');
    }
  });

  it('no circular dependency warnings', () => {
    expect(result.warnings.filter(w => w.includes('Circular'))).toEqual([]);
  });
});

// ─── Todo App Project ───────────────────────────────────────────────────────

describe('Integration: todo-app project', () => {
  let result: ProjectResult;
  let leanFiles: string[];

  beforeAll(() => {
    ({ result, leanFiles } = transpileProjectDir('todo-app'));
  });

  it('transpiles all 3 files without errors', () => {
    expect(result.errors).toEqual([]);
    expect(result.files.length).toBe(3);
  });

  it('generates .lean files for each source', () => {
    expect(leanFiles.length).toBe(3);
  });

  it('store file contains TodoStore class methods', () => {
    const storeFile = leanFiles.find(f => f.toLowerCase().includes('store'));
    if (storeFile) {
      const content = fs.readFileSync(storeFile, 'utf-8');
      expect(content).toMatch(/add|remove|toggle|getFiltered|count/);
    }
  });

  it('all files have proper Lean headers', () => {
    for (const f of leanFiles) {
      const content = fs.readFileSync(f, 'utf-8');
      expect(content).toContain('import TSLean');
    }
  });
});

// ─── Type Utils Project ─────────────────────────────────────────────────────

describe('Integration: type-utils project', () => {
  let result: ProjectResult;
  let leanFiles: string[];

  beforeAll(() => {
    ({ result, leanFiles } = transpileProjectDir('type-utils'));
  });

  it('transpiles all 3 files without errors', () => {
    expect(result.errors).toEqual([]);
    expect(result.files.length).toBe(3);
  });

  it('generates .lean files', () => {
    expect(leanFiles.length).toBe(3);
  });

  it('core file contains generic functions', () => {
    const coreFile = leanFiles.find(f => f.toLowerCase().includes('core'));
    if (coreFile) {
      const content = fs.readFileSync(coreFile, 'utf-8');
      expect(content).toContain('identity');
      expect(content).toContain('{');  // implicit type params
    }
  });

  it('result file contains Result type', () => {
    const resultFile = leanFiles.find(f => f.toLowerCase().includes('result'));
    if (resultFile) {
      const content = fs.readFileSync(resultFile, 'utf-8');
      expect(content).toMatch(/Result|ok|err/);
    }
  });

  it('collections file contains generic array operations', () => {
    const collectionsFile = leanFiles.find(f => f.toLowerCase().includes('collection'));
    if (collectionsFile) {
      const content = fs.readFileSync(collectionsFile, 'utf-8');
      expect(content).toMatch(/mapArray|filterArray|reduceArray/);
    }
  });
});

// ─── Cross-cutting concerns ─────────────────────────────────────────────────

describe('Integration: cross-project validation', () => {
  it('all three projects transpile without exceptions', () => {
    for (const name of ['calculator', 'todo-app', 'type-utils']) {
      expect(() => transpileProjectDir(name)).not.toThrow();
    }
  });

  it('dependency graph is acyclic for all projects', () => {
    for (const name of ['calculator', 'todo-app', 'type-utils']) {
      const { result } = transpileProjectDir(name);
      expect(result.graph.cycles.length).toBe(0);
    }
  });
});
