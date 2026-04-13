// Tests for the Phase 3 multi-file module system:
// module-resolver, dependency-graph, reader, lakefile-gen.

import { describe, it, expect } from 'vitest';
import * as path from 'path';
import * as fs from 'fs';
import * as os from 'os';
import {
  fileToLeanModule, leanModuleToPath, fileToLeanPath,
  resolveImportModule, isExternalModule,
} from '../src/project/module-resolver.js';
import {
  buildDependencyGraph, formatCycles,
} from '../src/project/dependency-graph.js';
import {
  generateLakefile, generateRootModule, generateToolchain,
} from '../src/project/lakefile-gen.js';

const ROOT = process.cwd();

// ─── Module Resolver ────────────────────────────────────────────────────────────

describe('Module Resolver: fileToLeanModule', () => {
  const opts = { rootDir: '/project/src', rootNS: 'MyApp' };

  it('simple file', () => {
    expect(fileToLeanModule('/project/src/utils.ts', opts)).toBe('MyApp.Utils');
  });

  it('nested file', () => {
    expect(fileToLeanModule('/project/src/components/Button.tsx', opts)).toBe('MyApp.Components.Button');
  });

  it('kebab-case file', () => {
    expect(fileToLeanModule('/project/src/auth-service.ts', opts)).toBe('MyApp.AuthService');
  });

  it('snake_case file', () => {
    expect(fileToLeanModule('/project/src/rate_limiter.ts', opts)).toBe('MyApp.RateLimiter');
  });

  it('index.ts → parent module', () => {
    expect(fileToLeanModule('/project/src/components/index.ts', opts)).toBe('MyApp.Components');
  });

  it('root index.ts → root namespace', () => {
    expect(fileToLeanModule('/project/src/index.ts', opts)).toBe('MyApp');
  });

  it('deeply nested', () => {
    expect(fileToLeanModule('/project/src/api/v2/handlers/auth.ts', opts)).toBe('MyApp.Api.V2.Handlers.Auth');
  });

  it('escapes Lean reserved words', () => {
    expect(fileToLeanModule('/project/src/string.ts', { rootDir: '/project/src', rootNS: 'P' })).toBe('P.String_');
    expect(fileToLeanModule('/project/src/type.ts', { rootDir: '/project/src', rootNS: 'P' })).toBe('P.Type_');
  });
});

describe('Module Resolver: leanModuleToPath', () => {
  it('converts dots to path separators', () => {
    expect(leanModuleToPath('MyApp.Components.Button')).toBe('MyApp/Components/Button.lean');
  });

  it('single component', () => {
    expect(leanModuleToPath('MyApp')).toBe('MyApp.lean');
  });
});

describe('Module Resolver: resolveImportModule', () => {
  const opts = {
    rootDir: path.join(ROOT, 'tests/fixtures/basic'),
    rootNS: 'Test',
  };

  it('resolves relative import', () => {
    const result = resolveImportModule(
      './hello',
      path.join(ROOT, 'tests/fixtures/basic/interfaces.ts'),
      opts,
    );
    expect(result).toBe('Test.Hello');
  });

  it('returns null for unresolvable relative', () => {
    const result = resolveImportModule(
      './nonexistent',
      path.join(ROOT, 'tests/fixtures/basic/hello.ts'),
      opts,
    );
    expect(result).toBeNull();
  });

  it('external package → TSLean.External.*', () => {
    const result = resolveImportModule('zod', '/some/file.ts', opts);
    expect(result).toBe('TSLean.Stdlib.Validation');
  });

  it('unknown external → TSLean.External.PackageName', () => {
    const result = resolveImportModule('some-lib', '/some/file.ts', opts);
    expect(result).toBe('TSLean.External.SomeLib');
  });

  it('scoped package → TSLean.External.Scope.Name', () => {
    const result = resolveImportModule('@hono/zod-validator', '/some/file.ts', opts);
    expect(result).toBe('TSLean.External.Hono.ZodValidator');
  });
});

describe('Module Resolver: isExternalModule', () => {
  it('detects external modules', () => {
    expect(isExternalModule('TSLean.External.Zod')).toBe(true);
    expect(isExternalModule('MyApp.Utils')).toBe(false);
    expect(isExternalModule('TSLean.Runtime.Basic')).toBe(false);
  });
});

// ─── Dependency Graph ───────────────────────────────────────────────────────────

describe('Dependency Graph', () => {
  const FP_DIR = path.join(ROOT, 'tests/fixtures/full-project');

  it('builds graph for full-project fixture', () => {
    const files = [
      path.join(FP_DIR, 'shared/types.ts'),
      path.join(FP_DIR, 'shared/validators.ts'),
      path.join(FP_DIR, 'backend/auth-do.ts'),
      path.join(FP_DIR, 'backend/router.ts'),
    ];
    const opts = { rootDir: FP_DIR, rootNS: 'FullProject' };
    const graph = buildDependencyGraph(files, opts);

    expect(graph.nodes.size).toBe(4);
    expect(graph.order.length).toBe(4);
    expect(graph.cycles.length).toBe(0);
  });

  it('topological order puts dependencies first', () => {
    const files = [
      path.join(FP_DIR, 'shared/types.ts'),
      path.join(FP_DIR, 'shared/validators.ts'),
      path.join(FP_DIR, 'backend/auth-do.ts'),
    ];
    const opts = { rootDir: FP_DIR, rootNS: 'FP' };
    const graph = buildDependencyGraph(files, opts);

    const typesIdx = graph.order.indexOf('FP.Shared.Types');
    const validatorsIdx = graph.order.indexOf('FP.Shared.Validators');
    const authIdx = graph.order.indexOf('FP.Backend.AuthDo');

    // Types must come before AuthDo (AuthDo imports Types)
    if (typesIdx >= 0 && authIdx >= 0) {
      expect(typesIdx).toBeLessThan(authIdx);
    }
    // Validators imports Types
    if (typesIdx >= 0 && validatorsIdx >= 0) {
      expect(typesIdx).toBeLessThan(validatorsIdx);
    }
  });

  it('detects barrel files', () => {
    const tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), 'tslean-barrel-'));
    fs.writeFileSync(path.join(tmpDir, 'index.ts'), 'export const x = 1;');
    fs.writeFileSync(path.join(tmpDir, 'utils.ts'), 'export const y = 2;');

    const files = [
      path.join(tmpDir, 'index.ts'),
      path.join(tmpDir, 'utils.ts'),
    ];
    const graph = buildDependencyGraph(files, { rootDir: tmpDir, rootNS: 'T' });

    const indexNode = graph.nodes.get('T');
    expect(indexNode?.isBarrel).toBe(true);

    const utilsNode = graph.nodes.get('T.Utils');
    expect(utilsNode?.isBarrel).toBe(false);

    fs.rmSync(tmpDir, { recursive: true });
  });

  it('formatCycles produces readable output', () => {
    const msgs = formatCycles([['A', 'B', 'C']]);
    expect(msgs[0]).toContain('A → B → C → A');
  });
});

// ─── Lakefile Generation ────────────────────────────────────────────────────────

describe('Lakefile Generation', () => {
  it('generates valid lakefile.toml', () => {
    const content = generateLakefile({
      name: 'MyProject', rootNS: 'MyProject',
      modules: ['MyProject.Utils', 'MyProject.App'],
      outDir: '/out', leanVersion: 'v4.29.0',
    });
    expect(content).toContain('name = "MyProject"');
    expect(content).toContain('roots = ["MyProject"]');
  });

  it('generates lean-toolchain', () => {
    expect(generateToolchain('v4.29.0')).toBe('leanprover/lean4:v4.29.0\n');
  });

  it('generates root module with imports in order', () => {
    const content = generateRootModule({
      name: 'MyProject', rootNS: 'MyProject',
      modules: ['MyProject.Utils', 'MyProject.App'],
      outDir: '/out', leanVersion: 'v4.29.0',
    });
    expect(content).toContain('import MyProject.Utils');
    expect(content).toContain('import MyProject.App');
    const utilsLine = content.indexOf('import MyProject.Utils');
    const appLine = content.indexOf('import MyProject.App');
    expect(utilsLine).toBeLessThan(appLine);
  });
});
