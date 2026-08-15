import { execFileSync } from 'node:child_process';
import { existsSync, readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, expect, it } from 'vitest';

describe('package contents', () => {
  it('runs the complete release gate before publishing', () => {
    const repository = resolve(import.meta.dirname, '..');
    const packageJson: unknown = JSON.parse(readFileSync(resolve(repository, 'package.json'), 'utf8'));
    if (!isRecord(packageJson) || !isRecord(packageJson['scripts'])) throw new TypeError('package scripts are missing');
    expect(packageJson['scripts']['prepublishOnly']).toBe('bun run verify');
    expect(packageJson['scripts']['verify']).toContain('bun run build && bun run lean-to-typescript:check');
  });

  it('does not restore the deleted rival compiler', () => {
    const repository = resolve(import.meta.dirname, '..');
    for (const path of [
      'lean/TSLean/Codegen.lean',
      'lean/TSLean/Generated/SelfHost',
      'lean/TSLean/JsonAST.lean',
      'lean/TSLean/Main.lean',
      'lean/TSLean/Parser.lean',
      'lean/TSLean/V2',
      'scripts/fixpoint-verify.sh',
      'scripts/self-host.sh',
      'scripts/selfhost-adapter.ts',
      'src/preprocessor/tsc-to-json.ts',
      'src/stubs/dts-reader.ts',
    ]) {
      expect(existsSync(resolve(repository, path)), path).toBe(false);
    }
  });

  it('includes Lean inputs without local build artifacts', () => {
    execFileSync('bun', ['run', 'build'], {
      cwd: resolve(import.meta.dirname, '..'),
      stdio: 'pipe',
    });
    const output = execFileSync('bun', ['pm', 'pack', '--dry-run', '--ignore-scripts'], {
      cwd: resolve(import.meta.dirname, '..'),
      encoding: 'utf8',
      maxBuffer: 100 * 1024 * 1024,
    });
    const files = output.split('\n').flatMap((line) => line.match(/^packed\s+\S+\s+(.+)$/)?.slice(1) ?? []);

    expect(files).toEqual(
      expect.arrayContaining([
        'lean/TSLean.lean',
        'lean/TSLean/LeanToTypeScript/Export.lean',
        'lean/lakefile.toml',
        'lean/lean-toolchain',
        'lean/lake-manifest.json',
        'scripts/generate-differential-manifest.mjs',
        'scripts/differential-manifest-lib.d.mts',
        'dist/lean-to-typescript/index.js',
        'dist/lean-to-typescript/index.d.ts',
        'docs/LEAN_TO_TS_PLAN.md',
        'examples/lean-to-typescript/README.md',
        'examples/lean-to-typescript/placement.generated.manifest.json',
        'examples/lean-to-typescript/placement.generated.ts',
        'examples/lean-to-typescript/placement.adapter.ts',
        'dist/lean-to-typescript/cli.js',
        'dist/lean-to-typescript/cli.d.ts',
        'spec/differential/schema.json',
        'spec/differential/primitive.json',
        'spec/differential/abstract-operations.json',
        'spec/differential/corpus-coverage.json',
        'spec/differential/corpus-coverage.schema.json',
        'spec/differential/manifest.json',
        'spec/differential/legacy-abstract-inventory.json',
        'spec/lean-to-typescript/compiler-registry.json',
        'spec/lean-to-typescript/placement.bounds.json',
      ]),
    );
    expect(files).not.toHaveLength(0);
    expect(files.filter((file) => /(^|\/)\.lake\//.test(file))).toEqual([]);
    expect(files.filter((file) => /\.(?:[io]lean(?:\.hash)?|trace|o|obj|a|so|dylib|dll|bc)$/.test(file))).toEqual([]);
    expect(files.filter((file) => /(^|\/)(?:node_modules|tmp|temp)(?:\/|$)/.test(file))).toEqual([]);
    expect(files.filter((file) => /spec\/differential\/.*\.(?:olean|ilean|o|trace)$/.test(file))).toEqual([]);
  });
});

function isRecord(value: unknown): value is Record<string, unknown> {
  return typeof value === 'object' && value !== null && !Array.isArray(value);
}
