import { execFileSync } from 'node:child_process';
import { resolve } from 'node:path';
import { describe, expect, it } from 'vitest';

describe('package contents', () => {
  it('includes Lean inputs without local build artifacts', () => {
    const output = execFileSync('bun', ['pm', 'pack', '--dry-run', '--ignore-scripts'], {
      cwd: resolve(import.meta.dirname, '..'),
      encoding: 'utf8',
      maxBuffer: 100 * 1024 * 1024,
    });
    const files = output
      .split('\n')
      .flatMap((line) => line.match(/^packed\s+\S+\s+(.+)$/)?.slice(1) ?? []);

    expect(files).toEqual(
      expect.arrayContaining([
        'lean/TSLean.lean',
        'lean/lakefile.toml',
        'lean/lean-toolchain',
        'lean/lake-manifest.json',
        'scripts/generate-differential-manifest.mjs',
        'scripts/differential-manifest-lib.d.mts',
        'spec/differential/schema.json',
        'spec/differential/primitive.json',
        'spec/differential/abstract-operations.json',
        'spec/differential/corpus-coverage.json',
        'spec/differential/corpus-coverage.schema.json',
        'spec/differential/manifest.json',
        'spec/differential/legacy-abstract-inventory.json',
      ]),
    );
    expect(files).not.toHaveLength(0);
    expect(files.filter((file) => /(^|\/)\.lake\//.test(file))).toEqual([]);
    expect(files.filter((file) => /\.(?:[io]lean(?:\.hash)?|trace|o|obj|a|so|dylib|dll|bc)$/.test(file))).toEqual([]);
    expect(files.filter((file) => /(^|\/)(?:node_modules|tmp|temp)(?:\/|$)/.test(file))).toEqual([]);
    expect(files.filter((file) => /spec\/differential\/.*\.(?:olean|ilean|o|trace)$/.test(file))).toEqual([]);
  });
});
