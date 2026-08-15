import { spawnSync } from 'node:child_process';
import { resolve } from 'node:path';
import { describe, expect, test } from 'vitest';

const leanRoot = resolve(import.meta.dirname, '../lean');

describe('heap scale gate', () => {
  test('runs semantic scale checks in the compiled benchmark', () => {
    const build = spawnSync('lake', ['build', 'js-heap-scale-tests', '--quiet', '--no-ansi'], {
      cwd: leanRoot,
      encoding: 'utf8',
      timeout: 90_000,
    });
    expect(build.status, `${build.stderr}\n${build.stdout}`).toBe(0);

    const executable = `js-heap-scale-tests${process.platform === 'win32' ? '.exe' : ''}`;
    const benchmark = spawnSync(resolve(leanRoot, '.lake/build/bin', executable), [], {
      cwd: leanRoot,
      encoding: 'utf8',
      timeout: 30_000,
    });
    expect(benchmark.status, `${benchmark.stderr}\n${benchmark.stdout}`).toBe(0);
    expect(benchmark.stdout).toContain('heap-scale strings keys=10000');
    expect(benchmark.stdout).toContain('heap-scale symbols keys=10000');
    expect(benchmark.stdout).toContain('heap-scale indices keys=10000');
    expect(benchmark.stdout).toContain('heap-churn cycles=100000');
  }, 120_000);
});
