import { execFileSync, spawnSync, type ExecFileSyncOptions } from 'node:child_process';
import { createRequire } from 'node:module';
import * as path from 'node:path';

const ROOT = process.cwd();
const CLI = path.join(ROOT, 'src/cli.ts');
const TSX_CLI = createRequire(import.meta.url).resolve('tsx/cli');

export function runCli(args: readonly string[], options: ExecFileSyncOptions = { stdio: 'pipe' }): Buffer {
  return execFileSync(process.execPath, [TSX_CLI, CLI, ...args], options);
}

export interface CliRun {
  status: number | null;
  stdout: string;
  stderr: string;
}

/** Run the CLI and capture its exit status, for the paths that are meant to fail. */
export function spawnCli(args: readonly string[]): CliRun {
  const run = spawnSync(process.execPath, [TSX_CLI, CLI, ...args], { encoding: 'utf8' });
  if (run.error) throw run.error;
  return { status: run.status, stdout: run.stdout, stderr: run.stderr };
}
