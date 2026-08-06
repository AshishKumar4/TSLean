import { execFileSync, type ExecFileSyncOptions } from 'node:child_process';
import { createRequire } from 'node:module';
import * as path from 'node:path';

const ROOT = process.cwd();
const CLI = path.join(ROOT, 'src/cli.ts');
const TSX_CLI = createRequire(import.meta.url).resolve('tsx/cli');

export function runCli(args: readonly string[], options: ExecFileSyncOptions = { stdio: 'pipe' }): Buffer {
  return execFileSync(process.execPath, [TSX_CLI, CLI, ...args], options);
}
