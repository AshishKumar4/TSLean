// Dumps the exporter's raw closure for a set of roots, so two toolchains' records can be diffed
// directly instead of inferred from a digest that moved.
//
//   node scripts/dump-semantic-closure.mjs <leanRoot> <toolchainDir> <entryModule[,module...]> <decl>...
import { execFileSync } from 'node:child_process';
import { mkdtempSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { delimiter, join, resolve } from 'node:path';

const [rawRoot, toolchain, moduleList, ...declarations] = process.argv.slice(2);
if (rawRoot === undefined || toolchain === undefined || moduleList === undefined || declarations.length === 0) {
  throw new Error('usage: <leanRoot> <toolchainDir> <entryModule[,module...]> <declaration>...');
}
const modules = moduleList.split(',');
const entryModule = modules[0];
const leanRoot = resolve(rawRoot);
const lean = join(toolchain, 'bin', 'lean');
const lake = join(toolchain, 'bin', 'lake');
const searchPath = execFileSync(lake, ['env', 'printenv', 'LEAN_PATH'], { cwd: leanRoot, encoding: 'utf8' })
  .trim()
  .split(delimiter)
  .map((entry) => resolve(leanRoot, entry))
  .join(delimiter);

execFileSync(lake, ['-H', 'build', 'TSLean.LeanToTypeScript.Export', ...modules], { cwd: leanRoot, stdio: 'pipe' });

const driver = join(mkdtempSync(join(tmpdir(), 'closure-dump-')), 'Driver.lean');
const roots = declarations.map((declaration) => JSON.stringify(declaration)).join(' ');
writeFileSync(
  driver,
  [
    'import TSLean.LeanToTypeScript.Export',
    `import ${entryModule}`,
    '',
    `#tslean_export ${JSON.stringify(entryModule)} ${JSON.stringify(modules.join('\n'))} ${roots}`,
    '',
  ].join('\n'),
);
const output = execFileSync(lean, [driver], {
  cwd: leanRoot,
  encoding: 'utf8',
  env: { ...process.env, LEAN_PATH: searchPath },
  maxBuffer: 64 * 1024 * 1024,
});
const line = output.split(/\r?\n/u).find((candidate) => candidate.startsWith('{'));
if (line === undefined) throw new Error(`no exporter response:\n${output}`);
const response = JSON.parse(line);
if (response.ok !== true) throw new Error(`exporter refused: ${response.error}`);
for (const entry of response.package.closure) {
  console.log(`${entry.role}\t${entry.declaration}`);
}
