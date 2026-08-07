import { createHash } from 'node:crypto';
import { execFileSync } from 'node:child_process';
import { readFileSync } from 'node:fs';
import { dirname, resolve } from 'node:path';
import { stdout } from 'node:process';
import { fileURLToPath } from 'node:url';

const root = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const golden = JSON.parse(readFileSync(resolve(root, 'spec/differential/legacy-abstract-inventory.json'), 'utf8'));
const suite = JSON.parse(readFileSync(resolve(root, 'spec/differential/abstract-operations.json'), 'utf8'));

if (golden.schemaVersion !== 1 || golden.totalEntries !== 97) throw new Error('invalid legacy inventory golden');
for (const [path, expected] of Object.entries(golden.files)) {
  const source = execFileSync('git', ['show', `${golden.revision}:${path}`], { cwd: root });
  const actual = createHash('sha256').update(source).digest('hex');
  if (actual !== expected) throw new Error(`legacy source hash changed: ${path}`);
}

let total = 0;
const mapped = new Set();
for (const group of golden.groups) {
  const scenario = suite.scenarios.find(({ id }) => id === group.scenarioId);
  if (scenario === undefined) throw new Error(`missing migrated scenario: ${group.scenarioId}`);
  const ids = scenario.vectors.map(({ id }) => id);
  if (group.count !== ids.length || JSON.stringify(group.vectorIds) !== JSON.stringify(ids)) {
    throw new Error(`legacy inventory mapping changed: ${group.scenarioId}`);
  }
  for (const id of ids) {
    const qualified = `${group.scenarioId}-${id}`;
    if (mapped.has(qualified)) throw new Error(`duplicate legacy inventory mapping: ${qualified}`);
    mapped.add(qualified);
  }
  total += ids.length;
}
if (total !== golden.totalEntries || mapped.size !== 97) throw new Error('legacy inventory mapping is incomplete');
stdout.write(`Legacy abstract inventory is current: ${mapped.size} entries\n`);
