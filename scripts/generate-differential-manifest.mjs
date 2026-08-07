import { readFileSync, writeFileSync } from 'node:fs';
import { dirname, resolve } from 'node:path';
import { argv, stdout } from 'node:process';
import { fileURLToPath } from 'node:url';
import {
  loadCombinedDifferential,
  renderDifferentialManifest,
  renderLeanRegistry,
  verifyDifferentialArtifacts,
} from './differential-manifest-lib.mjs';

const root = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const check = argv.slice(2).includes('--check');
const unknown = argv.slice(2).filter((argument) => argument !== '--check');
if (unknown.length > 0) throw new Error(`unknown arguments: ${unknown.join(' ')}`);

const { manifest, suite } = loadCombinedDifferential(root);
const outputPath = resolve(root, 'spec/differential/manifest.json');
const output = renderDifferentialManifest(manifest);
const registryOutput = renderLeanRegistry(suite);
const registryPath = resolve(root, 'lean/TSLean/JS/Oracle/Registry.lean');
if (check) {
  verifyDifferentialArtifacts(root, readFileSync(outputPath, 'utf8'), readFileSync(registryPath, 'utf8'));
  stdout.write(`Differential manifest is current: ${manifest.totalCount} vectors\n`);
} else {
  writeFileSync(outputPath, output);
  writeFileSync(registryPath, registryOutput);
  stdout.write(`Generated differential manifest: ${manifest.totalCount} vectors\n`);
}
