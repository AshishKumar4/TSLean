// Probe: compile a declaration out of Agent Core's formal library, which is pinned to
// leanprover/lean4:v4.16.0. Proves the compiler and the formal model now agree on a
// toolchain instead of refusing each other.
import { compileLeanToTypeScriptWithInputs } from '../dist/lean-to-typescript/compiler.js';

const projectRoot = '/home/mrwhite0racle/agent-core/packages/agent-core/formal';
const request = {
  projectRoot,
  moduleName: 'AgentCore.Policy',
  sourcePath: `${projectRoot}/AgentCore/Policy.lean`,
  declarations: ['AgentCore.deriveChannelTrust'],
};

try {
  const { package: emitted } = compileLeanToTypeScriptWithInputs(request);
  console.log('TOOLCHAIN', JSON.stringify(emitted.manifest.semantic.leanToolchain, undefined, 2));
  console.log('MODULES', emitted.manifest.semantic.modules.map((module) => module.path).join(', '));
  for (const module of emitted.modules) {
    console.log(`--- ${module.path}`);
    console.log(module.code);
  }
} catch (error) {
  console.log('FAILED', error.constructor.name);
  console.log(error.message);
  process.exitCode = 1;
}
