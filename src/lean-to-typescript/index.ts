export { compileLeanToTypeScript, type LeanToTypeScriptRequest } from './compiler.js';
export { UnsupportedLeanFragmentError } from './fragment.js';
export {
  leanToTypeScriptHelperBindings,
  type LeanToTypeScriptHelperBinding,
} from './emitter.js';
export {
  LEAN_RUNTIME_ASSUMPTIONS,
  LEAN_RUNTIME_OPCODES,
  referencedRuntimeOpcodes,
  runtimeHelperRole,
  type LeanOpcode,
  type LeanRuntimeAssumption,
  type LeanRuntimeComponent,
  type LeanRuntimeHelperRole,
  type LeanRuntimeOpcode,
  type LeanRuntimeSymbol,
} from './ir.js';
export type {
  LeanToTypeScriptClosureEntry,
  LeanToTypeScriptDeclarationRole,
  LeanToTypeScriptEnvironmentAttestation,
  LeanToTypeScriptGeneratedDeclaration,
  LeanToTypeScriptInput,
  LeanToTypeScriptManifest,
  LeanToTypeScriptModuleArtifact,
  LeanToTypeScriptModuleIdentity,
  LeanToTypeScriptPackage,
  LeanToTypeScriptSemanticIdentity,
  LeanToTypeScriptSourceSpan,
} from './artifact.js';
export { environmentAttestationDrift, semanticIdentityDigest, verifyLeanToTypeScriptPackage } from './manifest.js';
export { generatedModulePath, LEAN_TO_TYPESCRIPT_RUNTIME_MODULE_PATH } from './package-layout.js';
