export { compileLeanToTypeScript, type LeanToTypeScriptRequest } from './compiler.js';
export { UnsupportedLeanFragmentError } from './fragment.js';
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
