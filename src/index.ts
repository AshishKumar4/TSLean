export {
  compileTypeScriptProjectToLean,
  compileTypeScriptToLean,
  writeTypeScriptProjectOutputs,
} from './typescript-to-lean/index.js';
export type {
  DegradationMarker,
  GenerateResult,
  ParseOptions,
  ProjectOpts,
  ProjectResult,
} from './typescript-to-lean/index.js';

export {
  compileLeanToTypeScript,
  environmentAttestationDrift,
  generatedModulePath,
  LEAN_TO_TYPESCRIPT_RUNTIME_MODULE_PATH,
  semanticIdentityDigest,
  UnsupportedLeanFragmentError,
  verifyLeanToTypeScriptPackage,
} from './lean-to-typescript/index.js';
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
  LeanToTypeScriptRequest,
  LeanToTypeScriptSemanticIdentity,
  LeanToTypeScriptSourceSpan,
} from './lean-to-typescript/index.js';
