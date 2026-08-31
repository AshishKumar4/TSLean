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

export { leanAccepts, leanRun, PACKAGED_LEAN_PROJECT, pinnedLeanToolchain } from './lean-check.js';
export type { LeanAcceptance, LeanCheckOptions, LeanDiagnostic, LeanModuleSource, LeanRun } from './lean-check.js';

export {
  compareBehaviour,
  DEFAULT_BEHAVIOUR_LIMIT,
  domainSize,
  enumerateTuples,
  enumerateValues,
  profileModule,
  projectModule,
  renderValue,
  resolveProfileType,
  verifyLeanToTypeScriptRoundtrip,
  verifyTypeScriptToLeanRoundtrip,
} from './roundtrip/index.js';
export type {
  BehaviourDisagreement,
  BehaviourReport,
  BehaviourRequest,
  ModuleProfile,
  ObservedFunction,
  ProfileDeclaration,
  ProfileField,
  ProfileRefusal,
  ProfileType,
  ProfileValue,
  ProjectedModule,
  RoundtripCheck,
  RoundtripCounterexample,
  RoundtripOptions,
  RoundtripReport,
} from './roundtrip/index.js';
