/**
 * @module roundtrip
 *
 * The bidirectional check over the declared intersection of the two compilers.
 *
 * The profile states which constructs both directions carry with the same declared
 * semantics. The verifier sends a program round in each direction, runs both language
 * checkers, executes both sides over the enumerated input domain, and repeats the trip to
 * see whether it settles. What comes back is checks and counterexamples, never a proof.
 */
export type { BehaviourDisagreement, BehaviourReport, BehaviourRequest, ObservedFunction } from './behaviour.js';
export { compareBehaviour, DEFAULT_BEHAVIOUR_LIMIT } from './behaviour.js';
export { profileModule, resolveProfileType } from './profile.js';
export type { ModuleProfile, ProfileDeclaration, ProfileField, ProfileRefusal, ProfileType } from './profile.js';
export { projectModule } from './projection.js';
export type { ProjectedModule } from './projection.js';
export {
  domainSize,
  enumerateTuples,
  enumerateValues,
  renderValue,
} from './values.js';
export type { ProfileValue } from './values.js';
export { verifyLeanToTypeScriptRoundtrip, verifyTypeScriptToLeanRoundtrip } from './verify.js';
export type {
  RoundtripCheck,
  RoundtripCounterexample,
  RoundtripOptions,
  RoundtripReport,
} from './verify.js';
