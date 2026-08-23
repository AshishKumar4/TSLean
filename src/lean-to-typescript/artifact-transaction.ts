import { spawnSync } from 'node:child_process';
import { createHash, randomUUID } from 'node:crypto';
import {
  closeSync,
  constants,
  existsSync,
  fstatSync,
  ftruncateSync,
  fsyncSync,
  lstatSync,
  mkdirSync,
  openSync,
  readFileSync,
  realpathSync,
  renameSync,
  rmSync,
  statSync,
  writeFileSync,
} from 'node:fs';
import { basename, dirname, join } from 'node:path';
import { compareCodePoints } from './ordering.js';
import {
  assertLeanToTypeScriptPlatform,
  hostLeanToTypeScriptPlatform,
  type LeanToTypeScriptPlatform,
} from './platform.js';

export interface ArtifactDestination {
  readonly name: string;
  readonly path: string;
  readonly canonicalPath: string;
}

/**
 * What a transaction owns, independently of the file set it happens to write this time. The lock
 * and the journal are named from the scope, so a run that emits fewer modules than the last one
 * still contends for the same lock as a concurrent run that emits more.
 */
export interface ArtifactTransactionScope {
  /** Stable identity of the owned output, hashed into the lock and journal names. */
  readonly identity: string;
  /**
   * Name of the destination whose directory holds the lock. It has to be one the transaction always
   * writes, so the lock does not move when the emitted tree grows or shrinks.
   */
  readonly lockDestination: string;
}

interface ArtifactMetadata {
  readonly dev: bigint;
  readonly ino: bigint;
  isDirectory(): boolean;
  isFile(): boolean;
}

export interface ArtifactFileSystem {
  close(descriptor: number): void;
  exists(path: string): boolean;
  fstat(descriptor: number): ArtifactMetadata;
  fsync(descriptor: number): void;
  lock(descriptor: number): void;
  lstat(path: string): ArtifactMetadata;
  mkdir(path: string): void;
  open(path: string, flags: number, mode?: number): number;
  read(path: string): string;
  realpath(path: string): string;
  remove(path: string): void;
  rename(from: string, to: string): void;
  stat(path: string): ArtifactMetadata;
  truncate(descriptor: number): void;
  write(descriptor: number, contents: string): void;
}

export const nodeArtifactFileSystem: ArtifactFileSystem = Object.freeze({
  close: closeSync,
  exists: existsSync,
  fstat: (descriptor: number) => fstatSync(descriptor, { bigint: true }),
  fsync: fsyncSync,
  lock: lockDescriptor,
  lstat: (path: string) => lstatSync(path, { bigint: true }),
  mkdir: (path: string) => mkdirSync(path, { recursive: true }),
  open: (path: string, flags: number, mode?: number) =>
    mode === undefined ? openSync(path, flags) : openSync(path, flags, mode),
  read: (path: string) => readFileSync(path, 'utf8'),
  realpath: realpathSync,
  remove: (path: string) => rmSync(path),
  rename: renameSync,
  stat: (path: string) => statSync(path, { bigint: true }),
  truncate: (descriptor: number) => ftruncateSync(descriptor, 0),
  write: (descriptor: number, contents: string) => writeFileSync(descriptor, contents, 'utf8'),
});

interface FileIdentity {
  readonly device: bigint;
  readonly inode: bigint;
}

interface BoundDestination extends ArtifactDestination {
  readonly directoryPath: string;
  readonly directoryIdentity: FileIdentity;
  readonly directoryDescriptor: number;
  readonly descriptorPath: string;
  readonly filename: string;
}

interface PublicationLock {
  readonly destination: BoundDestination;
  readonly descriptor: number;
  readonly identity: FileIdentity;
  readonly name: string;
}

interface TransactionOwner {
  readonly processId: number;
  readonly processStartTime: string;
  readonly transactionId: string;
}

interface PublicationLockRecord {
  readonly schemaVersion: 1;
  readonly owner: TransactionOwner;
}

interface PublicationLockStageRecord {
  readonly schemaVersion: 1;
  readonly owner: TransactionOwner;
  readonly stage: UnjournaledStage;
}

interface PublicationLockState {
  readonly owner: TransactionOwner;
  readonly stages: readonly UnjournaledStage[];
}

interface UnjournaledStage {
  readonly canonicalPath: string;
  readonly stageName: string;
  readonly stagedIdentity: SerializedIdentity;
}

interface StagedArtifact {
  readonly destination: BoundDestination;
  /** A removal has no staged replacement: publication leaves the destination absent. */
  readonly removal: boolean;
  readonly stageName: string;
  readonly backupName: string;
  readonly stagedIdentity: FileIdentity | undefined;
  readonly originalIdentity: FileIdentity | undefined;
  originalMoved: boolean;
  stagedMoved: boolean;
}

interface JournalArtifact {
  readonly canonicalPath: string;
  readonly stageName: string;
  readonly backupName: string;
  readonly stagedIdentity: SerializedIdentity | null;
  readonly originalIdentity: SerializedIdentity | null;
}

interface SerializedIdentity {
  readonly device: string;
  readonly inode: string;
}

type JournalState = 'prepared' | 'committed';

interface TransactionJournal {
  readonly schemaVersion: 1;
  readonly owner: TransactionOwner;
  readonly state: JournalState;
  readonly artifacts: readonly JournalArtifact[];
}

interface RecoveryArtifact {
  readonly destination: BoundDestination;
  readonly journal: JournalArtifact;
  readonly stagedIdentity: FileIdentity | undefined;
  readonly originalIdentity: FileIdentity | undefined;
  readonly destinationIdentity: FileIdentity | undefined;
  readonly stageIdentity: FileIdentity | undefined;
  readonly backupIdentity: FileIdentity | undefined;
}

/**
 * Publishes a whole generated package atomically: every destination is staged and journalled
 * before any of them replaces its target, so a crash leaves either the complete previous tree or
 * the complete new one.
 */
export function publishArtifacts(
  scope: ArtifactTransactionScope,
  destinations: readonly ArtifactDestination[],
  contents: readonly (string | undefined)[],
  platform: LeanToTypeScriptPlatform = hostLeanToTypeScriptPlatform,
): void {
  publishArtifactsWithFileSystem(scope, destinations, contents, nodeArtifactFileSystem, platform);
}

/** A destination whose content is `undefined` is removed by the same transaction that writes the rest. */
export function publishArtifactsWithFileSystem(
  scope: ArtifactTransactionScope,
  destinations: readonly ArtifactDestination[],
  contents: readonly (string | undefined)[],
  filesystem: ArtifactFileSystem,
  platform: LeanToTypeScriptPlatform = hostLeanToTypeScriptPlatform,
): void {
  assertLeanToTypeScriptPlatform(platform);
  if (destinations.length !== contents.length) {
    throw new TypeError('artifact transaction requires one content for each destination');
  }
  const bound = bindDestinations(destinations, filesystem);
  let publicationLock: PublicationLock | undefined;
  let transactionOwner: TransactionOwner | undefined;
  const staged: StagedArtifact[] = [];
  const journalName = transactionJournalName(scope);
  let durablyCommitted = false;
  let preserveRecoveryEvidence = false;
  let removePublicationLockWhenFinished = false;
  try {
    publicationLock = acquirePublicationLock(bound, scope, journalName, filesystem);
    for (const destination of bound) assertBoundRoute(destination, filesystem);
    recoverBoundArtifacts(bound, journalName, publicationLock, filesystem);
    transactionOwner = currentTransactionOwner();
    writePublicationLockOwner(publicationLock, transactionOwner, filesystem);
    for (let index = 0; index < bound.length; index += 1) {
      const destination = bound[index];
      if (destination === undefined || index >= contents.length) {
        throw new TypeError('artifact transaction destinations and contents are misaligned');
      }
      assertPublicationLockOwned(publicationLock, filesystem);
      staged.push(
        stageArtifact(destination, contents[index], transactionOwner, publicationLock, bound.length, filesystem),
      );
    }
    const prepared = transactionJournal(staged, 'prepared', transactionOwner);
    writeJournalCopies(bound, journalName, prepared, publicationLock, filesystem);
    syncDirectories(bound, filesystem);
    assertPublicationLockOwned(publicationLock, filesystem);
    for (const artifact of staged) assertDestinationUnchanged(artifact, filesystem);
    for (const artifact of staged) {
      assertPublicationLockOwned(publicationLock, filesystem);
      moveOriginalToBackup(artifact, filesystem);
    }
    for (const artifact of staged) assertOriginalMoved(artifact, filesystem);
    for (const artifact of staged) {
      assertPublicationLockOwned(publicationLock, filesystem);
      moveStageToDestination(artifact, filesystem);
    }
    for (const artifact of staged) assertPublishedArtifact(artifact, filesystem);
    syncDirectories(bound, filesystem);
    for (const artifact of staged) assertPublishedArtifact(artifact, filesystem);
    for (const destination of bound) assertBoundRoute(destination, filesystem);
    const committed = { ...prepared, state: 'committed' } as const;
    for (const directory of uniqueDirectories(bound)) {
      writeBoundFile(directory, committedJournalName(journalName), encodeJournal(committed), filesystem);
      filesystem.fsync(directory.directoryDescriptor);
      for (const artifact of staged) assertPublishedArtifact(artifact, filesystem);
      durablyCommitted = true;
    }
    assertPublicationLockOwned(publicationLock, filesystem);
    finishCommittedTransaction(staged, bound, journalName, transactionOwner, publicationLock, filesystem);
    removePublicationLockWhenFinished = true;
  } catch (error: unknown) {
    if (publicationLock === undefined) throw error;
    const ownedPublicationLock = publicationLock;
    if (!publicationLockIsOwned(ownedPublicationLock, filesystem)) {
      throw new TypeError('artifact publication lock identity changed', { cause: error });
    }
    if (durablyCommitted) {
      for (const artifact of staged) assertPublishedArtifact(artifact, filesystem);
      try {
        if (transactionOwner !== undefined) {
          finishCommittedTransaction(staged, bound, journalName, transactionOwner, ownedPublicationLock, filesystem);
          removePublicationLockWhenFinished = true;
        }
      } catch (cleanupError: unknown) {
        void cleanupError;
      }
      return;
    }
    const rollbackError = rollback(staged, bound, ownedPublicationLock, filesystem);
    let unjournaledCleanupError: Error | undefined;
    if (rollbackError === undefined && transactionOwner !== undefined) {
      try {
        recoverUnjournaledStages(bound, ownedPublicationLock, filesystem);
      } catch (cleanupError: unknown) {
        unjournaledCleanupError = cleanupError instanceof Error ? cleanupError : new TypeError(String(cleanupError));
      }
    }
    const journalCleanupError =
      rollbackError === undefined && unjournaledCleanupError === undefined && transactionOwner !== undefined
        ? removeCurrentJournalCopies(bound, journalName, transactionOwner, ownedPublicationLock, filesystem)
        : undefined;
    if (rollbackError !== undefined || journalCleanupError !== undefined || unjournaledCleanupError !== undefined) {
      preserveRecoveryEvidence = true;
      const detail =
        rollbackError?.message ??
        journalCleanupError?.message ??
        unjournaledCleanupError?.message ??
        'unknown recovery failure';
      throw new TypeError(`artifact publication failed and rollback failed: ${detail}`, { cause: error });
    }
    removePublicationLockWhenFinished = transactionOwner !== undefined;
    throw error;
  } finally {
    try {
      if (
        !durablyCommitted &&
        !preserveRecoveryEvidence &&
        publicationLock !== undefined &&
        publicationLockIsOwned(publicationLock, filesystem)
      ) {
        for (const artifact of staged) cleanupUnpublishedFiles(artifact, publicationLock, filesystem);
      }
      if (
        removePublicationLockWhenFinished &&
        publicationLock !== undefined &&
        publicationLockIsOwned(publicationLock, filesystem)
      ) {
        removePublicationLock(publicationLock, filesystem);
      }
    } finally {
      if (publicationLock !== undefined) filesystem.close(publicationLock.descriptor);
      for (const destination of bound) filesystem.close(destination.directoryDescriptor);
    }
  }
}

export function recoverArtifactsWithFileSystem(
  scope: ArtifactTransactionScope,
  destinations: readonly ArtifactDestination[],
  filesystem: ArtifactFileSystem,
): void {
  const bound = bindDestinations(destinations, filesystem);
  let publicationLock: PublicationLock | undefined;
  let recoveryFinished = false;
  try {
    publicationLock = acquirePublicationLock(bound, scope, transactionJournalName(scope), filesystem);
    for (const destination of bound) assertBoundRoute(destination, filesystem);
    recoverBoundArtifacts(bound, transactionJournalName(scope), publicationLock, filesystem);
    recoveryFinished = true;
  } finally {
    try {
      if (recoveryFinished && publicationLock !== undefined && publicationLockIsOwned(publicationLock, filesystem)) {
        removePublicationLock(publicationLock, filesystem);
      }
    } finally {
      if (publicationLock !== undefined) filesystem.close(publicationLock.descriptor);
      for (const destination of bound) filesystem.close(destination.directoryDescriptor);
    }
  }
}

/**
 * The lock lives beside the scope's stable manifest destination, not beside whichever generated
 * module happens to sort first. The module set changes whenever a package grows or shrinks; the
 * manifest does not, so every shape of the same owned tree contends for this one lock.
 */
function acquirePublicationLock(
  destinations: readonly BoundDestination[],
  scope: ArtifactTransactionScope,
  journalName: string,
  filesystem: ArtifactFileSystem,
): PublicationLock {
  const destination = destinations.find((candidate) => candidate.name === scope.lockDestination);
  if (destination === undefined) {
    throw new TypeError(`artifact transaction scope names no destination ${scope.lockDestination}`);
  }
  const name = `${journalName}.lock`;
  const path = childPath(destination, name);
  while (true) {
    const descriptor = filesystem.open(
      path,
      constants.O_RDWR | constants.O_CREAT | platformConstant('O_NOFOLLOW'),
      0o600,
    );
    try {
      const metadata = filesystem.fstat(descriptor);
      if (!metadata.isFile()) throw new TypeError('artifact publication lock must be a regular file');
      const lockIdentity = identity(metadata);
      filesystem.lock(descriptor);
      const namedIdentity = fileIdentity(path, filesystem);
      if (namedIdentity !== undefined && sameIdentity(namedIdentity, lockIdentity)) {
        filesystem.fsync(descriptor);
        filesystem.fsync(destination.directoryDescriptor);
        return { destination, descriptor, identity: lockIdentity, name };
      }
    } catch (error: unknown) {
      filesystem.close(descriptor);
      throw error;
    }
    filesystem.close(descriptor);
  }
}

/**
 * The lock's own record of the transaction: its owner, and one entry per file staged before the
 * journal exists. `stageLimit` is the transaction's destination count, so a lock that has grown
 * past the set it belongs to is corrupt rather than merely unexpected.
 */
function readPublicationLockState(
  publicationLock: PublicationLock,
  stageLimit: number,
  filesystem: ArtifactFileSystem,
): PublicationLockState | undefined {
  assertPublicationLockOwned(publicationLock, filesystem);
  const source = filesystem.read(childPath(publicationLock.destination, publicationLock.name));
  assertPublicationLockOwned(publicationLock, filesystem);
  if (source.length === 0) return undefined;
  if (!source.endsWith('\n')) throw new TypeError('artifact publication lock record is corrupt');
  const records = source.slice(0, -1).split('\n').map(decodePublicationLockLine);
  const first = records[0];
  if (
    first === undefined ||
    !isRecord(first) ||
    !hasExactKeys(first, ['owner', 'schemaVersion']) ||
    first['schemaVersion'] !== 1 ||
    !isTransactionOwner(first['owner'])
  ) {
    throw new TypeError('artifact publication lock record is invalid');
  }
  const owner = first['owner'];
  const stages: UnjournaledStage[] = [];
  for (const record of records.slice(1)) {
    if (
      !isRecord(record) ||
      !hasExactKeys(record, ['owner', 'schemaVersion', 'stage']) ||
      record['schemaVersion'] !== 1 ||
      !isTransactionOwner(record['owner']) ||
      !sameTransactionOwner(record['owner'], owner)
    ) {
      throw new TypeError('artifact publication lock stage record is invalid');
    }
    const stage = decodeUnjournaledStage(record['stage']);
    if (stages.some((entry) => entry.canonicalPath === stage.canonicalPath || entry.stageName === stage.stageName)) {
      throw new TypeError('artifact publication lock has duplicate stage records');
    }
    stages.push(stage);
  }
  if (stages.length > stageLimit) throw new TypeError('artifact publication lock has too many stage records');
  return { owner, stages };
}

function writePublicationLockOwner(
  publicationLock: PublicationLock,
  owner: TransactionOwner,
  filesystem: ArtifactFileSystem,
): void {
  assertPublicationLockOwned(publicationLock, filesystem);
  const record: PublicationLockRecord = { schemaVersion: 1, owner };
  filesystem.truncate(publicationLock.descriptor);
  filesystem.write(publicationLock.descriptor, `${JSON.stringify(record)}\n`);
  filesystem.fsync(publicationLock.descriptor);
  filesystem.fsync(publicationLock.destination.directoryDescriptor);
  assertPublicationLockOwned(publicationLock, filesystem);
}

/**
 * Records one staged file in the lock before it is journalled, so a crash between staging and the
 * journal still leaves a durable pointer to the orphan. The transaction's own destination count
 * bounds the record: one entry per destination, and never the same destination twice.
 */
function recordUnjournaledStage(
  publicationLock: PublicationLock,
  owner: TransactionOwner,
  stage: UnjournaledStage,
  destinationCount: number,
  filesystem: ArtifactFileSystem,
): void {
  const state = readPublicationLockState(publicationLock, destinationCount, filesystem);
  if (state === undefined || !sameTransactionOwner(state.owner, owner)) {
    throw new TypeError('artifact publication lock owner changed');
  }
  if (
    state.stages.length >= destinationCount ||
    state.stages.some((entry) => entry.canonicalPath === stage.canonicalPath)
  ) {
    throw new TypeError('artifact publication lock cannot record another stage');
  }
  const record: PublicationLockStageRecord = { schemaVersion: 1, owner, stage };
  assertPublicationLockOwned(publicationLock, filesystem);
  filesystem.write(publicationLock.descriptor, `${JSON.stringify(record)}\n`);
  filesystem.fsync(publicationLock.descriptor);
  assertPublicationLockOwned(publicationLock, filesystem);
}

function assertPublicationLockOwned(publicationLock: PublicationLock, filesystem: ArtifactFileSystem): void {
  if (!publicationLockIsOwned(publicationLock, filesystem)) {
    throw new TypeError('artifact publication lock identity changed');
  }
}

function publicationLockIsOwned(publicationLock: PublicationLock, filesystem: ArtifactFileSystem): boolean {
  try {
    const descriptorIdentity = identity(filesystem.fstat(publicationLock.descriptor));
    const namedIdentity = fileIdentity(childPath(publicationLock.destination, publicationLock.name), filesystem);
    return (
      sameIdentity(descriptorIdentity, publicationLock.identity) &&
      namedIdentity !== undefined &&
      sameIdentity(namedIdentity, publicationLock.identity)
    );
  } catch (error: unknown) {
    if (hasErrorCode(error, 'ENOENT', 'ENOTDIR')) return false;
    throw error;
  }
}

function removePublicationLock(publicationLock: PublicationLock, filesystem: ArtifactFileSystem): void {
  assertPublicationLockOwned(publicationLock, filesystem);
  removeKnownFile(publicationLock.destination, publicationLock.name, publicationLock.identity, filesystem);
}

/**
 * Binds every destination's parent directory before any of them is written. Two destinations that
 * turn out to name the same file would make the transaction unable to roll either back, so the
 * whole set is checked pairwise and a failure closes every descriptor already opened.
 */
function bindDestinations(
  destinations: readonly ArtifactDestination[],
  filesystem: ArtifactFileSystem,
): readonly BoundDestination[] {
  if (destinations.length === 0) throw new TypeError('artifact publication requires at least one destination');
  const bound: BoundDestination[] = [];
  try {
    for (const destination of destinations) {
      const next = bindDestination(destination, filesystem);
      const nextFile = fileIdentity(childPath(next, next.filename), filesystem);
      for (const previous of bound) {
        if (!sameIdentity(previous.directoryIdentity, next.directoryIdentity)) continue;
        const previousFile = fileIdentity(childPath(previous, previous.filename), filesystem);
        if (
          previous.filename === next.filename ||
          (previousFile !== undefined && nextFile !== undefined && sameIdentity(previousFile, nextFile))
        ) {
          filesystem.close(next.directoryDescriptor);
          throw new TypeError('artifact destinations must identify distinct regular files');
        }
      }
      bound.push(next);
    }
  } catch (error: unknown) {
    for (const opened of bound) filesystem.close(opened.directoryDescriptor);
    throw error;
  }
  return bound;
}

function bindDestination(destination: ArtifactDestination, filesystem: ArtifactFileSystem): BoundDestination {
  const directoryPath = dirname(destination.canonicalPath);
  filesystem.mkdir(directoryPath);
  if (filesystem.realpath(directoryPath) !== directoryPath) {
    throw new TypeError(`${destination.name} canonical parent changed before artifact publication`);
  }
  if (dirname(canonicalDestination(destination.path, filesystem)) !== directoryPath) {
    throw new TypeError('artifact destination changed during compilation');
  }
  const descriptor = filesystem.open(
    directoryPath,
    constants.O_RDONLY | platformConstant('O_DIRECTORY') | platformConstant('O_NOFOLLOW'),
  );
  try {
    const directoryIdentity = identity(filesystem.fstat(descriptor));
    if (!sameIdentity(directoryIdentity, identity(filesystem.stat(directoryPath)))) {
      throw new TypeError('artifact destination changed during compilation');
    }
    const descriptorPath = `/proc/self/fd/${descriptor}`;
    if (!filesystem.exists(descriptorPath) || !filesystem.stat(descriptorPath).isDirectory()) {
      throw new TypeError('identity-bound artifact publication requires /proc/self/fd directory handles');
    }
    return {
      ...destination,
      directoryPath,
      directoryIdentity,
      directoryDescriptor: descriptor,
      descriptorPath,
      filename: basename(destination.canonicalPath),
    };
  } catch (error: unknown) {
    filesystem.close(descriptor);
    throw error;
  }
}

function stageArtifact(
  destination: BoundDestination,
  contents: string | undefined,
  owner: TransactionOwner,
  publicationLock: PublicationLock,
  destinationCount: number,
  filesystem: ArtifactFileSystem,
): StagedArtifact {
  assertBoundRoute(destination, filesystem);
  const stageName = transactionName(destination.filename, 'stage');
  const backupName = transactionName(destination.filename, 'backup');
  const originalIdentity = fileIdentity(childPath(destination, destination.filename), filesystem);
  if (contents === undefined) {
    // A removal stages nothing. It still takes a backup, so a rollback restores the file it deleted.
    return {
      destination,
      removal: true,
      stageName,
      backupName,
      stagedIdentity: undefined,
      originalIdentity,
      originalMoved: false,
      stagedMoved: false,
    };
  }
  const stagedIdentity = writeBoundFile(destination, stageName, contents, filesystem, (createdIdentity) => {
    recordUnjournaledStage(
      publicationLock,
      owner,
      {
        canonicalPath: destination.canonicalPath,
        stageName,
        stagedIdentity: serializeIdentity(createdIdentity),
      },
      destinationCount,
      filesystem,
    );
  });
  return {
    destination,
    removal: false,
    stageName,
    backupName,
    stagedIdentity,
    originalIdentity,
    originalMoved: false,
    stagedMoved: false,
  };
}

function writeBoundFile(
  destination: BoundDestination,
  name: string,
  contents: string,
  filesystem: ArtifactFileSystem,
  afterOpen?: (identity: FileIdentity) => void,
): FileIdentity {
  const path = childPath(destination, name);
  const descriptor = filesystem.open(
    path,
    constants.O_WRONLY | constants.O_CREAT | constants.O_EXCL | platformConstant('O_NOFOLLOW'),
    0o666,
  );
  let openedIdentity: FileIdentity | undefined;
  try {
    const metadata = filesystem.fstat(descriptor);
    if (!metadata.isFile()) throw new TypeError('artifact transaction target must be a regular file');
    openedIdentity = identity(metadata);
    afterOpen?.(openedIdentity);
    filesystem.write(descriptor, contents);
    filesystem.fsync(descriptor);
    const writtenIdentity = identity(filesystem.fstat(descriptor));
    if (!sameIdentity(writtenIdentity, openedIdentity)) {
      throw new TypeError('artifact transaction file descriptor identity changed');
    }
    filesystem.close(descriptor);
    return writtenIdentity;
  } catch (error: unknown) {
    try {
      filesystem.close(descriptor);
    } catch (closeError: unknown) {
      void closeError;
    }
    removeKnownFile(destination, name, openedIdentity, filesystem);
    throw error;
  }
}

function writeJournalCopies(
  destinations: readonly BoundDestination[],
  journalName: string,
  journal: TransactionJournal,
  publicationLock: PublicationLock,
  filesystem: ArtifactFileSystem,
): void {
  const source = encodeJournal(journal);
  for (const destination of uniqueDirectories(destinations)) {
    assertPublicationLockOwned(publicationLock, filesystem);
    writeBoundFile(destination, journalName, source, filesystem);
  }
}

function assertDestinationUnchanged(artifact: StagedArtifact, filesystem: ArtifactFileSystem): void {
  assertBoundRoute(artifact.destination, filesystem);
  const actual = fileIdentity(childPath(artifact.destination, artifact.destination.filename), filesystem);
  if (!optionalSameIdentity(actual, artifact.originalIdentity)) {
    throw new TypeError('artifact destination changed during compilation');
  }
}

function moveOriginalToBackup(artifact: StagedArtifact, filesystem: ArtifactFileSystem): void {
  if (artifact.originalIdentity === undefined) {
    assertFileAbsent(artifact.destination, artifact.destination.filename, 'artifact destination changed', filesystem);
    return;
  }
  assertKnownFile(artifact.destination, artifact.destination.filename, artifact.originalIdentity, filesystem);
  assertFileAbsent(artifact.destination, artifact.backupName, 'artifact backup changed', filesystem);
  filesystem.rename(
    childPath(artifact.destination, artifact.destination.filename),
    childPath(artifact.destination, artifact.backupName),
  );
  artifact.originalMoved = true;
  assertOriginalMoved(artifact, filesystem);
}

function assertOriginalMoved(artifact: StagedArtifact, filesystem: ArtifactFileSystem): void {
  assertFileAbsent(artifact.destination, artifact.destination.filename, 'artifact destination changed', filesystem);
  if (artifact.originalIdentity !== undefined) {
    assertKnownFile(artifact.destination, artifact.backupName, artifact.originalIdentity, filesystem);
  }
}

function moveStageToDestination(artifact: StagedArtifact, filesystem: ArtifactFileSystem): void {
  if (artifact.removal || artifact.stagedIdentity === undefined) {
    // Nothing replaces a removed destination; the backup already holds what was there.
    artifact.stagedMoved = true;
    assertPublishedArtifact(artifact, filesystem);
    return;
  }
  assertKnownFile(artifact.destination, artifact.stageName, artifact.stagedIdentity, filesystem);
  assertFileAbsent(artifact.destination, artifact.destination.filename, 'artifact destination changed', filesystem);
  filesystem.rename(
    childPath(artifact.destination, artifact.stageName),
    childPath(artifact.destination, artifact.destination.filename),
  );
  artifact.stagedMoved = true;
  assertPublishedArtifact(artifact, filesystem);
}

function assertPublishedArtifact(artifact: StagedArtifact, filesystem: ArtifactFileSystem): void {
  if (artifact.stagedIdentity === undefined) {
    assertFileAbsent(artifact.destination, artifact.destination.filename, 'artifact removal changed', filesystem);
    return;
  }
  assertKnownFile(artifact.destination, artifact.destination.filename, artifact.stagedIdentity, filesystem);
}

function rollback(
  artifacts: readonly StagedArtifact[],
  destinations: readonly BoundDestination[],
  publicationLock: PublicationLock,
  filesystem: ArtifactFileSystem,
): Error | undefined {
  try {
    for (const artifact of [...artifacts].reverse()) {
      if (artifact.stagedMoved) {
        assertPublicationLockOwned(publicationLock, filesystem);
        removeKnownFile(artifact.destination, artifact.destination.filename, artifact.stagedIdentity, filesystem);
        artifact.stagedMoved = false;
      }
      if (artifact.originalMoved) {
        assertPublicationLockOwned(publicationLock, filesystem);
        const backupIdentity = fileIdentity(childPath(artifact.destination, artifact.backupName), filesystem);
        if (!optionalSameIdentity(backupIdentity, artifact.originalIdentity)) {
          throw new TypeError('artifact rollback backup identity changed');
        }
        assertPublicationLockOwned(publicationLock, filesystem);
        assertFileAbsent(
          artifact.destination,
          artifact.destination.filename,
          'artifact rollback destination changed',
          filesystem,
        );
        filesystem.rename(
          childPath(artifact.destination, artifact.backupName),
          childPath(artifact.destination, artifact.destination.filename),
        );
        if (artifact.originalIdentity !== undefined) {
          assertKnownFile(artifact.destination, artifact.destination.filename, artifact.originalIdentity, filesystem);
        }
        artifact.originalMoved = false;
      }
    }
    syncDirectories(destinations, filesystem);
    return undefined;
  } catch (error: unknown) {
    return error instanceof Error ? error : new TypeError(String(error));
  }
}

function cleanupUnpublishedFiles(
  artifact: StagedArtifact,
  publicationLock: PublicationLock,
  filesystem: ArtifactFileSystem,
): void {
  if (!artifact.stagedMoved) {
    assertPublicationLockOwned(publicationLock, filesystem);
    removeKnownFile(artifact.destination, artifact.stageName, artifact.stagedIdentity, filesystem);
  }
  if (artifact.originalMoved) return;
  assertPublicationLockOwned(publicationLock, filesystem);
  removeKnownFile(artifact.destination, artifact.backupName, artifact.originalIdentity, filesystem);
}

function finishCommittedTransaction(
  artifacts: readonly StagedArtifact[],
  destinations: readonly BoundDestination[],
  journalName: string,
  owner: TransactionOwner,
  publicationLock: PublicationLock,
  filesystem: ArtifactFileSystem,
): void {
  for (const artifact of artifacts) {
    assertPublicationLockOwned(publicationLock, filesystem);
    assertPublishedArtifact(artifact, filesystem);
    removeKnownFile(artifact.destination, artifact.backupName, artifact.originalIdentity, filesystem);
    artifact.originalMoved = false;
  }
  for (const artifact of artifacts) assertPublishedArtifact(artifact, filesystem);
  assertPublicationLockOwned(publicationLock, filesystem);
  syncDirectories(destinations, filesystem);
  const journalCleanupError = removeCurrentJournalCopies(destinations, journalName, owner, publicationLock, filesystem);
  if (journalCleanupError !== undefined) throw journalCleanupError;
  syncDirectories(destinations, filesystem);
}

function transactionJournal(
  artifacts: readonly StagedArtifact[],
  state: JournalState,
  owner: TransactionOwner,
): TransactionJournal {
  const entries = artifacts
    .map((artifact): JournalArtifact => ({
      canonicalPath: artifact.destination.canonicalPath,
      stageName: artifact.stageName,
      backupName: artifact.backupName,
      stagedIdentity: artifact.stagedIdentity === undefined ? null : serializeIdentity(artifact.stagedIdentity),
      originalIdentity: artifact.originalIdentity === undefined ? null : serializeIdentity(artifact.originalIdentity),
    }))
    .sort((left, right) => compareCodePoints(left.canonicalPath, right.canonicalPath));
  if (entries.length === 0) throw new TypeError('artifact transaction journal requires at least one artifact');
  return { schemaVersion: 1, owner, state, artifacts: entries };
}

/**
 * Recovers an interrupted transaction before a new publisher writes. The manifest directory is
 * always part of a package transaction, so it anchors discovery even when the newer publisher has
 * a smaller tree. Once a journal is found, recovery binds the JOURNAL'S destination set rather
 * than the caller's current set: otherwise a shrink could restore only the files it still names
 * and strand a backup for a removed module.
 */
function recoverBoundArtifacts(
  destinations: readonly BoundDestination[],
  journalName: string,
  publicationLock: PublicationLock,
  filesystem: ArtifactFileSystem,
): void {
  assertPublicationLockOwned(publicationLock, filesystem);
  const copies = uniqueDirectories(destinations)
    .flatMap((destination) =>
      [journalName, committedJournalName(journalName)].map((name) => ({
        destination,
        path: childPath(destination, name),
      })),
    )
    .filter(({ path }) => filesystem.exists(path))
    .map((copy) => {
      const journalIdentity = fileIdentity(copy.path, filesystem);
      if (journalIdentity === undefined) throw new TypeError('artifact transaction journal disappeared');
      return { ...copy, identity: journalIdentity };
    });
  if (copies.length === 0) {
    recoverUnjournaledStages(destinations, publicationLock, filesystem);
    return;
  }
  const journals = copies.map(({ path }) => decodeJournal(filesystem.read(path)));
  const first = journals[0];
  if (first === undefined) throw new TypeError('artifact transaction journal disappeared');
  const expectedTransaction = comparableJournal(first);
  if (journals.some((journal) => comparableJournal(journal) !== expectedTransaction)) {
    throw new TypeError('artifact transaction journals disagree');
  }
  for (const copy of copies) {
    const currentIdentity = fileIdentity(copy.path, filesystem);
    if (currentIdentity === undefined || !sameIdentity(currentIdentity, copy.identity)) {
      throw new TypeError('artifact transaction journal identity changed');
    }
  }
  const journalDestinations = bindDestinations(
    first.artifacts.map((artifact) => ({
      name: `journal:${artifact.canonicalPath}`,
      path: artifact.canonicalPath,
      canonicalPath: artifact.canonicalPath,
    })),
    filesystem,
  );
  try {
    const lockOwner = readPublicationLockState(publicationLock, journalDestinations.length, filesystem)?.owner;
    if (lockOwner === undefined) {
      if (transactionOwnerIsLive(first.owner)) {
        throw new TypeError('artifact transaction journal belongs to a live foreign publisher');
      }
    } else if (!sameTransactionOwner(lockOwner, first.owner)) {
      throw new TypeError('artifact transaction journal owner does not match the publication lock');
    }
    const state: JournalState = journals.some((journal) => journal.state === 'committed') ? 'committed' : 'prepared';
    const recovery = prepareRecovery(journalDestinations, first, state, filesystem);
    for (const artifact of recovery) {
      assertPublicationLockOwned(publicationLock, filesystem);
      recoverArtifact(artifact, state, publicationLock, filesystem);
    }
    assertPublicationLockOwned(publicationLock, filesystem);
    syncDirectories(journalDestinations, filesystem);
    const cleanupError = removeCurrentJournalCopies(
      journalDestinations,
      journalName,
      first.owner,
      publicationLock,
      filesystem,
    );
    if (cleanupError !== undefined) throw cleanupError;
    syncDirectories(journalDestinations, filesystem);
  } finally {
    for (const destination of journalDestinations) filesystem.close(destination.directoryDescriptor);
  }
}

function recoverUnjournaledStages(
  destinations: readonly BoundDestination[],
  publicationLock: PublicationLock,
  filesystem: ArtifactFileSystem,
): void {
  const state = readPublicationLockState(publicationLock, destinations.length, filesystem);
  if (state === undefined || state.stages.length === 0) return;
  const recoverable: {
    readonly destination: BoundDestination;
    readonly identity: FileIdentity;
    readonly name: string;
  }[] = [];
  for (const stage of state.stages) {
    const destination = destinations.find((entry) => entry.canonicalPath === stage.canonicalPath);
    if (destination === undefined || !isTransactionName(stage.stageName, 'stage', destination.filename)) {
      throw new TypeError('artifact publication lock names an invalid stage');
    }
    const expected = deserializeIdentity(stage.stagedIdentity);
    const actual = fileIdentity(childPath(destination, stage.stageName), filesystem);
    if (actual === undefined) continue;
    if (!sameIdentity(actual, expected)) {
      throw new TypeError('artifact transaction file identity changed');
    }
    recoverable.push({ destination, identity: expected, name: stage.stageName });
  }
  for (const stage of recoverable) {
    assertPublicationLockOwned(publicationLock, filesystem);
    removeKnownFile(stage.destination, stage.name, stage.identity, filesystem);
  }
  syncDirectories(destinations, filesystem);
}

function prepareRecovery(
  destinations: readonly BoundDestination[],
  journal: TransactionJournal,
  state: JournalState,
  filesystem: ArtifactFileSystem,
): readonly RecoveryArtifact[] {
  const recovery: RecoveryArtifact[] = [];
  for (const destination of destinations) {
    const artifact = journal.artifacts.find((entry) => entry.canonicalPath === destination.canonicalPath);
    if (artifact === undefined) {
      throw new TypeError('artifact transaction journal names different destinations');
    }
    if (
      !isTransactionName(artifact.stageName, 'stage', destination.filename) ||
      !isTransactionName(artifact.backupName, 'backup', destination.filename)
    ) {
      throw new TypeError('artifact transaction journal entry names invalid transaction files');
    }
    const prepared = {
      destination,
      journal: artifact,
      stagedIdentity: artifact.stagedIdentity === null ? undefined : deserializeIdentity(artifact.stagedIdentity),
      originalIdentity: artifact.originalIdentity === null ? undefined : deserializeIdentity(artifact.originalIdentity),
      destinationIdentity: fileIdentity(childPath(destination, destination.filename), filesystem),
      stageIdentity: fileIdentity(childPath(destination, artifact.stageName), filesystem),
      backupIdentity: fileIdentity(childPath(destination, artifact.backupName), filesystem),
    };
    validateRecoveryArtifact(prepared, state);
    recovery.push(prepared);
  }
  return recovery;
}

function validateRecoveryArtifact(artifact: RecoveryArtifact, state: JournalState): void {
  const removal = artifact.stagedIdentity === undefined;
  const destinationIsStaged = optionalSameIdentity(artifact.destinationIdentity, artifact.stagedIdentity);
  const stageIsStaged = optionalSameIdentity(artifact.stageIdentity, artifact.stagedIdentity);
  const destinationIsOriginal = optionalSameIdentity(artifact.destinationIdentity, artifact.originalIdentity);
  const backupIsOriginal = optionalSameIdentity(artifact.backupIdentity, artifact.originalIdentity);
  if (removal) {
    if (artifact.stageIdentity !== undefined) {
      throw new TypeError('artifact removal transaction has an unexpected stage');
    }
    if (state === 'committed') {
      if (artifact.destinationIdentity !== undefined || (artifact.backupIdentity !== undefined && !backupIsOriginal)) {
        throw new TypeError('committed artifact removal lost its absent destination');
      }
      return;
    }
    if (destinationIsOriginal && artifact.backupIdentity === undefined) return;
    if (artifact.destinationIdentity === undefined && backupIsOriginal) return;
    throw new TypeError('prepared artifact removal identities changed');
  }
  if (state === 'committed') {
    if (!destinationIsStaged || artifact.stageIdentity !== undefined) {
      throw new TypeError('committed artifact transaction lost its published destination');
    }
    if (artifact.backupIdentity !== undefined && !backupIsOriginal) {
      throw new TypeError('committed artifact transaction backup identity changed');
    }
    return;
  }
  if (destinationIsOriginal && artifact.stageIdentity === undefined && artifact.backupIdentity === undefined) return;
  if (Number(destinationIsStaged) + Number(stageIsStaged) !== 1) {
    throw new TypeError('prepared artifact transaction staged identity changed');
  }
  if (artifact.originalIdentity === undefined) {
    if (artifact.backupIdentity !== undefined) {
      throw new TypeError('prepared artifact transaction has an unexpected backup');
    }
    if (artifact.destinationIdentity !== undefined && !destinationIsStaged) {
      throw new TypeError('prepared artifact transaction destination identity changed');
    }
    return;
  }
  if (Number(destinationIsOriginal) + Number(backupIsOriginal) !== 1) {
    throw new TypeError('prepared artifact transaction original identity changed');
  }
  if (artifact.destinationIdentity !== undefined && !destinationIsOriginal && !destinationIsStaged) {
    throw new TypeError('prepared artifact transaction destination identity changed');
  }
}

function recoverArtifact(
  artifact: RecoveryArtifact,
  state: JournalState,
  publicationLock: PublicationLock,
  filesystem: ArtifactFileSystem,
): void {
  const removal = artifact.stagedIdentity === undefined;
  if (state === 'committed') {
    assertPublicationLockOwned(publicationLock, filesystem);
    if (removal) {
      assertFileAbsent(
        artifact.destination,
        artifact.destination.filename,
        'committed artifact removal changed',
        filesystem,
      );
    }
    removeKnownFile(artifact.destination, artifact.journal.backupName, artifact.originalIdentity, filesystem);
    return;
  }
  if (!removal && sameOptionalIdentity(artifact.destinationIdentity, artifact.stagedIdentity)) {
    assertPublicationLockOwned(publicationLock, filesystem);
    assertKnownFile(artifact.destination, artifact.destination.filename, artifact.stagedIdentity, filesystem);
    assertFileAbsent(
      artifact.destination,
      artifact.journal.stageName,
      'prepared artifact transaction stage path changed',
      filesystem,
    );
    filesystem.rename(
      childPath(artifact.destination, artifact.destination.filename),
      childPath(artifact.destination, artifact.journal.stageName),
    );
    assertKnownFile(artifact.destination, artifact.journal.stageName, artifact.stagedIdentity, filesystem);
    assertFileAbsent(
      artifact.destination,
      artifact.destination.filename,
      'prepared artifact transaction destination changed',
      filesystem,
    );
  }
  if (
    artifact.originalIdentity !== undefined &&
    sameOptionalIdentity(artifact.backupIdentity, artifact.originalIdentity)
  ) {
    assertPublicationLockOwned(publicationLock, filesystem);
    assertKnownFile(artifact.destination, artifact.journal.backupName, artifact.originalIdentity, filesystem);
    assertFileAbsent(
      artifact.destination,
      artifact.destination.filename,
      'prepared artifact transaction destination changed',
      filesystem,
    );
    filesystem.rename(
      childPath(artifact.destination, artifact.journal.backupName),
      childPath(artifact.destination, artifact.destination.filename),
    );
    assertKnownFile(artifact.destination, artifact.destination.filename, artifact.originalIdentity, filesystem);
  }
  assertPublicationLockOwned(publicationLock, filesystem);
  if (!removal) {
    removeKnownFile(artifact.destination, artifact.journal.stageName, artifact.stagedIdentity, filesystem);
  }
}

function encodeJournal(journal: TransactionJournal): string {
  return `${JSON.stringify(journal)}\n`;
}

function decodePublicationLockLine(source: string): unknown {
  try {
    return JSON.parse(source);
  } catch (error: unknown) {
    throw new TypeError('artifact publication lock record is corrupt', { cause: error });
  }
}

function decodeUnjournaledStage(value: unknown): UnjournaledStage {
  if (
    !isRecord(value) ||
    !hasExactKeys(value, ['canonicalPath', 'stageName', 'stagedIdentity']) ||
    typeof value['canonicalPath'] !== 'string' ||
    typeof value['stageName'] !== 'string' ||
    !isSerializedIdentity(value['stagedIdentity'])
  ) {
    throw new TypeError('artifact publication lock stage is invalid');
  }
  return {
    canonicalPath: value['canonicalPath'],
    stageName: value['stageName'],
    stagedIdentity: value['stagedIdentity'],
  };
}

function decodeJournal(source: string): TransactionJournal {
  let parsed: unknown;
  try {
    parsed = JSON.parse(source);
  } catch (error: unknown) {
    throw new TypeError('artifact transaction journal is corrupt', { cause: error });
  }
  if (
    !isRecord(parsed) ||
    !hasExactKeys(parsed, ['artifacts', 'owner', 'schemaVersion', 'state']) ||
    parsed['schemaVersion'] !== 1 ||
    !isTransactionOwner(parsed['owner']) ||
    !isJournalState(parsed['state']) ||
    !Array.isArray(parsed['artifacts'])
  ) {
    throw new TypeError('artifact transaction journal has an invalid root');
  }
  const artifacts = parsed['artifacts'].map(decodeJournalArtifact);
  if (artifacts.length === 0) {
    throw new TypeError('artifact transaction journal must contain at least one artifact');
  }
  return {
    schemaVersion: 1,
    owner: parsed['owner'],
    state: parsed['state'],
    artifacts,
  };
}

function decodeJournalArtifact(value: unknown): JournalArtifact {
  if (
    !isRecord(value) ||
    !hasExactKeys(value, ['backupName', 'canonicalPath', 'originalIdentity', 'stageName', 'stagedIdentity'])
  ) {
    throw new TypeError('artifact transaction journal entry must be an exact object');
  }
  const canonicalPath = value['canonicalPath'];
  const stageName = value['stageName'];
  const backupName = value['backupName'];
  const originalIdentity = value['originalIdentity'];
  const stagedIdentity = value['stagedIdentity'];
  if (
    typeof canonicalPath !== 'string' ||
    typeof stageName !== 'string' ||
    typeof backupName !== 'string' ||
    !(originalIdentity === null || isSerializedIdentity(originalIdentity)) ||
    !(stagedIdentity === null || isSerializedIdentity(stagedIdentity))
  ) {
    throw new TypeError('artifact transaction journal entry is invalid');
  }
  return {
    canonicalPath,
    stageName,
    backupName,
    stagedIdentity,
    originalIdentity,
  };
}

function comparableJournal(journal: TransactionJournal): string {
  return JSON.stringify({
    schemaVersion: journal.schemaVersion,
    owner: journal.owner,
    artifacts: journal.artifacts,
  });
}

function isTransactionName(value: string, kind: 'backup' | 'stage', filename: string): boolean {
  const prefix = `.${filename}.tslean-${kind}-`;
  return value.startsWith(prefix) && isTransactionId(value.slice(prefix.length));
}

function isTransactionId(value: unknown): value is string {
  return (
    typeof value === 'string' &&
    /^[0-9a-f]{8}-[0-9a-f]{4}-[1-5][0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$/u.test(value)
  );
}

function isTransactionOwner(value: unknown): value is TransactionOwner {
  return (
    isRecord(value) &&
    hasExactKeys(value, ['processId', 'processStartTime', 'transactionId']) &&
    typeof value['processId'] === 'number' &&
    Number.isSafeInteger(value['processId']) &&
    value['processId'] > 0 &&
    typeof value['processStartTime'] === 'string' &&
    /^\d+$/u.test(value['processStartTime']) &&
    isTransactionId(value['transactionId'])
  );
}

function currentTransactionOwner(): TransactionOwner {
  const processStartTime = readProcessStartTime(process.pid);
  if (processStartTime === undefined) {
    throw new TypeError('artifact publication cannot identify the current process');
  }
  return { processId: process.pid, processStartTime, transactionId: randomUUID() };
}

function transactionOwnerIsLive(owner: TransactionOwner): boolean {
  return readProcessStartTime(owner.processId) === owner.processStartTime;
}

function sameTransactionOwner(left: TransactionOwner, right: TransactionOwner): boolean {
  return (
    left.processId === right.processId &&
    left.processStartTime === right.processStartTime &&
    left.transactionId === right.transactionId
  );
}

function readProcessStartTime(processId: number): string | undefined {
  let source: string;
  try {
    source = readFileSync(`/proc/${processId}/stat`, 'utf8');
  } catch (error: unknown) {
    if (hasErrorCode(error, 'ENOENT', 'ESRCH')) return undefined;
    throw error;
  }
  const commandEnd = source.lastIndexOf(') ');
  if (commandEnd === -1) throw new TypeError('artifact publication process identity is invalid');
  const fieldsAfterCommand = source
    .slice(commandEnd + 2)
    .trim()
    .split(/\s+/u);
  const startTime = fieldsAfterCommand[19];
  if (startTime === undefined || !/^\d+$/u.test(startTime)) {
    throw new TypeError('artifact publication process identity is invalid');
  }
  return startTime;
}

function isJournalState(value: unknown): value is JournalState {
  return value === 'prepared' || value === 'committed';
}

function isSerializedIdentity(value: unknown): value is SerializedIdentity {
  return (
    isRecord(value) &&
    hasExactKeys(value, ['device', 'inode']) &&
    typeof value['device'] === 'string' &&
    /^\d+$/u.test(value['device']) &&
    typeof value['inode'] === 'string' &&
    /^\d+$/u.test(value['inode'])
  );
}

function hasExactKeys(value: Record<string, unknown>, keys: readonly string[]): boolean {
  const actual = Object.keys(value).sort();
  return actual.length === keys.length && actual.every((key, index) => key === keys[index]);
}

function serializeIdentity(value: FileIdentity): SerializedIdentity {
  return { device: value.device.toString(), inode: value.inode.toString() };
}

function deserializeIdentity(value: SerializedIdentity): FileIdentity {
  return { device: BigInt(value.device), inode: BigInt(value.inode) };
}

function transactionJournalName(scope: ArtifactTransactionScope): string {
  const digest = createHash('sha256')
    .update(JSON.stringify([scope.identity]))
    .digest('hex');
  return `.tslean-transaction-${digest}.json`;
}

function committedJournalName(journalName: string): string {
  return `${journalName}.committed`;
}

function removeCurrentJournalCopies(
  destinations: readonly BoundDestination[],
  journalName: string,
  owner: TransactionOwner,
  publicationLock: PublicationLock,
  filesystem: ArtifactFileSystem,
): Error | undefined {
  try {
    const copies: { readonly destination: BoundDestination; readonly identity: FileIdentity; readonly name: string }[] =
      [];
    for (const destination of uniqueDirectories(destinations)) {
      for (const name of [journalName, committedJournalName(journalName)]) {
        assertPublicationLockOwned(publicationLock, filesystem);
        const path = childPath(destination, name);
        const journalIdentity = fileIdentity(path, filesystem);
        if (journalIdentity === undefined) continue;
        const journal = decodeJournal(filesystem.read(path));
        assertPublicationLockOwned(publicationLock, filesystem);
        if (!sameTransactionOwner(journal.owner, owner)) {
          throw new TypeError('artifact transaction journal belongs to a different publisher');
        }
        copies.push({ destination, identity: journalIdentity, name });
      }
    }
    for (const copy of copies) {
      assertPublicationLockOwned(publicationLock, filesystem);
      removeKnownFile(copy.destination, copy.name, copy.identity, filesystem);
    }
    return undefined;
  } catch (error: unknown) {
    return error instanceof Error ? error : new TypeError(String(error));
  }
}

function uniqueDirectories(destinations: readonly BoundDestination[]): readonly BoundDestination[] {
  const unique = new Map<string, BoundDestination>();
  for (const destination of destinations) {
    unique.set(`${destination.directoryIdentity.device}:${destination.directoryIdentity.inode}`, destination);
  }
  return [...unique.values()];
}

function removeKnownFile(
  destination: BoundDestination,
  name: string,
  expected: FileIdentity | undefined,
  filesystem: ArtifactFileSystem,
): void {
  if (expected === undefined) return;
  const path = childPath(destination, name);
  const actual = fileIdentity(path, filesystem);
  if (actual === undefined) return;
  if (!sameIdentity(actual, expected)) throw new TypeError('artifact transaction file identity changed');
  filesystem.remove(path);
}

function assertKnownFile(
  destination: BoundDestination,
  name: string,
  expected: FileIdentity,
  filesystem: ArtifactFileSystem,
): void {
  const actual = fileIdentity(childPath(destination, name), filesystem);
  if (actual === undefined || !sameIdentity(actual, expected)) {
    throw new TypeError('artifact transaction file identity changed');
  }
}

function assertFileAbsent(
  destination: BoundDestination,
  name: string,
  message: string,
  filesystem: ArtifactFileSystem,
): void {
  if (fileIdentity(childPath(destination, name), filesystem) !== undefined) throw new TypeError(message);
}

function assertBoundRoute(destination: BoundDestination, filesystem: ArtifactFileSystem): void {
  const actualDirectory = identity(filesystem.fstat(destination.directoryDescriptor));
  if (!sameIdentity(actualDirectory, destination.directoryIdentity)) {
    throw new TypeError('artifact destination directory handle changed');
  }
  let namedDirectory: FileIdentity;
  try {
    namedDirectory = identity(filesystem.stat(destination.directoryPath));
  } catch (error: unknown) {
    if (hasErrorCode(error, 'ENOENT', 'ENOTDIR')) {
      throw new TypeError('artifact destination changed during compilation', { cause: error });
    }
    throw error;
  }
  if (!sameIdentity(namedDirectory, destination.directoryIdentity)) {
    throw new TypeError('artifact destination changed during compilation');
  }
  if (canonicalDestination(destination.path, filesystem) !== destination.canonicalPath) {
    throw new TypeError('artifact destination changed during compilation');
  }
}

function canonicalDestination(path: string, filesystem: ArtifactFileSystem): string {
  const parent = filesystem.realpath(dirname(path));
  return realpathIfPresent(path, filesystem) ?? join(parent, basename(path));
}

function realpathIfPresent(path: string, filesystem: ArtifactFileSystem): string | undefined {
  try {
    return filesystem.realpath(path);
  } catch (error: unknown) {
    if (hasErrorCode(error, 'ENOENT')) return undefined;
    throw error;
  }
}

function syncDirectories(destinations: readonly BoundDestination[], filesystem: ArtifactFileSystem): void {
  const synchronized = new Set<string>();
  for (const destination of destinations) {
    const key = `${destination.directoryIdentity.device}:${destination.directoryIdentity.inode}`;
    if (synchronized.has(key)) continue;
    filesystem.fsync(destination.directoryDescriptor);
    synchronized.add(key);
  }
}

function fileIdentity(path: string, filesystem: ArtifactFileSystem): FileIdentity | undefined {
  try {
    const metadata = filesystem.lstat(path);
    if (!metadata.isFile()) throw new TypeError('artifact transaction target must be a regular file');
    return identity(metadata);
  } catch (error: unknown) {
    if (hasErrorCode(error, 'ENOENT')) return undefined;
    throw error;
  }
}

function identity(metadata: Pick<ArtifactMetadata, 'dev' | 'ino'>): FileIdentity {
  return { device: metadata.dev, inode: metadata.ino };
}

function sameIdentity(left: FileIdentity, right: FileIdentity): boolean {
  return left.device === right.device && left.inode === right.inode;
}

function optionalSameIdentity(left: FileIdentity | undefined, right: FileIdentity | undefined): boolean {
  return left === undefined ? right === undefined : right !== undefined && sameIdentity(left, right);
}

function sameOptionalIdentity(left: FileIdentity | undefined, right: FileIdentity): boolean {
  return left !== undefined && sameIdentity(left, right);
}

function childPath(destination: BoundDestination, name: string): string {
  return `${destination.descriptorPath}/${name}`;
}

function transactionName(filename: string, kind: 'backup' | 'stage'): string {
  return `.${filename}.tslean-${kind}-${randomUUID()}`;
}

function lockDescriptor(descriptor: number): void {
  const inheritedDescriptor = 3;
  const result = spawnSync('/usr/bin/flock', ['--exclusive', String(inheritedDescriptor)], {
    encoding: 'utf8',
    stdio: ['ignore', 'pipe', 'pipe', descriptor],
  });
  if (result.error !== undefined) {
    throw new TypeError(`artifact publication lock could not start: ${result.error.message}`);
  }
  if (result.status !== 0) {
    const detail = result.stderr.trim();
    throw new TypeError(`artifact publication lock failed${detail.length === 0 ? '' : `: ${detail}`}`);
  }
}

function platformConstant(name: 'O_DIRECTORY' | 'O_NOFOLLOW'): number {
  const value: unknown = constants[name];
  if (typeof value !== 'number') throw new TypeError(`artifact publication requires ${name}`);
  return value;
}

function hasErrorCode(error: unknown, ...codes: readonly string[]): boolean {
  return error instanceof Error && 'code' in error && typeof error.code === 'string' && codes.includes(error.code);
}

function isRecord(value: unknown): value is Record<string, unknown> {
  return typeof value === 'object' && value !== null && !Array.isArray(value);
}
