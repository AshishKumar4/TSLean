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

interface StagedArtifact {
  readonly destination: BoundDestination;
  readonly stageName: string;
  readonly backupName: string;
  readonly stagedIdentity: FileIdentity;
  readonly originalIdentity: FileIdentity | undefined;
  originalMoved: boolean;
  stagedMoved: boolean;
}

interface JournalArtifact {
  readonly canonicalPath: string;
  readonly stageName: string;
  readonly backupName: string;
  readonly stagedIdentity: SerializedIdentity;
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
  readonly artifacts: readonly [JournalArtifact, JournalArtifact];
}

interface RecoveryArtifact {
  readonly destination: BoundDestination;
  readonly journal: JournalArtifact;
  readonly stagedIdentity: FileIdentity;
  readonly originalIdentity: FileIdentity | undefined;
  readonly destinationIdentity: FileIdentity | undefined;
  readonly stageIdentity: FileIdentity | undefined;
  readonly backupIdentity: FileIdentity | undefined;
}

export function publishArtifactPair(
  destinations: readonly [ArtifactDestination, ArtifactDestination],
  contents: readonly [string, string],
  platform: LeanToTypeScriptPlatform = hostLeanToTypeScriptPlatform,
): void {
  publishArtifactPairWithFileSystem(destinations, contents, nodeArtifactFileSystem, platform);
}

export function publishArtifactPairWithFileSystem(
  destinations: readonly [ArtifactDestination, ArtifactDestination],
  contents: readonly [string, string],
  filesystem: ArtifactFileSystem,
  platform: LeanToTypeScriptPlatform = hostLeanToTypeScriptPlatform,
): void {
  assertLeanToTypeScriptPlatform(platform);
  const bound = bindDestinations(destinations, filesystem);
  let publicationLock: PublicationLock | undefined;
  let transactionOwner: TransactionOwner | undefined;
  const staged: StagedArtifact[] = [];
  const journalName = transactionJournalName(bound);
  let durablyCommitted = false;
  let removePublicationLockWhenFinished = false;
  try {
    publicationLock = acquirePublicationLock(bound, journalName, filesystem);
    for (const destination of bound) assertBoundRoute(destination, filesystem);
    recoverBoundArtifactPair(bound, journalName, publicationLock, filesystem);
    transactionOwner = currentTransactionOwner();
    writePublicationLockOwner(publicationLock, transactionOwner, filesystem);
    for (let index = 0; index < bound.length; index += 1) {
      const destination = bound[index];
      const artifactContents = contents[index];
      if (destination === undefined || artifactContents === undefined) {
        throw new TypeError('artifact transaction requires exactly two destinations and contents');
      }
      assertPublicationLockOwned(publicationLock, filesystem);
      staged.push(stageArtifact(destination, artifactContents, filesystem));
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
    for (const artifact of staged) {
      assertPublicationLockOwned(publicationLock, filesystem);
      moveStageToDestination(artifact, filesystem);
    }
    syncDirectories(bound, filesystem);
    for (const destination of bound) assertBoundRoute(destination, filesystem);
    const committed = { ...prepared, state: 'committed' } as const;
    for (const directory of uniqueDirectories(bound)) {
      writeBoundFile(directory, committedJournalName(journalName), encodeJournal(committed), filesystem);
      filesystem.fsync(directory.directoryDescriptor);
      durablyCommitted = true;
    }
    assertPublicationLockOwned(publicationLock, filesystem);
    finishCommittedTransaction(staged, bound, journalName, transactionOwner, publicationLock, filesystem);
    removePublicationLockWhenFinished = true;
  } catch (error: unknown) {
    if (publicationLock === undefined) throw error;
    if (!publicationLockIsOwned(publicationLock, filesystem)) {
      throw new TypeError('artifact publication lock identity changed', { cause: error });
    }
    if (durablyCommitted) {
      try {
        if (transactionOwner !== undefined) {
          finishCommittedTransaction(staged, bound, journalName, transactionOwner, publicationLock, filesystem);
          removePublicationLockWhenFinished = true;
        }
      } catch (cleanupError: unknown) {
        void cleanupError;
      }
      return;
    }
    const rollbackError = rollback(staged, bound, publicationLock, filesystem);
    const journalCleanupError =
      transactionOwner === undefined
        ? undefined
        : removeCurrentJournalCopies(bound, journalName, transactionOwner, publicationLock, filesystem);
    if (rollbackError !== undefined || journalCleanupError !== undefined) {
      const detail = rollbackError?.message ?? journalCleanupError?.message ?? 'unknown recovery failure';
      throw new TypeError(`artifact publication failed and rollback failed: ${detail}`, { cause: error });
    }
    removePublicationLockWhenFinished = transactionOwner !== undefined;
    throw error;
  } finally {
    try {
      if (!durablyCommitted && publicationLock !== undefined && publicationLockIsOwned(publicationLock, filesystem)) {
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

export function recoverArtifactPairWithFileSystem(
  destinations: readonly [ArtifactDestination, ArtifactDestination],
  filesystem: ArtifactFileSystem,
): void {
  const bound = bindDestinations(destinations, filesystem);
  let publicationLock: PublicationLock | undefined;
  let recoveryFinished = false;
  try {
    publicationLock = acquirePublicationLock(bound, transactionJournalName(bound), filesystem);
    for (const destination of bound) assertBoundRoute(destination, filesystem);
    recoverBoundArtifactPair(bound, transactionJournalName(bound), publicationLock, filesystem);
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

function acquirePublicationLock(
  destinations: readonly [BoundDestination, BoundDestination],
  journalName: string,
  filesystem: ArtifactFileSystem,
): PublicationLock {
  const destination = [...destinations].sort((left, right) =>
    compareCodePoints(left.canonicalPath, right.canonicalPath),
  )[0];
  if (destination === undefined) throw new TypeError('artifact publication requires exactly two destinations');
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

function readPublicationLockOwner(
  publicationLock: PublicationLock,
  filesystem: ArtifactFileSystem,
): TransactionOwner | undefined {
  assertPublicationLockOwned(publicationLock, filesystem);
  const source = filesystem.read(childPath(publicationLock.destination, publicationLock.name));
  assertPublicationLockOwned(publicationLock, filesystem);
  if (source.length === 0) return undefined;
  let parsed: unknown;
  try {
    parsed = JSON.parse(source);
  } catch (error: unknown) {
    throw new TypeError('artifact publication lock record is corrupt', { cause: error });
  }
  if (
    !isRecord(parsed) ||
    !hasExactKeys(parsed, ['owner', 'schemaVersion']) ||
    parsed['schemaVersion'] !== 1 ||
    !isTransactionOwner(parsed['owner'])
  ) {
    throw new TypeError('artifact publication lock record is invalid');
  }
  return parsed['owner'];
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

function bindDestinations(
  destinations: readonly [ArtifactDestination, ArtifactDestination],
  filesystem: ArtifactFileSystem,
): readonly [BoundDestination, BoundDestination] {
  const first = bindDestination(destinations[0], filesystem);
  try {
    const second = bindDestination(destinations[1], filesystem);
    const firstFile = fileIdentity(childPath(first, first.filename), filesystem);
    const secondFile = fileIdentity(childPath(second, second.filename), filesystem);
    if (
      sameIdentity(first.directoryIdentity, second.directoryIdentity) &&
      (first.filename === second.filename ||
        (firstFile !== undefined && secondFile !== undefined && sameIdentity(firstFile, secondFile)))
    ) {
      filesystem.close(second.directoryDescriptor);
      throw new TypeError('artifact destinations must identify distinct regular files');
    }
    return [first, second];
  } catch (error: unknown) {
    filesystem.close(first.directoryDescriptor);
    throw error;
  }
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
  contents: string,
  filesystem: ArtifactFileSystem,
): StagedArtifact {
  assertBoundRoute(destination, filesystem);
  const stageName = transactionName(destination.filename, 'stage');
  const backupName = transactionName(destination.filename, 'backup');
  const stagedIdentity = writeBoundFile(destination, stageName, contents, filesystem);
  return {
    destination,
    stageName,
    backupName,
    stagedIdentity,
    originalIdentity: fileIdentity(childPath(destination, destination.filename), filesystem),
    originalMoved: false,
    stagedMoved: false,
  };
}

function writeBoundFile(
  destination: BoundDestination,
  name: string,
  contents: string,
  filesystem: ArtifactFileSystem,
): FileIdentity {
  const path = childPath(destination, name);
  const descriptor = filesystem.open(
    path,
    constants.O_WRONLY | constants.O_CREAT | constants.O_EXCL | platformConstant('O_NOFOLLOW'),
    0o666,
  );
  try {
    filesystem.write(descriptor, contents);
    filesystem.fsync(descriptor);
    const writtenIdentity = identity(filesystem.fstat(descriptor));
    filesystem.close(descriptor);
    return writtenIdentity;
  } catch (error: unknown) {
    try {
      filesystem.close(descriptor);
    } catch (closeError: unknown) {
      void closeError;
    }
    removeKnownFile(destination, name, fileIdentity(path, filesystem), filesystem);
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
  if (artifact.originalIdentity === undefined) return;
  filesystem.rename(
    childPath(artifact.destination, artifact.destination.filename),
    childPath(artifact.destination, artifact.backupName),
  );
  artifact.originalMoved = true;
}

function moveStageToDestination(artifact: StagedArtifact, filesystem: ArtifactFileSystem): void {
  filesystem.rename(
    childPath(artifact.destination, artifact.stageName),
    childPath(artifact.destination, artifact.destination.filename),
  );
  artifact.stagedMoved = true;
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
        filesystem.rename(
          childPath(artifact.destination, artifact.backupName),
          childPath(artifact.destination, artifact.destination.filename),
        );
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
    removeKnownFile(artifact.destination, artifact.backupName, artifact.originalIdentity, filesystem);
    artifact.originalMoved = false;
  }
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
      stagedIdentity: serializeIdentity(artifact.stagedIdentity),
      originalIdentity: artifact.originalIdentity === undefined ? null : serializeIdentity(artifact.originalIdentity),
    }))
    .sort((left, right) => compareCodePoints(left.canonicalPath, right.canonicalPath));
  if (entries.length !== 2 || entries[0] === undefined || entries[1] === undefined) {
    throw new TypeError('artifact transaction journal requires exactly two artifacts');
  }
  return { schemaVersion: 1, owner, state, artifacts: [entries[0], entries[1]] };
}

function recoverBoundArtifactPair(
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
      if (journalIdentity === undefined) {
        throw new TypeError('artifact transaction journal disappeared');
      }
      return { ...copy, identity: journalIdentity };
    });
  if (copies.length === 0) return;
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
  const lockOwner = readPublicationLockOwner(publicationLock, filesystem);
  if (lockOwner === undefined) {
    if (transactionOwnerIsLive(first.owner)) {
      throw new TypeError('artifact transaction journal belongs to a live foreign publisher');
    }
  } else if (!sameTransactionOwner(lockOwner, first.owner)) {
    throw new TypeError('artifact transaction journal owner does not match the publication lock');
  }
  const state: JournalState = journals.some((journal) => journal.state === 'committed') ? 'committed' : 'prepared';
  const recovery = prepareRecovery(destinations, first, state, filesystem);
  for (const artifact of recovery) {
    assertPublicationLockOwned(publicationLock, filesystem);
    recoverArtifact(artifact, state, publicationLock, filesystem);
  }
  assertPublicationLockOwned(publicationLock, filesystem);
  syncDirectories(destinations, filesystem);
  const cleanupError = removeCurrentJournalCopies(destinations, journalName, first.owner, publicationLock, filesystem);
  if (cleanupError !== undefined) throw cleanupError;
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
      stagedIdentity: deserializeIdentity(artifact.stagedIdentity),
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
  const destinationIsStaged = optionalSameIdentity(artifact.destinationIdentity, artifact.stagedIdentity);
  const stageIsStaged = optionalSameIdentity(artifact.stageIdentity, artifact.stagedIdentity);
  if (state === 'committed') {
    if (!destinationIsStaged || artifact.stageIdentity !== undefined) {
      throw new TypeError('committed artifact transaction lost its published destination');
    }
    if (
      artifact.backupIdentity !== undefined &&
      !optionalSameIdentity(artifact.backupIdentity, artifact.originalIdentity)
    ) {
      throw new TypeError('committed artifact transaction backup identity changed');
    }
    return;
  }
  const destinationIsOriginal = optionalSameIdentity(artifact.destinationIdentity, artifact.originalIdentity);
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
  const backupIsOriginal = optionalSameIdentity(artifact.backupIdentity, artifact.originalIdentity);
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
  if (state === 'committed') {
    assertPublicationLockOwned(publicationLock, filesystem);
    removeKnownFile(artifact.destination, artifact.journal.backupName, artifact.originalIdentity, filesystem);
    return;
  }
  if (sameOptionalIdentity(artifact.destinationIdentity, artifact.stagedIdentity)) {
    assertPublicationLockOwned(publicationLock, filesystem);
    filesystem.rename(
      childPath(artifact.destination, artifact.destination.filename),
      childPath(artifact.destination, artifact.journal.stageName),
    );
  }
  if (
    artifact.originalIdentity !== undefined &&
    sameOptionalIdentity(artifact.backupIdentity, artifact.originalIdentity)
  ) {
    assertPublicationLockOwned(publicationLock, filesystem);
    filesystem.rename(
      childPath(artifact.destination, artifact.journal.backupName),
      childPath(artifact.destination, artifact.destination.filename),
    );
  }
  assertPublicationLockOwned(publicationLock, filesystem);
  removeKnownFile(artifact.destination, artifact.journal.stageName, artifact.stagedIdentity, filesystem);
}

function encodeJournal(journal: TransactionJournal): string {
  return `${JSON.stringify(journal)}\n`;
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
  if (artifacts.length !== 2 || artifacts[0] === undefined || artifacts[1] === undefined) {
    throw new TypeError('artifact transaction journal must contain exactly two artifacts');
  }
  return {
    schemaVersion: 1,
    owner: parsed['owner'],
    state: parsed['state'],
    artifacts: [artifacts[0], artifacts[1]],
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
  if (
    typeof canonicalPath !== 'string' ||
    typeof stageName !== 'string' ||
    typeof backupName !== 'string' ||
    !(originalIdentity === null || isSerializedIdentity(originalIdentity)) ||
    !isSerializedIdentity(value['stagedIdentity'])
  ) {
    throw new TypeError('artifact transaction journal entry is invalid');
  }
  return {
    canonicalPath,
    stageName,
    backupName,
    originalIdentity,
    stagedIdentity: value['stagedIdentity'],
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

function transactionJournalName(destinations: readonly BoundDestination[]): string {
  const canonicalPaths = destinations.map((destination) => destination.canonicalPath).sort(compareCodePoints);
  const digest = createHash('sha256').update(JSON.stringify(canonicalPaths)).digest('hex');
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
