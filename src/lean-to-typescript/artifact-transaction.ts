import { createHash, randomUUID } from 'node:crypto';
import {
  closeSync,
  constants,
  existsSync,
  fstatSync,
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
  lstat(path: string): ArtifactMetadata;
  mkdir(path: string): void;
  open(path: string, flags: number, mode?: number): number;
  read(path: string): string;
  realpath(path: string): string;
  remove(path: string): void;
  rename(from: string, to: string): void;
  stat(path: string): ArtifactMetadata;
  write(descriptor: number, contents: string): void;
}

export const nodeArtifactFileSystem: ArtifactFileSystem = Object.freeze({
  close: closeSync,
  exists: existsSync,
  fstat: (descriptor: number) => fstatSync(descriptor, { bigint: true }),
  fsync: fsyncSync,
  lstat: (path: string) => lstatSync(path, { bigint: true }),
  mkdir: (path: string) => mkdirSync(path, { recursive: true }),
  open: (path: string, flags: number, mode?: number) =>
    mode === undefined ? openSync(path, flags) : openSync(path, flags, mode),
  read: (path: string) => readFileSync(path, 'utf8'),
  realpath: realpathSync,
  remove: (path: string) => rmSync(path),
  rename: renameSync,
  stat: (path: string) => statSync(path, { bigint: true }),
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
  readonly transactionId: string;
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
): void {
  publishArtifactPairWithFileSystem(destinations, contents, nodeArtifactFileSystem);
}

export function publishArtifactPairWithFileSystem(
  destinations: readonly [ArtifactDestination, ArtifactDestination],
  contents: readonly [string, string],
  filesystem: ArtifactFileSystem,
): void {
  const bound = bindDestinations(destinations, filesystem);
  const staged: StagedArtifact[] = [];
  const journalName = transactionJournalName(bound);
  let durablyCommitted = false;
  try {
    recoverBoundArtifactPair(bound, journalName, filesystem);
    for (let index = 0; index < bound.length; index += 1) {
      const destination = bound[index];
      const artifactContents = contents[index];
      if (destination === undefined || artifactContents === undefined) {
        throw new TypeError('artifact transaction requires exactly two destinations and contents');
      }
      staged.push(stageArtifact(destination, artifactContents, filesystem));
    }
    const prepared = transactionJournal(staged, 'prepared');
    writeJournalCopies(bound, journalName, prepared, filesystem);
    syncDirectories(bound, filesystem);
    for (const artifact of staged) assertDestinationUnchanged(artifact, filesystem);
    for (const artifact of staged) moveOriginalToBackup(artifact, filesystem);
    for (const artifact of staged) moveStageToDestination(artifact, filesystem);
    syncDirectories(bound, filesystem);
    for (const destination of bound) assertBoundRoute(destination, filesystem);
    const committed = { ...prepared, state: 'committed' } as const;
    for (const directory of uniqueDirectories(bound)) {
      writeBoundFile(directory, committedJournalName(journalName), encodeJournal(committed), filesystem);
      filesystem.fsync(directory.directoryDescriptor);
      durablyCommitted = true;
    }
    finishCommittedTransaction(staged, bound, journalName, filesystem);
  } catch (error: unknown) {
    if (durablyCommitted) {
      try {
        finishCommittedTransaction(staged, bound, journalName, filesystem);
      } catch (cleanupError: unknown) {
        void cleanupError;
      }
      return;
    }
    const rollbackError = rollback(staged, bound, filesystem);
    const journalCleanupError = removeCurrentJournalCopies(bound, journalName, filesystem);
    if (rollbackError !== undefined || journalCleanupError !== undefined) {
      const detail = rollbackError?.message ?? journalCleanupError?.message ?? 'unknown recovery failure';
      throw new TypeError(`artifact publication failed and rollback failed: ${detail}`, { cause: error });
    }
    throw error;
  } finally {
    if (!durablyCommitted) {
      for (const artifact of staged) cleanupUnpublishedFiles(artifact, filesystem);
    }
    for (const destination of bound) filesystem.close(destination.directoryDescriptor);
  }
}

export function recoverArtifactPairWithFileSystem(
  destinations: readonly [ArtifactDestination, ArtifactDestination],
  filesystem: ArtifactFileSystem,
): void {
  const bound = bindDestinations(destinations, filesystem);
  try {
    recoverBoundArtifactPair(bound, transactionJournalName(bound), filesystem);
  } finally {
    for (const destination of bound) filesystem.close(destination.directoryDescriptor);
  }
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
  filesystem: ArtifactFileSystem,
): void {
  const source = encodeJournal(journal);
  for (const destination of uniqueDirectories(destinations)) {
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
  filesystem: ArtifactFileSystem,
): Error | undefined {
  try {
    for (const artifact of [...artifacts].reverse()) {
      if (artifact.stagedMoved) {
        removeKnownFile(artifact.destination, artifact.destination.filename, artifact.stagedIdentity, filesystem);
        artifact.stagedMoved = false;
      }
      if (artifact.originalMoved) {
        const backupIdentity = fileIdentity(childPath(artifact.destination, artifact.backupName), filesystem);
        if (!optionalSameIdentity(backupIdentity, artifact.originalIdentity)) {
          throw new TypeError('artifact rollback backup identity changed');
        }
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

function cleanupUnpublishedFiles(artifact: StagedArtifact, filesystem: ArtifactFileSystem): void {
  if (!artifact.stagedMoved) {
    removeKnownFile(artifact.destination, artifact.stageName, artifact.stagedIdentity, filesystem);
  }
  if (artifact.originalMoved) return;
  removeKnownFile(artifact.destination, artifact.backupName, artifact.originalIdentity, filesystem);
}

function finishCommittedTransaction(
  artifacts: readonly StagedArtifact[],
  destinations: readonly BoundDestination[],
  journalName: string,
  filesystem: ArtifactFileSystem,
): void {
  for (const artifact of artifacts) {
    removeKnownFile(artifact.destination, artifact.backupName, artifact.originalIdentity, filesystem);
    artifact.originalMoved = false;
  }
  syncDirectories(destinations, filesystem);
  const journalCleanupError = removeCurrentJournalCopies(destinations, journalName, filesystem);
  if (journalCleanupError !== undefined) throw journalCleanupError;
  syncDirectories(destinations, filesystem);
}

function transactionJournal(artifacts: readonly StagedArtifact[], state: JournalState): TransactionJournal {
  const entries = artifacts.map((artifact): JournalArtifact => ({
    canonicalPath: artifact.destination.canonicalPath,
    stageName: artifact.stageName,
    backupName: artifact.backupName,
    stagedIdentity: serializeIdentity(artifact.stagedIdentity),
    originalIdentity: artifact.originalIdentity === undefined ? null : serializeIdentity(artifact.originalIdentity),
  }));
  if (entries.length !== 2 || entries[0] === undefined || entries[1] === undefined) {
    throw new TypeError('artifact transaction journal requires exactly two artifacts');
  }
  return { schemaVersion: 1, transactionId: randomUUID(), state, artifacts: [entries[0], entries[1]] };
}

function recoverBoundArtifactPair(
  destinations: readonly BoundDestination[],
  journalName: string,
  filesystem: ArtifactFileSystem,
): void {
  const copies = uniqueDirectories(destinations)
    .flatMap((destination) =>
      [journalName, committedJournalName(journalName)].map((name) => ({
        destination,
        path: childPath(destination, name),
      })),
    )
    .filter(({ path }) => filesystem.exists(path))
    .map((copy) => {
      if (fileIdentity(copy.path, filesystem) === undefined) {
        throw new TypeError('artifact transaction journal disappeared');
      }
      return copy;
    });
  if (copies.length === 0) return;
  const journals = copies.map(({ path }) => decodeJournal(filesystem.read(path)));
  const first = journals[0];
  if (first === undefined) throw new TypeError('artifact transaction journal disappeared');
  const expectedTransaction = comparableJournal(first);
  if (journals.some((journal) => comparableJournal(journal) !== expectedTransaction)) {
    throw new TypeError('artifact transaction journals disagree');
  }
  const state: JournalState = journals.some((journal) => journal.state === 'committed') ? 'committed' : 'prepared';
  const recovery = prepareRecovery(destinations, first, state, filesystem);
  for (const artifact of recovery) recoverArtifact(artifact, state, filesystem);
  syncDirectories(destinations, filesystem);
  const cleanupError = removeCurrentJournalCopies(destinations, journalName, filesystem);
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
  for (let index = 0; index < destinations.length; index += 1) {
    const destination = destinations[index];
    const artifact = journal.artifacts[index];
    if (destination === undefined || artifact === undefined || artifact.canonicalPath !== destination.canonicalPath) {
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
  const destinationIsOriginal = optionalSameIdentity(artifact.destinationIdentity, artifact.originalIdentity);
  const backupIsOriginal = optionalSameIdentity(artifact.backupIdentity, artifact.originalIdentity);
  if (Number(destinationIsOriginal) + Number(backupIsOriginal) !== 1) {
    throw new TypeError('prepared artifact transaction original identity changed');
  }
  if (artifact.destinationIdentity !== undefined && !destinationIsOriginal && !destinationIsStaged) {
    throw new TypeError('prepared artifact transaction destination identity changed');
  }
}

function recoverArtifact(artifact: RecoveryArtifact, state: JournalState, filesystem: ArtifactFileSystem): void {
  if (state === 'committed') {
    removeKnownFile(artifact.destination, artifact.journal.backupName, artifact.originalIdentity, filesystem);
    return;
  }
  if (sameOptionalIdentity(artifact.destinationIdentity, artifact.stagedIdentity)) {
    removeKnownFile(artifact.destination, artifact.destination.filename, artifact.stagedIdentity, filesystem);
  }
  if (
    artifact.originalIdentity !== undefined &&
    sameOptionalIdentity(artifact.backupIdentity, artifact.originalIdentity)
  ) {
    filesystem.rename(
      childPath(artifact.destination, artifact.journal.backupName),
      childPath(artifact.destination, artifact.destination.filename),
    );
  }
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
    !hasExactKeys(parsed, ['artifacts', 'schemaVersion', 'state', 'transactionId']) ||
    parsed['schemaVersion'] !== 1 ||
    !isTransactionId(parsed['transactionId']) ||
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
    transactionId: parsed['transactionId'],
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
    transactionId: journal.transactionId,
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
  const digest = createHash('sha256')
    .update(JSON.stringify(destinations.map((destination) => destination.canonicalPath)))
    .digest('hex');
  return `.tslean-transaction-${digest}.json`;
}

function committedJournalName(journalName: string): string {
  return `${journalName}.committed`;
}

function removeCurrentJournalCopies(
  destinations: readonly BoundDestination[],
  journalName: string,
  filesystem: ArtifactFileSystem,
): Error | undefined {
  try {
    for (const destination of uniqueDirectories(destinations)) {
      for (const name of [journalName, committedJournalName(journalName)]) {
        removeKnownFile(destination, name, fileIdentity(childPath(destination, name), filesystem), filesystem);
      }
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
