export interface LeanToTypeScriptInput {
  readonly kind: 'compiler' | 'lean-module' | 'lean-project' | 'lean-source' | 'typescript';
  readonly identity: string;
  readonly sha256: string;
}

export interface LeanToTypeScriptManifest {
  readonly schemaVersion: 1;
  readonly fragmentVersion: string;
  readonly sourceModule: string;
  readonly declarations: readonly string[];
  readonly semanticIrSha256: string;
  readonly inputClosureSha256: string;
  readonly generatedBodySha256: string;
  readonly inputs: readonly LeanToTypeScriptInput[];
  readonly typescriptVersion: string;
  readonly runtime: string;
  readonly leanToolchain: {
    readonly identity: string;
    readonly leanVersion: string;
    readonly lakeVersion: string;
  };
}

export interface LeanToTypeScriptArtifact {
  readonly code: string;
  readonly manifest: LeanToTypeScriptManifest;
}
