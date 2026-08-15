export interface LeanToTypeScriptPlatform {
  readonly name: NodeJS.Platform;
}

export const hostLeanToTypeScriptPlatform: LeanToTypeScriptPlatform = Object.freeze({ name: process.platform });

export function assertLeanToTypeScriptPlatform(platform: LeanToTypeScriptPlatform): void {
  if (platform.name !== 'linux') {
    throw new TypeError(`Lean-to-TypeScript v1 requires Linux; received ${platform.name}`);
  }
}
