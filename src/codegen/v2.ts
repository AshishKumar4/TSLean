/**
 * @module codegen/v2
 *
 * V2 codegen entry point: IR → LeanAST → Text.
 * Replaces the string-building approach of V1 with a typed AST intermediate.
 */

import type { IRModule } from '../ir/types.js';
import { lowerModule } from './lower.js';
import { printFile } from './printer.js';
import type { LeanFile, LeanDecl } from './lean-ast.js';

export interface CodegenOptions {
  /** Self-host mode: rewrite namespaces/imports for TSLean.Generated.SelfHost.* */
  selfHost?: boolean;
  /** Output file basename (used in self-host mode for namespace mapping) */
  baseName?: string;
}

/**
 * Generate Lean 4 source code from an IR module using the V2 pipeline.
 */
export function generateLeanV2(mod: IRModule, opts?: CodegenOptions): string {
  let leanFile = lowerModule(mod);
  if (opts?.selfHost) {
    leanFile = applySelfHostTransforms(leanFile, opts.baseName ?? mod.name);
  }
  return printFile(leanFile);
}

// ─── Self-host transforms ───────────────────────────────────────────────────────

/** Namespace mapping: IR module name → SelfHost lean name */
const NS_MAP: Record<string, string> = {
  'TSLean.Generated.Types': 'TSLean.Generated.SelfHost.ir_types',
  'TSLean.Generated.EffectsIndex': 'TSLean.Generated.SelfHost.EffectsIndex',
  'TSLean.Generated.StdlibIndex': 'TSLean.Generated.SelfHost.StdlibIndex',
  'TSLean.Generated.TypemapIndex': 'TSLean.Generated.SelfHost.TypemapIndex',
  'TSLean.Generated.RewriteIndex': 'TSLean.Generated.SelfHost.RewriteIndex',
  'TSLean.Generated.VerificationIndex': 'TSLean.Generated.SelfHost.VerificationIndex',
  'TSLean.Generated.DoModelAmbient': 'TSLean.Generated.SelfHost.DoModelAmbient',
  'TSLean.Generated.CodegenIndex': 'TSLean.Generated.SelfHost.CodegenIndex',
  'TSLean.Generated.ParserIndex': 'TSLean.Generated.SelfHost.ParserIndex',
  'TSLean.Generated.ProjectIndex': 'TSLean.Generated.SelfHost.ProjectIndex',
  'TSLean.Generated.SrcCli': 'TSLean.Generated.SelfHost.SrcCli',
};

/** Import path rewriting for self-host */
const IMPORT_MAP: Record<string, string> = {
  'TSLean.Generated.Ir.Types': 'TSLean.Generated.SelfHost.ir_types',
  'TSLean.Generated.Effects.Index': 'TSLean.Generated.SelfHost.effects_index',
  'TSLean.Generated.Stdlib.Index': 'TSLean.Generated.SelfHost.stdlib_index',
  'TSLean.Generated.Typemap.Index': 'TSLean.Generated.SelfHost.typemap_index',
  'TSLean.Generated.DoModel.Ambient': 'TSLean.Generated.SelfHost.DoModel_Ambient',
  'TSLean.Generated.Codegen.Index': 'TSLean.Generated.SelfHost.codegen_index',
  'TSLean.Generated.Parser.Index': 'TSLean.Generated.SelfHost.parser_index',
  'TSLean.Generated.Rewrite.Index': 'TSLean.Generated.SelfHost.rewrite_index',
  'TSLean.Generated.Verification.Index': 'TSLean.Generated.SelfHost.verification_index',
  'TSLean.Generated.Project.Index': 'TSLean.Generated.SelfHost.project_index',
};

function applySelfHostTransforms(file: LeanFile, baseName: string): LeanFile {
  const newDecls: LeanDecl[] = [];
  const isIrTypes = baseName === 'ir_types';

  // Rewrite imports
  for (const d of file.decls) {
    if (d.tag === 'Import') {
      const mapped = IMPORT_MAP[d.module];
      if (mapped) {
        newDecls.push({ tag: 'Import', module: mapped });
      } else {
        newDecls.push(d);
      }
      continue;
    }
    if (d.tag === 'Open') {
      // Add TSLean.Generated.Types to opens if ir_types is imported
      const hasTypes = newDecls.some(x =>
        x.tag === 'Import' && x.module.includes('ir_types'));
      if (hasTypes) {
        newDecls.push({ tag: 'Open', namespaces: [...d.namespaces, 'TSLean.Generated.Types'] });
      } else {
        newDecls.push(d);
      }
      continue;
    }
    if (d.tag === 'Namespace') {
      const mappedName = NS_MAP[d.name] ?? `TSLean.Generated.SelfHost.${capitalize(baseName)}`;
      newDecls.push({ ...d, name: mappedName });
      continue;
    }
    newDecls.push(d);
  }

  // Inject Prelude and ir_types imports at the top (after existing imports)
  if (!isIrTypes) {
    const firstNonImport = newDecls.findIndex(d => d.tag !== 'Import' && d.tag !== 'Blank');
    const preludeImports: LeanDecl[] = [
      { tag: 'Import', module: 'TSLean.Generated.SelfHost.Prelude' },
    ];
    if (!newDecls.some(d => d.tag === 'Import' && d.module.includes('ir_types'))) {
      preludeImports.push({ tag: 'Import', module: 'TSLean.Generated.SelfHost.ir_types' });
    }
    newDecls.splice(firstNonImport >= 0 ? firstNonImport : 0, 0, ...preludeImports);
  }

  return { ...file, decls: newDecls };
}

function capitalize(s: string): string {
  return s.charAt(0).toUpperCase() + s.slice(1);
}
