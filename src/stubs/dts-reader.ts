// .d.ts reader: extract type declarations from TypeScript definition files
// and generate Lean stub modules (opaque types + axiomatized functions).

import * as ts from 'typescript';
import * as fs from 'fs';
import * as path from 'path';
import { capitalize } from '../utils.js';

// ─── Types ──────────────────────────────────────────────────────────────────────

export interface StubDecl {
  kind: 'opaque-type' | 'axiom-fn' | 'const' | 'class' | 'enum' | 'namespace';
  name: string;
  leanType?: string;         // Lean type signature
  typeParams?: string[];     // generic params
  doc?: string;              // doc comment
  members?: StubDecl[];      // namespace/class members
}

export interface StubModule {
  packageName: string;       // npm package name (e.g., 'node:fs')
  leanModule: string;        // Lean module name (e.g., 'TSLean.Stubs.NodeFs')
  decls: StubDecl[];
}

// ─── .d.ts extraction ───────────────────────────────────────────────────────────

/** Extract stub declarations from a .d.ts file. */
export function extractDtsStubs(dtsPath: string): StubDecl[] {
  const sourceText = fs.readFileSync(dtsPath, 'utf-8');
  const sf = ts.createSourceFile(dtsPath, sourceText, ts.ScriptTarget.ES2022, true);
  const decls: StubDecl[] = [];

  for (const stmt of sf.statements) {
    const d = extractStmt(stmt);
    if (d) decls.push(...(Array.isArray(d) ? d : [d]));
  }

  return decls;
}

function extractStmt(node: ts.Statement): StubDecl | StubDecl[] | null {
  // Exported function declarations
  if (ts.isFunctionDeclaration(node) && node.name && isExported(node)) {
    return extractFunctionDecl(node);
  }
  // Exported interface/type alias → opaque type
  if (ts.isInterfaceDeclaration(node) && isExported(node)) {
    return {
      kind: 'opaque-type',
      name: node.name.text,
      typeParams: node.typeParameters?.map(tp => tp.name.text),
      doc: getDoc(node),
    };
  }
  if (ts.isTypeAliasDeclaration(node) && isExported(node)) {
    return {
      kind: 'opaque-type',
      name: node.name.text,
      typeParams: node.typeParameters?.map(tp => tp.name.text),
      doc: getDoc(node),
    };
  }
  // Exported class → opaque type + constructor axiom
  if (ts.isClassDeclaration(node) && node.name && isExported(node)) {
    return extractClassDecl(node);
  }
  // Exported enum → inductive type
  if (ts.isEnumDeclaration(node) && isExported(node)) {
    return { kind: 'enum', name: node.name.text, doc: getDoc(node) };
  }
  // Module declaration (namespace)
  if (ts.isModuleDeclaration(node) && node.name) {
    const name = ts.isStringLiteral(node.name) ? node.name.text : node.name.text;
    const members = extractModuleBlock(node);
    if (members.length > 0) {
      return { kind: 'namespace', name, members, doc: getDoc(node) };
    }
  }
  // Variable declarations (exported constants)
  if (ts.isVariableStatement(node) && isExported(node)) {
    return node.declarationList.declarations
      .filter(d => ts.isIdentifier(d.name))
      .map(d => ({
        kind: 'const' as const,
        name: (d.name as ts.Identifier).text,
        leanType: d.type ? typeNodeToLean(d.type) : 'String',
        doc: getDoc(node),
      }));
  }
  return null;
}

function extractFunctionDecl(node: ts.FunctionDeclaration): StubDecl {
  const name = node.name!.text;
  const params = node.parameters.map(p => {
    const pName = ts.isIdentifier(p.name) ? p.name.text : '_';
    const pType = p.type ? typeNodeToLean(p.type) : 'String';
    return `(${pName} : ${pType})`;
  }).join(' ');
  const retType = node.type ? typeNodeToLean(node.type) : 'String';
  const typeParams = node.typeParameters?.map(tp => tp.name.text);
  const tpStr = typeParams?.map(t => `{${t} : Type}`).join(' ') ?? '';
  return {
    kind: 'axiom-fn',
    name,
    leanType: `${tpStr} ${params} : ${retType}`.trim(),
    typeParams,
    doc: getDoc(node),
  };
}

function extractClassDecl(node: ts.ClassDeclaration): StubDecl[] {
  const name = node.name!.text;
  const typeParams = node.typeParameters?.map(tp => tp.name.text);
  const decls: StubDecl[] = [{
    kind: 'opaque-type',
    name,
    typeParams,
    doc: getDoc(node),
  }];
  // Extract public methods as axioms
  for (const member of node.members) {
    if (ts.isMethodDeclaration(member) && member.name && ts.isIdentifier(member.name)) {
      const mName = member.name.text;
      const params = member.parameters.map(p => {
        const pName = ts.isIdentifier(p.name) ? p.name.text : '_';
        const pType = p.type ? typeNodeToLean(p.type) : 'String';
        return `(${pName} : ${pType})`;
      }).join(' ');
      const retType = member.type ? typeNodeToLean(member.type) : 'Unit';
      decls.push({
        kind: 'axiom-fn',
        name: `${name}.${mName}`,
        leanType: `(self : ${name}) ${params} : ${retType}`.trim(),
      });
    }
  }
  return decls;
}

function extractModuleBlock(node: ts.ModuleDeclaration): StubDecl[] {
  const body = node.body;
  if (!body) return [];
  if (ts.isModuleBlock(body)) {
    const decls: StubDecl[] = [];
    for (const stmt of body.statements) {
      const d = extractStmt(stmt);
      if (d) decls.push(...(Array.isArray(d) ? d : [d]));
    }
    return decls;
  }
  if (ts.isModuleDeclaration(body)) {
    return extractModuleBlock(body);
  }
  return [];
}

// ─── Type node → Lean type string ───────────────────────────────────────────────

function typeNodeToLean(node: ts.TypeNode): string {
  if (ts.isTypeReferenceNode(node)) {
    const name = node.typeName.getText();
    const args = node.typeArguments?.map(a => typeNodeToLean(a)) ?? [];
    const mapped = mapKnownType(name);
    return args.length > 0 ? `${mapped} ${args.map(a => `(${a})`).join(' ')}` : mapped;
  }
  if (node.kind === ts.SyntaxKind.StringKeyword) return 'String';
  if (node.kind === ts.SyntaxKind.NumberKeyword) return 'Float';
  if (node.kind === ts.SyntaxKind.BooleanKeyword) return 'Bool';
  if (node.kind === ts.SyntaxKind.VoidKeyword) return 'Unit';
  if (node.kind === ts.SyntaxKind.AnyKeyword) return 'String';
  if (node.kind === ts.SyntaxKind.NeverKeyword) return 'Empty';
  if (node.kind === ts.SyntaxKind.UndefinedKeyword) return 'Unit';
  if (node.kind === ts.SyntaxKind.NullKeyword) return 'Unit';
  if (ts.isArrayTypeNode(node)) return `Array (${typeNodeToLean(node.elementType)})`;
  if (ts.isTupleTypeNode(node)) {
    const elems = node.elements.map(e => typeNodeToLean(e as ts.TypeNode));
    return elems.length === 0 ? 'Unit' : elems.join(' × ');
  }
  if (ts.isUnionTypeNode(node)) {
    const types = node.types.filter(t => t.kind !== ts.SyntaxKind.UndefinedKeyword && t.kind !== ts.SyntaxKind.NullKeyword);
    if (types.length === 0) return 'Unit';
    if (types.length < node.types.length) return `Option (${typeNodeToLean(types[0])})`;
    return typeNodeToLean(types[0]);
  }
  if (ts.isFunctionTypeNode(node)) {
    const params = node.parameters.map(p => p.type ? typeNodeToLean(p.type) : 'String');
    const ret = typeNodeToLean(node.type);
    return params.length === 0 ? `Unit → ${ret}` : `${params.join(' → ')} → ${ret}`;
  }
  if (ts.isTypeLiteralNode(node)) return 'String'; // object literal types → String
  if (ts.isLiteralTypeNode(node)) return 'String'; // literal types → String
  if (ts.isParenthesizedTypeNode(node)) return typeNodeToLean(node.type);
  if (ts.isTypeParameterDeclaration(node as any)) return (node as any).name?.text ?? 'α';
  return 'String'; // fallback
}

function mapKnownType(name: string): string {
  const map: Record<string, string> = {
    'Promise': 'IO', 'Buffer': 'Array UInt8', 'Uint8Array': 'Array UInt8',
    'Map': 'AssocMap', 'Set': 'Array', 'Date': 'Nat', 'Error': 'String',
    'RegExp': 'String', 'URL': 'String', 'ReadableStream': 'IO String',
    'WritableStream': 'IO Unit', 'Record': 'AssocMap String',
  };
  return map[name] ?? name;
}

// ─── Lean stub generation ───────────────────────────────────────────────────────

/** Generate a complete Lean stub module from extracted declarations. */
export function generateLeanStub(mod: StubModule): string {
  const lines: string[] = [
    `-- ${mod.leanModule}`,
    `-- Auto-generated Lean stubs for npm package: ${mod.packageName}`,
    `-- These are axiomatized declarations for verification purposes.`,
    ``,
    `namespace ${mod.leanModule}`,
    ``,
  ];

  for (const d of mod.decls) {
    lines.push(...renderDecl(d, ''));
  }

  lines.push(``, `end ${mod.leanModule}`);
  return lines.join('\n');
}

function renderDecl(d: StubDecl, indent: string): string[] {
  const lines: string[] = [];
  if (d.doc) lines.push(`${indent}/-- ${d.doc} -/`);

  switch (d.kind) {
    case 'opaque-type': {
      const tps = d.typeParams?.map(t => `(${t} : Type)`).join(' ') ?? '';
      const sig = tps ? ` ${tps}` : '';
      lines.push(`${indent}opaque ${d.name}${sig} : Type`);
      lines.push(`${indent}instance : Inhabited ${d.name} := ⟨sorry⟩`);
      break;
    }
    case 'axiom-fn': {
      lines.push(`${indent}axiom ${d.name} : ${d.leanType ?? 'String'}`);
      break;
    }
    case 'const': {
      lines.push(`${indent}axiom ${d.name} : ${d.leanType ?? 'String'}`);
      break;
    }
    case 'class': {
      const tps = d.typeParams?.map(t => `(${t} : Type)`).join(' ') ?? '';
      lines.push(`${indent}opaque ${d.name}${tps ? ' ' + tps : ''} : Type`);
      lines.push(`${indent}instance : Inhabited ${d.name} := ⟨sorry⟩`);
      break;
    }
    case 'enum': {
      lines.push(`${indent}opaque ${d.name} : Type`);
      lines.push(`${indent}instance : Inhabited ${d.name} := ⟨sorry⟩`);
      break;
    }
    case 'namespace': {
      lines.push(`${indent}namespace ${d.name}`);
      if (d.members) {
        for (const m of d.members) lines.push(...renderDecl(m, indent + '  '));
      }
      lines.push(`${indent}end ${d.name}`);
      break;
    }
  }
  lines.push('');
  return lines;
}

// ─── Package discovery ──────────────────────────────────────────────────────────

/** Find .d.ts files for a package in node_modules. */
export function findDtsFiles(packageName: string, projectDir: string): string[] {
  const candidates = [
    path.join(projectDir, 'node_modules', packageName, 'index.d.ts'),
    path.join(projectDir, 'node_modules', '@types', packageName, 'index.d.ts'),
    path.join(projectDir, 'node_modules', '@types', packageName.replace('/', '__'), 'index.d.ts'),
  ];
  return candidates.filter(c => fs.existsSync(c));
}

/** Convert an npm package name to a Lean module name for stubs. */
export function packageToLeanModule(packageName: string): string {
  const clean = packageName
    .replace(/^node:/, 'Node')
    .replace(/^@/, '')
    .replace(/[^a-zA-Z0-9/]/g, ' ');
  const parts = clean.split(/[\s/]+/).filter(Boolean).map(p => capitalize(p));
  return `TSLean.Stubs.${parts.join('.')}`;
}

// ─── Cache management ───────────────────────────────────────────────────────────

const CACHE_DIR = '.tslean-cache/stubs';

/** Write a generated stub to the cache directory. */
export function cacheStub(projectDir: string, mod: StubModule, content: string): void {
  const cacheDir = path.join(projectDir, CACHE_DIR);
  const filePath = path.join(cacheDir, mod.leanModule.replace(/\./g, '/') + '.lean');
  fs.mkdirSync(path.dirname(filePath), { recursive: true });
  fs.writeFileSync(filePath, content, 'utf-8');
}

/** Read a cached stub if it exists. */
export function readCachedStub(projectDir: string, leanModule: string): string | null {
  const filePath = path.join(projectDir, CACHE_DIR, leanModule.replace(/\./g, '/') + '.lean');
  return fs.existsSync(filePath) ? fs.readFileSync(filePath, 'utf-8') : null;
}

/** Generate stubs for a package: extract .d.ts → Lean, cache result. */
export function generatePackageStubs(packageName: string, projectDir: string): StubModule | null {
  const dtsFiles = findDtsFiles(packageName, projectDir);
  if (dtsFiles.length === 0) return null;

  const leanModule = packageToLeanModule(packageName);
  const decls: StubDecl[] = [];
  for (const f of dtsFiles) {
    decls.push(...extractDtsStubs(f));
  }
  if (decls.length === 0) return null;

  const mod: StubModule = { packageName, leanModule, decls };
  const content = generateLeanStub(mod);
  cacheStub(projectDir, mod, content);
  return mod;
}
