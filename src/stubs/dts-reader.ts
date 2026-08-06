// .d.ts reader: extract type declarations from TypeScript definition files
// and generate Lean stub modules (opaque types + axiomatized functions).

import * as ts from 'typescript';
import * as fs from 'fs';
import * as path from 'path';
import { capitalize, escapeLeanComment } from '../utils.js';

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
  try {
    fs.readFileSync(dtsPath, 'utf-8');
  } catch {
    throw new Error(`Unable to read .d.ts entry "${dtsPath}". Check that the file exists and is readable.`);
  }

  const entryPath = path.resolve(dtsPath);
  const program = ts.createProgram([entryPath], {
    module: ts.ModuleKind.ESNext,
    moduleResolution: ts.ModuleResolutionKind.Bundler,
    noEmit: true,
    skipLibCheck: true,
    target: ts.ScriptTarget.ES2022,
  });
  const sourceFile = program.getSourceFile(entryPath);
  if (!sourceFile) {
    throw new Error(`Unable to read .d.ts entry "${dtsPath}". Check that the file exists and is readable.`);
  }

  const checker = program.getTypeChecker();
  const entrySymbol = checker.getSymbolAtLocation(sourceFile);
  if (entrySymbol) return extractModuleExports(entrySymbol, checker);

  const decls: StubDecl[] = [];
  for (const statement of sourceFile.statements) {
    if (!ts.isModuleDeclaration(statement)) continue;
    const symbol = checker.getSymbolAtLocation(statement.name);
    if (!symbol) continue;
    const members = extractModuleExports(symbol, checker);
    if (members.length === 0) continue;
    decls.push({
      kind: 'namespace',
      name: statement.name.text,
      members,
      doc: getDoc(symbol, checker),
    });
  }
  return decls;
}

function extractModuleExports(symbol: ts.Symbol, checker: ts.TypeChecker): StubDecl[] {
  const decls: StubDecl[] = [];
  for (const exportedSymbol of checker.getExportsOfModule(symbol)) {
    const decl = extractExportedSymbol(exportedSymbol, checker);
    if (decl) decls.push(...(Array.isArray(decl) ? decl : [decl]));
  }
  return decls;
}

function extractExportedSymbol(exportedSymbol: ts.Symbol, checker: ts.TypeChecker): StubDecl | StubDecl[] | null {
  const symbol = exportedSymbol.flags & ts.SymbolFlags.Alias
    ? checker.getAliasedSymbol(exportedSymbol)
    : exportedSymbol;
  const declaration = firstSupportedDeclaration(symbol);
  if (!declaration) return null;

  const exportedName = exportedSymbol.name === 'default'
    ? declarationName(declaration)
    : exportedSymbol.name;
  if (!exportedName) return null;
  const doc = getDoc(symbol, checker);

  if (ts.isFunctionDeclaration(declaration)) {
    return extractFunctionDecl(declaration, exportedName, doc);
  }
  if (ts.isInterfaceDeclaration(declaration) || ts.isTypeAliasDeclaration(declaration)) {
    return {
      kind: 'opaque-type',
      name: exportedName,
      typeParams: extractTypeParamNames(declaration.typeParameters, exportedName),
      doc,
    };
  }
  if (ts.isClassDeclaration(declaration)) {
    return extractClassDecl(declaration, exportedName, checker, doc);
  }
  if (ts.isEnumDeclaration(declaration)) {
    return { kind: 'enum', name: exportedName, doc };
  }
  if (ts.isVariableDeclaration(declaration)) {
    return {
      kind: 'const',
      name: exportedName,
      leanType: declaration.type ? typeNodeToLean(declaration.type) : 'String',
      doc,
    };
  }
  if (ts.isModuleDeclaration(declaration)) {
    const members = extractModuleExports(symbol, checker);
    return members.length > 0
      ? { kind: 'namespace', name: exportedName, members, doc }
      : null;
  }
  return null;
}

function firstSupportedDeclaration(symbol: ts.Symbol): ts.Declaration | undefined {
  for (const declaration of symbol.declarations ?? []) {
    if (ts.isFunctionDeclaration(declaration) ||
        ts.isInterfaceDeclaration(declaration) ||
        ts.isTypeAliasDeclaration(declaration) ||
        ts.isClassDeclaration(declaration) ||
        ts.isEnumDeclaration(declaration) ||
        ts.isVariableDeclaration(declaration) ||
        ts.isModuleDeclaration(declaration)) {
      return declaration;
    }
  }
  return undefined;
}

function declarationName(declaration: ts.Declaration): string | undefined {
  if (ts.isFunctionDeclaration(declaration) || ts.isClassDeclaration(declaration)) {
    return declaration.name?.text;
  }
  if (ts.isInterfaceDeclaration(declaration) ||
      ts.isTypeAliasDeclaration(declaration) ||
      ts.isEnumDeclaration(declaration) ||
      ts.isModuleDeclaration(declaration)) {
    return declaration.name.text;
  }
  if (ts.isVariableDeclaration(declaration) && ts.isIdentifier(declaration.name)) {
    return declaration.name.text;
  }
  return undefined;
}

function getDoc(symbol: ts.Symbol, checker: ts.TypeChecker): string | undefined {
  const doc = ts.displayPartsToString(symbol.getDocumentationComment(checker)).trim();
  return doc || undefined;
}

function extractTypeParamNames(
  typeParams: ts.NodeArray<ts.TypeParameterDeclaration> | undefined,
  owner: string,
): string[] | undefined {
  return typeParams?.map(typeParam => {
    if (typeParam.constraint) {
      throw new Error(
        `Unsupported generic constraint on "${owner}.${typeParam.name.text}": ${typeParam.constraint.getText()}`,
      );
    }
    return typeParam.name.text;
  });
}

function extractFunctionDecl(node: ts.FunctionDeclaration, name: string, doc?: string): StubDecl {
  const params = node.parameters.map(p => {
    const pName = ts.isIdentifier(p.name) ? p.name.text : '_';
    const pType = p.type ? typeNodeToLean(p.type) : 'String';
    return `(${pName} : ${pType})`;
  }).join(' ');
  const retType = node.type ? typeNodeToLean(node.type) : 'String';
  const typeParams = extractTypeParamNames(node.typeParameters, name);
  const tpStr = renderImplicitTypeParams(typeParams);
  return {
    kind: 'axiom-fn',
    name,
    leanType: `${tpStr} ${params} : ${retType}`.trim(),
    typeParams,
    doc,
  };
}

function extractClassDecl(
  node: ts.ClassDeclaration,
  name: string,
  checker: ts.TypeChecker,
  doc?: string,
): StubDecl[] {
  const typeParams = extractTypeParamNames(node.typeParameters, name);
  const decls: StubDecl[] = [{
    kind: 'opaque-type',
    name,
    typeParams,
    doc,
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
      const methodTypeParams = extractTypeParamNames(member.typeParameters, `${name}.${mName}`);
      const binders = [
        renderImplicitTypeParams(typeParams),
        renderImplicitTypeParams(methodTypeParams),
        `(self : ${applyTypeParams(name, typeParams)})`,
        params,
      ].filter(Boolean).join(' ');
      const symbol = checker.getSymbolAtLocation(member.name);
      decls.push({
        kind: 'axiom-fn',
        name: `${name}.${mName}`,
        leanType: `${binders} : ${retType}`,
        doc: symbol ? getDoc(symbol, checker) : undefined,
      });
    }
  }
  return decls;
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
    const elems = node.elements.map(e => typeNodeToLean(e));
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

function renderExplicitTypeParams(typeParams: string[] | undefined): string {
  return typeParams?.map(typeParam => `(${typeParam} : Type)`).join(' ') ?? '';
}

function renderImplicitTypeParams(typeParams: string[] | undefined): string {
  return typeParams?.map(typeParam => `{${typeParam} : Type}`).join(' ') ?? '';
}

function applyTypeParams(name: string, typeParams: string[] | undefined): string {
  return typeParams?.length ? `${name} ${typeParams.join(' ')}` : name;
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
  if (d.doc) lines.push(`${indent}/-- ${escapeLeanComment(d.doc)} -/`);

  switch (d.kind) {
    case 'opaque-type':
    case 'class': {
      const tps = renderExplicitTypeParams(d.typeParams);
      const sig = tps ? ` ${tps}` : '';
      lines.push(`${indent}opaque ${d.name}${sig} : Type`);
      const instanceParams = renderImplicitTypeParams(d.typeParams);
      const target = d.typeParams?.length ? `(${applyTypeParams(d.name, d.typeParams)})` : d.name;
      lines.push(`${indent}instance${instanceParams ? ` ${instanceParams}` : ''} : Inhabited ${target} := ⟨sorry⟩`);
      break;
    }
    case 'axiom-fn': {
      lines.push(`${indent}axiom ${d.name} ${d.leanType ?? ': String'}`);
      break;
    }
    case 'const': {
      lines.push(`${indent}axiom ${d.name} : ${d.leanType ?? 'String'}`);
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
