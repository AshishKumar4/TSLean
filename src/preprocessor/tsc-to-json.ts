#!/usr/bin/env npx tsx
/**
 * tsc-to-json.ts — Serialize a TypeScript AST + rich type info to JSON.
 *
 * v2.0: Full type resolution via ts.TypeChecker. Unlike v1 which used
 * `noResolve: true` (stripping all cross-module types), v2 resolves
 * imports and standard library types, providing accurate type data for:
 * - Function signatures (parameter types + return types)
 * - Resolved call signatures (overload resolution)
 * - Symbol metadata (enum/namespace/type-alias flags)
 * - Object type properties (for branded type / discriminated union detection)
 *
 * Usage: npx tsx src/preprocessor/tsc-to-json.ts <input.ts> [output.json]
 *
 * JSON Schema (v2):
 *   { version: 2, fileName, sourceText, statements: JsonNode[] }
 * where JsonNode has kind, text, flags, resolvedType, signature,
 * symbolFlags, callSignature, and role-specific children.
 */

import * as ts from 'typescript';
import * as fs from 'fs';
import * as path from 'path';

// ─── JSON types ─────────────────────────────────────────────────────────────────

interface JsonType {
  flags: number;
  name?: string;
  objectFlags?: number;
  types?: JsonType[];
  typeArguments?: JsonType[];
  value?: string;              // for literal types
  symbol?: string;             // symbol name
  aliasName?: string;          // alias symbol name
  // v2: structured type metadata
  properties?: Array<{ name: string; typeFlags: number; type?: JsonType }>;
  callSignatures?: Array<{ params: Array<{ name: string; type?: JsonType }>; returnType?: JsonType }>;
}

interface JsonSignature {
  parameters: Array<{ name: string; type?: JsonType; optional?: boolean; rest?: boolean }>;
  returnType?: JsonType;
}

interface JsonNode {
  kind: string;
  text?: string;
  flags?: number;
  pos?: number;
  end?: number;
  resolvedType?: JsonType;

  // Role-specific children — mirrors ts.Node field names exactly
  name?: JsonNode;
  expression?: JsonNode;
  body?: JsonNode;
  statements?: JsonNode[];
  parameters?: JsonNode[];
  typeParameters?: JsonNode[];
  type?: JsonNode;
  initializer?: JsonNode;
  members?: JsonNode[];
  heritageClauses?: JsonNode[];
  modifiers?: JsonNode[];
  decorators?: JsonNode[];

  // Variable declarations
  declarationList?: JsonNode;
  declarations?: JsonNode[];

  // Control flow
  thenStatement?: JsonNode;
  elseStatement?: JsonNode;
  condition?: JsonNode;
  incrementor?: JsonNode;
  statement?: JsonNode;         // for-of, for-in, while body
  caseBlock?: JsonNode;
  clauses?: JsonNode[];
  tryBlock?: JsonNode;
  catchClause?: JsonNode;
  block?: JsonNode;
  variableDeclaration?: JsonNode;
  finallyBlock?: JsonNode;

  // Expressions
  left?: JsonNode;
  right?: JsonNode;
  operatorToken?: JsonNode;
  operand?: JsonNode;
  operator?: number;
  arguments?: JsonNode[];
  typeArguments?: JsonNode[];
  argumentExpression?: JsonNode;
  questionDotToken?: JsonNode;
  questionToken?: boolean;
  whenTrue?: JsonNode;
  whenFalse?: JsonNode;

  // Literals / templates
  elements?: JsonNode[];
  properties?: JsonNode[];
  head?: JsonNode;
  templateSpans?: JsonNode[];
  literal?: JsonNode;
  template?: JsonNode;

  // Imports / exports
  moduleSpecifier?: JsonNode;
  importClause?: JsonNode;
  namedBindings?: JsonNode;
  isTypeOnly?: boolean;
  isExportEquals?: boolean;

  // Parameters / bindings
  dotDotDotToken?: JsonNode;
  propertyName?: JsonNode;

  // Heritage
  token?: number;
  types?: JsonNode[];

  // Type-specific children
  elementType?: JsonNode;
  typeName?: JsonNode;

  // Comment info
  leadingComments?: string[];

  // v2: rich type metadata
  symbolFlags?: number;          // from checker.getSymbolAtLocation().flags
  signature?: JsonSignature;     // from checker.getSignatureFromDeclaration()
  callSignature?: { returnType?: JsonType }; // from checker.getResolvedSignature()
  sourceText?: string;           // preserved source text (StringLiteral)
}

interface JsonAST {
  version: number;
  fileName: string;
  sourceText: string;
  statements: JsonNode[];
}

type SerializableProperty =
  | 'name' | 'expression' | 'body' | 'statements' | 'parameters'
  | 'typeParameters' | 'type' | 'initializer' | 'members' | 'heritageClauses'
  | 'modifiers' | 'declarationList' | 'declarations' | 'thenStatement'
  | 'elseStatement' | 'condition' | 'incrementor' | 'statement' | 'caseBlock'
  | 'clauses' | 'tryBlock' | 'catchClause' | 'block' | 'variableDeclaration'
  | 'finallyBlock' | 'left' | 'right' | 'operatorToken' | 'operand' | 'operator'
  | 'arguments' | 'typeArguments' | 'argumentExpression' | 'questionDotToken'
  | 'questionToken' | 'whenTrue' | 'whenFalse' | 'elements' | 'properties'
  | 'head' | 'templateSpans' | 'literal' | 'template' | 'moduleSpecifier'
  | 'importClause' | 'namedBindings' | 'isTypeOnly' | 'isExportEquals'
  | 'dotDotDotToken' | 'propertyName' | 'token' | 'types' | 'elementType'
  | 'typeName';

type AstValue = ts.Node | AstValue[] | number | boolean | undefined;
type SerializableNode = ts.Node & Partial<Record<SerializableProperty, AstValue>>;

// ─── Serialization ──────────────────────────────────────────────────────────────

const MAX_DEPTH = 30;

/** Map SyntaxKind to a stable name. ts.SyntaxKind[k] returns aliases for some
 *  kinds (e.g. "FirstStatement" for VariableStatement), so we override those. */
const KIND_OVERRIDES: Record<number, string> = {
  [ts.SyntaxKind.VariableStatement]: 'VariableStatement',
  [ts.SyntaxKind.NumericLiteral]: 'NumericLiteral',
  [ts.SyntaxKind.BigIntLiteral]: 'BigIntLiteral',
  [ts.SyntaxKind.StringLiteral]: 'StringLiteral',
  [ts.SyntaxKind.RegularExpressionLiteral]: 'RegularExpressionLiteral',
  [ts.SyntaxKind.NoSubstitutionTemplateLiteral]: 'NoSubstitutionTemplateLiteral',
  [ts.SyntaxKind.TemplateHead]: 'TemplateHead',
  [ts.SyntaxKind.TemplateMiddle]: 'TemplateMiddle',
  [ts.SyntaxKind.TemplateTail]: 'TemplateTail',
  [ts.SyntaxKind.TrueKeyword]: 'TrueKeyword',
  [ts.SyntaxKind.FalseKeyword]: 'FalseKeyword',
  [ts.SyntaxKind.NullKeyword]: 'NullKeyword',
  [ts.SyntaxKind.ThisKeyword]: 'ThisKeyword',
  [ts.SyntaxKind.SuperKeyword]: 'SuperKeyword',
  [ts.SyntaxKind.ImportKeyword]: 'ImportKeyword',
  [ts.SyntaxKind.BreakStatement]: 'BreakStatement',
  [ts.SyntaxKind.ExpressionStatement]: 'ExpressionStatement',
  [ts.SyntaxKind.CaseClause]: 'CaseClause',
};

function syntaxKindName(kind: ts.SyntaxKind): string {
  return KIND_OVERRIDES[kind] ?? ts.SyntaxKind[kind] ?? `Unknown_${kind}`;
}

const MAX_TYPE_DEPTH = 4;
const MAX_PROPERTIES = 30;

function isObjectType(type: ts.Type): type is ts.ObjectType {
  return 'objectFlags' in type && typeof type.objectFlags === 'number';
}

function isTypeReference(type: ts.Type): type is ts.TypeReference {
  return isObjectType(type) && !!(type.objectFlags & ts.ObjectFlags.Reference);
}

function hasStringValue(type: ts.Type): type is ts.Type & { value: string } {
  return 'value' in type && typeof type.value === 'string';
}

function isType(value: object | null): value is ts.Type {
  return typeof value === 'object' && value !== null && 'flags' in value && typeof value.flags === 'number';
}

function getTypeArguments(type: ts.Type): ts.Type[] | undefined {
  if (!('typeArguments' in type) || !Array.isArray(type.typeArguments)) return undefined;
  return type.typeArguments.every(isType) ? type.typeArguments : undefined;
}

function serializeTypes(checker: ts.TypeChecker, types: readonly ts.Type[], depth: number): JsonType[] {
  return types.flatMap(type => {
    const serialized = serializeType(checker, type, depth);
    return serialized === undefined ? [] : [serialized];
  });
}

function serializeType(checker: ts.TypeChecker, type: ts.Type, depth = 0): JsonType | undefined {
  if (!type || depth > MAX_TYPE_DEPTH) return undefined;
  const result: JsonType = { flags: type.flags };

  if (type.symbol?.name) result.symbol = type.symbol.name;
  if (type.aliasSymbol?.name) result.aliasName = type.aliasSymbol.name;

  if (isObjectType(type)) result.objectFlags = type.objectFlags;
  if (hasStringValue(type)) result.value = type.value;

  if (type.isUnion()) {
    result.types = serializeTypes(checker, type.types, depth + 1);
  }
  if (type.isIntersection()) {
    result.types = serializeTypes(checker, type.types, depth + 1);
  }

  // Type arguments: prefer checker-resolved, fallback to AST-level
  if (isObjectType(type)) {
    const objFlags = type.objectFlags ?? 0;
    // Only for Reference types (Array<T>, Map<K,V>, etc.) — not all object types
    if (objFlags & ts.ObjectFlags.Reference && isTypeReference(type)) {
      try {
        const args = checker.getTypeArguments(type);
        if (args && args.length > 0) {
          result.typeArguments = serializeTypes(checker, args, depth + 1);
        }
      } catch { /* getTypeArguments may throw for non-reference types */ }
    }
  }
  const typeArguments = getTypeArguments(type);
  if (!result.typeArguments && typeArguments) {
    result.typeArguments = serializeTypes(checker, typeArguments, depth + 1);
  }

  // v2: Object type properties (only at depth 0 to avoid blowup)
  if (depth === 0 && (type.flags & ts.TypeFlags.Object) && !(type.flags & ts.TypeFlags.Any)) {
    try {
      const props = checker.getPropertiesOfType(type);
      if (props.length > 0 && props.length <= MAX_PROPERTIES) {
        result.properties = props.map(p => {
          const pt = checker.getTypeOfSymbol(p);
          return { name: p.name, typeFlags: pt.flags };
        });
      }
    } catch { /* getPropertiesOfType may fail on some synthetic types */ }
  }

  // v2: Call signatures (only at depth 0 — for callable object types / function types)
  if (depth === 0 && (type.flags & ts.TypeFlags.Object)) {
    try {
      const sigs = checker.getSignaturesOfType(type, ts.SignatureKind.Call);
      if (sigs.length > 0) {
        result.callSignatures = sigs.slice(0, 2).map(sig => ({
          params: sig.parameters.map(p => ({
            name: p.name,
            type: serializeType(checker, checker.getTypeOfSymbol(p), 2),
          })),
          returnType: serializeType(checker, checker.getReturnTypeOfSignature(sig), 2),
        }));
      }
    } catch { /* getSignaturesOfType may fail on non-object types */ }
  }

  // For type names, use checker.typeToString as a fallback
  if (!result.symbol && !result.value) {
    try { result.name = checker.typeToString(type); } catch (err) {
      console.warn(`[tsc-to-json] failed to stringify type: ${err instanceof Error ? err.message : err}`);
    }
  }

  return result;
}

function isNode(value: AstValue): value is ts.Node {
  return typeof value === 'object' && value !== null && 'kind' in value && typeof value.kind === 'number';
}

function hasSerializableProperty(node: ts.Node, property: SerializableProperty): node is SerializableNode {
  return property in node;
}

function getNodeProperty(node: ts.Node, property: SerializableProperty): ts.Node | undefined {
  if (!hasSerializableProperty(node, property)) return undefined;
  const value = node[property];
  return isNode(value) ? value : undefined;
}

function getNodeArrayProperty(node: ts.Node, property: SerializableProperty): ts.Node[] | undefined {
  if (!hasSerializableProperty(node, property)) return undefined;
  const value = node[property];
  return Array.isArray(value) && value.every(isNode) ? value : undefined;
}

function getNumberProperty(node: ts.Node, property: SerializableProperty): number | undefined {
  if (!hasSerializableProperty(node, property)) return undefined;
  const value = node[property];
  return typeof value === 'number' ? value : undefined;
}

function hasTruthyProperty(node: ts.Node, property: SerializableProperty): boolean {
  return hasSerializableProperty(node, property) && !!node[property];
}

function serializeChild(
  node: ts.Node,
  property: SerializableProperty,
  checker: ts.TypeChecker,
  sf: ts.SourceFile,
  depth: number
): JsonNode | undefined {
  const child = getNodeProperty(node, property);
  return child && serializeNode(child, checker, sf, depth + 1);
}

function serializeChildren(
  node: ts.Node,
  property: SerializableProperty,
  checker: ts.TypeChecker,
  sf: ts.SourceFile,
  depth: number
): JsonNode[] | undefined {
  const children = getNodeArrayProperty(node, property);
  return children && serializeArray(children, checker, sf, depth);
}

function serializeNode(
  node: ts.Node,
  checker: ts.TypeChecker,
  sf: ts.SourceFile,
  depth = 0
): JsonNode {
  if (depth > MAX_DEPTH) return { kind: 'TooDeep' };

  const result: JsonNode = {
    kind: syntaxKindName(node.kind),
  };

  // Basic properties
  const text = getNodeText(node);
  if (text !== undefined) result.text = text;
  // For StringLiteral nodes, preserve source text with quotes for faithful sanitization
  if (ts.isStringLiteral(node)) {
    try { result.sourceText = node.getText(sf); } catch (err) {
      console.warn(`[tsc-to-json] failed to get source text: ${err instanceof Error ? err.message : err}`);
    }
  }
  if (node.flags) result.flags = node.flags;
  result.pos = node.pos;
  result.end = node.end;

  // Resolve type via checker (for expression and declaration nodes)
  // Skip type resolution for import/export clauses (type-only, no runtime type)
  if (!ts.isImportClause(node) && !ts.isImportSpecifier(node) && !ts.isExportSpecifier(node)) {
    try {
      const type = checker.getTypeAtLocation(node);
      if (type) result.resolvedType = serializeType(checker, type, 0);
    } catch (err) {
      console.warn(`[tsc-to-json] failed to resolve type at ${syntaxKindName(node.kind)}: ${err instanceof Error ? err.message : err}`);
    }
  }

  // v2: Symbol flags (enum detection, namespace detection)
  if (ts.isIdentifier(node) || ts.isPropertyAccessExpression(node)) {
    try {
      const sym = checker.getSymbolAtLocation(node);
      if (sym && sym.flags) result.symbolFlags = sym.flags;
    } catch { /* symbol resolution may fail for synthetic nodes */ }
  }

  // v2: Function signature (parameter types + return type from checker)
  if (ts.isFunctionDeclaration(node) || ts.isMethodDeclaration(node) ||
      ts.isArrowFunction(node) || ts.isFunctionExpression(node) ||
      ts.isGetAccessor(node) || ts.isConstructorDeclaration(node)) {
    try {
      const sig = checker.getSignatureFromDeclaration(node);
      if (sig) {
        result.signature = {
          parameters: sig.parameters.map(p => {
            const ptype = checker.getTypeOfSymbol(p);
            const decl = p.valueDeclaration;
            return {
              name: p.name,
              type: serializeType(checker, ptype, 0),
              optional: !!(p.flags & ts.SymbolFlags.Optional) || (decl && ts.isParameter(decl) && !!decl.questionToken) || undefined,
              rest: (decl && ts.isParameter(decl) && !!decl.dotDotDotToken) || undefined,
            };
          }),
          returnType: serializeType(checker, checker.getReturnTypeOfSignature(sig), 0),
        };
      }
    } catch { /* signature resolution may fail for abstract/overloaded */ }
  }

  // v2: Resolved call signature (overload resolution for call expressions)
  if (ts.isCallExpression(node) || ts.isNewExpression(node)) {
    try {
      const sig = checker.getResolvedSignature(node);
      if (sig) {
        const retType = checker.getReturnTypeOfSignature(sig);
        if (retType) {
          result.callSignature = {
            returnType: serializeType(checker, retType, 0),
          };
        }
      }
    } catch { /* resolved signature may fail for unresolved calls */ }
  }

  // Name
  result.name = serializeChild(node, 'name', checker, sf, depth);

  // Expression
  result.expression = serializeChild(node, 'expression', checker, sf, depth);

  // Body
  result.body = serializeChild(node, 'body', checker, sf, depth);

  // Statements
  result.statements = serializeChildren(node, 'statements', checker, sf, depth);

  // Parameters
  result.parameters = serializeChildren(node, 'parameters', checker, sf, depth);

  // Type parameters
  result.typeParameters = serializeChildren(node, 'typeParameters', checker, sf, depth);

  // Type annotation
  result.type = serializeChild(node, 'type', checker, sf, depth);

  // Initializer
  result.initializer = serializeChild(node, 'initializer', checker, sf, depth);

  // Members
  result.members = serializeChildren(node, 'members', checker, sf, depth);

  // Heritage clauses
  result.heritageClauses = serializeChildren(node, 'heritageClauses', checker, sf, depth);

  // Modifiers
  result.modifiers = serializeChildren(node, 'modifiers', checker, sf, depth);

  // Variable declarations
  result.declarationList = serializeChild(node, 'declarationList', checker, sf, depth);
  result.declarations = serializeChildren(node, 'declarations', checker, sf, depth);

  // Control flow
  result.thenStatement = serializeChild(node, 'thenStatement', checker, sf, depth);
  result.elseStatement = serializeChild(node, 'elseStatement', checker, sf, depth);
  result.condition = serializeChild(node, 'condition', checker, sf, depth);
  result.incrementor = serializeChild(node, 'incrementor', checker, sf, depth);
  result.statement = serializeChild(node, 'statement', checker, sf, depth);
  result.caseBlock = serializeChild(node, 'caseBlock', checker, sf, depth);
  result.clauses = serializeChildren(node, 'clauses', checker, sf, depth);
  result.tryBlock = serializeChild(node, 'tryBlock', checker, sf, depth);
  result.catchClause = serializeChild(node, 'catchClause', checker, sf, depth);
  result.block = serializeChild(node, 'block', checker, sf, depth);
  result.variableDeclaration = serializeChild(node, 'variableDeclaration', checker, sf, depth);
  result.finallyBlock = serializeChild(node, 'finallyBlock', checker, sf, depth);

  // Expressions
  result.left = serializeChild(node, 'left', checker, sf, depth);
  result.right = serializeChild(node, 'right', checker, sf, depth);
  result.operatorToken = serializeChild(node, 'operatorToken', checker, sf, depth);
  result.operand = serializeChild(node, 'operand', checker, sf, depth);
  result.operator = getNumberProperty(node, 'operator');
  result.arguments = serializeChildren(node, 'arguments', checker, sf, depth);
  result.typeArguments = serializeChildren(node, 'typeArguments', checker, sf, depth);
  result.argumentExpression = serializeChild(node, 'argumentExpression', checker, sf, depth);
  result.questionDotToken = hasTruthyProperty(node, 'questionDotToken') ? { kind: 'QuestionDotToken' } : undefined;
  result.questionToken = hasTruthyProperty(node, 'questionToken') ? true : undefined;
  result.whenTrue = serializeChild(node, 'whenTrue', checker, sf, depth);
  result.whenFalse = serializeChild(node, 'whenFalse', checker, sf, depth);

  // Literals / templates
  result.elements = serializeChildren(node, 'elements', checker, sf, depth);
  result.properties = serializeChildren(node, 'properties', checker, sf, depth);
  result.head = serializeChild(node, 'head', checker, sf, depth);
  result.templateSpans = serializeChildren(node, 'templateSpans', checker, sf, depth);
  result.literal = serializeChild(node, 'literal', checker, sf, depth);
  result.template = serializeChild(node, 'template', checker, sf, depth);

  // Imports / exports
  result.moduleSpecifier = serializeChild(node, 'moduleSpecifier', checker, sf, depth);
  result.importClause = serializeChild(node, 'importClause', checker, sf, depth);
  result.namedBindings = serializeChild(node, 'namedBindings', checker, sf, depth);
  result.isTypeOnly = hasTruthyProperty(node, 'isTypeOnly') ? true : undefined;
  result.isExportEquals = hasTruthyProperty(node, 'isExportEquals') ? true : undefined;

  // Parameters / bindings
  result.dotDotDotToken = hasTruthyProperty(node, 'dotDotDotToken') ? { kind: 'DotDotDotToken' } : undefined;
  result.propertyName = serializeChild(node, 'propertyName', checker, sf, depth);

  // Heritage clauses and union types
  result.token = getNumberProperty(node, 'token');
  result.types = serializeChildren(node, 'types', checker, sf, depth);

  // Type-specific children: ArrayType, TupleType, etc.
  result.elementType = serializeChild(node, 'elementType', checker, sf, depth);
  result.typeName = serializeChild(node, 'typeName', checker, sf, depth);

  // Leading comments
  const comments = getLeadingComments(node, sf);
  if (comments.length > 0) result.leadingComments = comments;

  return result;
}

function serializeArray(
  nodes: ts.NodeArray<ts.Node> | ts.Node[],
  checker: ts.TypeChecker,
  sf: ts.SourceFile,
  parentDepth: number
): JsonNode[] {
  return Array.from(nodes).map(n => serializeNode(n, checker, sf, parentDepth + 1));
}

function getNodeText(node: ts.Node): string | undefined {
  if (ts.isIdentifier(node)) return node.text;
  if (ts.isStringLiteral(node) || ts.isNoSubstitutionTemplateLiteral(node)) return node.text;
  if (ts.isNumericLiteral(node)) return node.text;
  if (ts.isRegularExpressionLiteral(node)) return node.text;
  if (ts.isTemplateHead(node) || ts.isTemplateMiddle(node) || ts.isTemplateTail(node)) return node.text;
  return undefined;
}

function getLeadingComments(node: ts.Node, sf: ts.SourceFile): string[] {
  const text = sf.getFullText();
  const ranges = ts.getLeadingCommentRanges(text, node.getFullStart());
  if (!ranges) return [];
  return ranges.map(r => text.slice(r.pos, r.end));
}

// ─── Main ───────────────────────────────────────────────────────────────────────

function main(): void {
  const [,, inputFile, outputFile] = process.argv;
  if (!inputFile) {
    process.stderr.write('Usage: npx tsx src/preprocessor/tsc-to-json.ts <input.ts> [output.json]\n');
    process.exit(1);
  }

  const fileName = path.resolve(inputFile);
  const sourceText = fs.readFileSync(fileName, 'utf-8');

  const compilerOpts: ts.CompilerOptions = {
    target: ts.ScriptTarget.ES2022,
    module: ts.ModuleKind.NodeNext,
    moduleResolution: ts.ModuleResolutionKind.NodeNext,
    strict: true,
    skipLibCheck: true,
  };

  const host = ts.createCompilerHost(compilerOpts);
  const program = ts.createProgram([fileName], compilerOpts, host);
  const checker = program.getTypeChecker();
  const sf = program.getSourceFile(fileName);
  if (!sf) {
    process.stderr.write(`Could not parse: ${fileName}\n`);
    process.exit(1);
  }

  const ast: JsonAST = {
    version: 2,
    fileName: sf.fileName,
    sourceText,
    statements: Array.from(sf.statements).map(s => serializeNode(s, checker, sf, 0)),
  };

  const json = JSON.stringify(ast);

  if (outputFile) {
    fs.writeFileSync(outputFile, json, 'utf-8');
    process.stderr.write(`✓ ${inputFile} → ${outputFile} (${json.length} bytes)\n`);
  } else {
    process.stdout.write(json);
  }
}

main();
