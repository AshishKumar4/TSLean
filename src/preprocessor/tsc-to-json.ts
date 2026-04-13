#!/usr/bin/env npx tsx
/**
 * tsc-to-json.ts — Serialize a TypeScript AST + type info to JSON.
 *
 * This is the "Stage 0" preprocessor for the runnable self-host.
 * It runs the TS compiler to parse and type-check, then serializes the
 * AST and resolved types into a JSON format that the Lean transpiler
 * can read without any TS compiler dependency.
 *
 * Usage: npx tsx src/preprocessor/tsc-to-json.ts <input.ts> [output.json]
 *
 * JSON Schema:
 *   { fileName, sourceText, statements: JsonNode[] }
 * where JsonNode has kind, text, flags, resolvedType, and role-specific children.
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

  // Comment info
  leadingComments?: string[];
}

interface JsonAST {
  fileName: string;
  sourceText: string;
  statements: JsonNode[];
}

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

function serializeType(checker: ts.TypeChecker, type: ts.Type, depth = 0): JsonType | undefined {
  if (!type || depth > 10) return undefined;
  const result: JsonType = { flags: type.flags };

  if (type.symbol?.name) result.symbol = type.symbol.name;
  if (type.aliasSymbol?.name) result.aliasName = type.aliasSymbol.name;

  if ('objectFlags' in type) result.objectFlags = (type as ts.ObjectType).objectFlags;
  if ('value' in type && typeof (type as any).value === 'string') result.value = (type as any).value;

  if (type.isUnion()) {
    result.types = type.types.map(t => serializeType(checker, t, depth + 1)).filter(Boolean) as JsonType[];
  }
  if (type.isIntersection()) {
    result.types = type.types.map(t => serializeType(checker, t, depth + 1)).filter(Boolean) as JsonType[];
  }
  if ('typeArguments' in type && (type as ts.TypeReference).typeArguments) {
    result.typeArguments = (type as ts.TypeReference).typeArguments!
      .map(t => serializeType(checker, t, depth + 1))
      .filter(Boolean) as JsonType[];
  }
  // For type names, use checker.typeToString as a fallback
  if (!result.symbol && !result.value) {
    try { result.name = checker.typeToString(type); } catch {}
  }

  return result;
}

function isNode(v: any): v is ts.Node {
  return v && typeof v === 'object' && typeof v.kind === 'number';
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
  if (node.flags) result.flags = node.flags;
  result.pos = node.pos;
  result.end = node.end;

  // Resolve type via checker (for expression and declaration nodes)
  try {
    const type = checker.getTypeAtLocation(node);
    if (type) result.resolvedType = serializeType(checker, type, 0);
  } catch {}

  // Role-specific children
  const n = node as any;

  // Name
  if (n.name && isNode(n.name)) result.name = serializeNode(n.name, checker, sf, depth + 1);

  // Expression
  if (n.expression && isNode(n.expression)) result.expression = serializeNode(n.expression, checker, sf, depth + 1);

  // Body
  if (n.body && isNode(n.body)) result.body = serializeNode(n.body, checker, sf, depth + 1);

  // Statements
  if (n.statements) result.statements = serializeArray(n.statements, checker, sf, depth);

  // Parameters
  if (n.parameters) result.parameters = serializeArray(n.parameters, checker, sf, depth);

  // Type parameters
  if (n.typeParameters) result.typeParameters = serializeArray(n.typeParameters, checker, sf, depth);

  // Type annotation
  if (n.type && isNode(n.type)) result.type = serializeNode(n.type, checker, sf, depth + 1);

  // Initializer
  if (n.initializer && isNode(n.initializer)) result.initializer = serializeNode(n.initializer, checker, sf, depth + 1);

  // Members
  if (n.members) result.members = serializeArray(n.members, checker, sf, depth);

  // Heritage clauses
  if (n.heritageClauses) result.heritageClauses = serializeArray(n.heritageClauses, checker, sf, depth);

  // Modifiers
  if (n.modifiers) result.modifiers = serializeArray(n.modifiers, checker, sf, depth);

  // Variable declarations
  if (n.declarationList && isNode(n.declarationList))
    result.declarationList = serializeNode(n.declarationList, checker, sf, depth + 1);
  if (n.declarations) result.declarations = serializeArray(n.declarations, checker, sf, depth);

  // Control flow
  if (n.thenStatement && isNode(n.thenStatement)) result.thenStatement = serializeNode(n.thenStatement, checker, sf, depth + 1);
  if (n.elseStatement && isNode(n.elseStatement)) result.elseStatement = serializeNode(n.elseStatement, checker, sf, depth + 1);
  if (n.condition && isNode(n.condition)) result.condition = serializeNode(n.condition, checker, sf, depth + 1);
  if (n.incrementor && isNode(n.incrementor)) result.incrementor = serializeNode(n.incrementor, checker, sf, depth + 1);
  if (n.statement && isNode(n.statement)) result.statement = serializeNode(n.statement, checker, sf, depth + 1);
  if (n.caseBlock && isNode(n.caseBlock)) result.caseBlock = serializeNode(n.caseBlock, checker, sf, depth + 1);
  if (n.clauses) result.clauses = serializeArray(n.clauses, checker, sf, depth);
  if (n.tryBlock && isNode(n.tryBlock)) result.tryBlock = serializeNode(n.tryBlock, checker, sf, depth + 1);
  if (n.catchClause && isNode(n.catchClause)) result.catchClause = serializeNode(n.catchClause, checker, sf, depth + 1);
  if (n.block && isNode(n.block)) result.block = serializeNode(n.block, checker, sf, depth + 1);
  if (n.variableDeclaration && isNode(n.variableDeclaration))
    result.variableDeclaration = serializeNode(n.variableDeclaration, checker, sf, depth + 1);
  if (n.finallyBlock && isNode(n.finallyBlock)) result.finallyBlock = serializeNode(n.finallyBlock, checker, sf, depth + 1);

  // Expressions
  if (n.left && isNode(n.left)) result.left = serializeNode(n.left, checker, sf, depth + 1);
  if (n.right && isNode(n.right)) result.right = serializeNode(n.right, checker, sf, depth + 1);
  if (n.operatorToken && isNode(n.operatorToken)) result.operatorToken = serializeNode(n.operatorToken, checker, sf, depth + 1);
  if (n.operand && isNode(n.operand)) result.operand = serializeNode(n.operand, checker, sf, depth + 1);
  if (typeof n.operator === 'number') result.operator = n.operator;
  if (n.arguments) result.arguments = serializeArray(n.arguments, checker, sf, depth);
  if (n.typeArguments) result.typeArguments = serializeArray(n.typeArguments, checker, sf, depth);
  if (n.argumentExpression && isNode(n.argumentExpression))
    result.argumentExpression = serializeNode(n.argumentExpression, checker, sf, depth + 1);
  if (n.questionDotToken) result.questionDotToken = { kind: 'QuestionDotToken' };
  if (n.whenTrue && isNode(n.whenTrue)) result.whenTrue = serializeNode(n.whenTrue, checker, sf, depth + 1);
  if (n.whenFalse && isNode(n.whenFalse)) result.whenFalse = serializeNode(n.whenFalse, checker, sf, depth + 1);

  // Literals / templates
  if (n.elements) result.elements = serializeArray(n.elements, checker, sf, depth);
  if (n.properties) result.properties = serializeArray(n.properties, checker, sf, depth);
  if (n.head && isNode(n.head)) result.head = serializeNode(n.head, checker, sf, depth + 1);
  if (n.templateSpans) result.templateSpans = serializeArray(n.templateSpans, checker, sf, depth);
  if (n.literal && isNode(n.literal)) result.literal = serializeNode(n.literal, checker, sf, depth + 1);
  if (n.template && isNode(n.template)) result.template = serializeNode(n.template, checker, sf, depth + 1);

  // Imports / exports
  if (n.moduleSpecifier && isNode(n.moduleSpecifier))
    result.moduleSpecifier = serializeNode(n.moduleSpecifier, checker, sf, depth + 1);
  if (n.importClause && isNode(n.importClause))
    result.importClause = serializeNode(n.importClause, checker, sf, depth + 1);
  if (n.namedBindings && isNode(n.namedBindings))
    result.namedBindings = serializeNode(n.namedBindings, checker, sf, depth + 1);
  if (n.isTypeOnly) result.isTypeOnly = true;
  if (n.isExportEquals) result.isExportEquals = true;

  // Parameters / bindings
  if (n.dotDotDotToken) result.dotDotDotToken = { kind: 'DotDotDotToken' };
  if (n.propertyName && isNode(n.propertyName))
    result.propertyName = serializeNode(n.propertyName, checker, sf, depth + 1);

  // Heritage clauses
  if (typeof n.token === 'number') result.token = n.token;
  if (n.types && Array.isArray(n.types) && n !== node)
    result.types = serializeArray(n.types, checker, sf, depth);
  else if (n.types && Array.isArray(n.types) && ts.isHeritageClause(node))
    result.types = serializeArray(n.types, checker, sf, depth);

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
    noResolve: true,
    lib: [],
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
    fileName: sf.fileName,
    sourceText,
    statements: Array.from(sf.statements).map(s => serializeNode(s, checker, sf, 0)),
  };

  const json = JSON.stringify(ast, null, 2);

  if (outputFile) {
    fs.writeFileSync(outputFile, json, 'utf-8');
    process.stderr.write(`✓ ${inputFile} → ${outputFile} (${json.length} bytes)\n`);
  } else {
    process.stdout.write(json);
  }
}

main();
