// Parser: TypeScript compiler API → IR.
// Uses ts.createProgram + TypeChecker for fully-resolved types.
// Key transformations:
//   early-return CPS  :  if (cond) return x; rest  →  if cond then x else rest
//   switch            →  match
//   this              →  self
//   DO ambient inject :  when DurableObjectState detected

import * as ts from 'typescript';
import * as path from 'path';
import {
  IRModule, IRDecl, IRExpr, IRType, IRParam, IRCase, IRPattern, DoStmt,
  IRImport, Effect, BinOp,
  Pure, IO, Async, stateEffect, exceptEffect, combineEffects,
  isPure, hasAsync,
  TyNat, TyFloat, TyString, TyBool, TyUnit, TyNever, TyOption, TyArray,
  TyTuple, TyFn, TyMap, TyRef, TyVar, TyPromise,
  litStr, litNat, litBool, litUnit, varExpr, holeExpr,
} from '../ir/types.js';
import { mapType, extractStructFields, extractTypeParams, detectDiscriminatedUnion } from '../typemap/index.js';
import { inferNodeEffect } from '../effects/index.js';
import { hasDOPattern, CF_AMBIENT, makeAmbientHost, DO_LEAN_IMPORTS } from '../do-model/ambient.js';

// ─── Public API ───────────────────────────────────────────────────────────────

export interface ParseOptions {
  fileName: string;
  sourceText?: string;
  extraFiles?: Map<string, string>;
}

export function parseFile(opts: ParseOptions): IRModule {
  const { fileName } = opts;
  const sourceText = opts.sourceText ?? ts.sys.readFile(fileName) ?? '';
  const virtual = new Map<string, string>(opts.extraFiles ?? []);
  virtual.set(fileName, sourceText);

  const needsDO = hasDOPattern(sourceText);
  const ambientFile = '/__cf_ambient.d.ts';
  if (needsDO) virtual.set(ambientFile, CF_AMBIENT);

  const compilerOpts: ts.CompilerOptions = {
    target: ts.ScriptTarget.ES2022,
    module: ts.ModuleKind.NodeNext,
    moduleResolution: ts.ModuleResolutionKind.NodeNext,
    strict: true,
    skipLibCheck: true,
    noResolve: false,
    lib: ['lib.es2022.d.ts'],
  };

  const baseHost = ts.createCompilerHost(compilerOpts);
  const host     = makeAmbientHost(baseHost, virtual);
  const roots    = needsDO ? [fileName, ambientFile] : [fileName];
  const program  = ts.createProgram(roots, compilerOpts, host);
  const checker  = program.getTypeChecker();
  const sf       = program.getSourceFile(fileName);
  if (!sf) throw new Error(`Cannot get source file: ${fileName}`);

  return new ParserCtx(checker, sf, needsDO).parseModule();
}

// ─── Parser context ────────────────────────────────────────────────────────────

class ParserCtx {
  private imports: IRImport[] = [];

  constructor(
    private readonly checker: ts.TypeChecker,
    private readonly sf: ts.SourceFile,
    private readonly needsDO: boolean,
  ) {}

  parseModule(): IRModule {
    const name = fileToModuleName(this.sf.fileName);
    const decls: IRDecl[] = [];

    for (const stmt of this.sf.statements) {
      if (ts.isImportDeclaration(stmt)) { this.collectImport(stmt); continue; }
      const d = this.parseStatement(stmt);
      if (d) (Array.isArray(d) ? decls.push(...d) : decls.push(d));
    }

    if (this.needsDO) {
      for (const m of DO_LEAN_IMPORTS) {
        if (!this.imports.some(i => i.module === m)) this.imports.push({ module: m });
      }
    }

    return { name, imports: this.imports, decls, comments: [], sourceFile: this.sf.fileName };
  }

  // ─── Imports ──────────────────────────────────────────────────────────────

  private collectImport(node: ts.ImportDeclaration): void {
    const spec = (node.moduleSpecifier as ts.StringLiteral).text;
    // Skip type-only imports (they have no runtime value)
    if (node.importClause?.isTypeOnly) return;
    const lean = this.tsModToLean(spec);
    const names: string[] = [];
    if (node.importClause?.name) names.push(node.importClause.name.text);
    if (node.importClause?.namedBindings) {
      if (ts.isNamedImports(node.importClause.namedBindings)) {
        for (const el of node.importClause.namedBindings.elements) {
          if (!el.isTypeOnly) names.push(el.name.text);
        }
      } else if (ts.isNamespaceImport(node.importClause.namedBindings)) {
        // import * as X from './mod' → just import the module
        names.push(node.importClause.namedBindings.name.text);
      }
    }
    this.imports.push(names.length ? { module: lean, names } : { module: lean });
  }

  private tsModToLean(spec: string): string {
    if (!spec.startsWith('.')) {
      const known: Record<string, string> = { zod: 'TSLean.Stdlib.Validation', uuid: 'TSLean.Stdlib.Uuid' };
      return known[spec] ?? `TSLean.External.${cap(spec.replace(/[^a-zA-Z0-9]/g, '_'))}`;
    }
    const parts = spec
      .replace(/^[./]+/, '').replace(/\.(ts|js)$/, '')
      .split('/').filter(Boolean)
      .map(p => p.split(/[-_]/).map(cap).join(''));
    return 'TSLean.Generated.' + parts.join('.');
  }

  // ─── Statements ───────────────────────────────────────────────────────────

  private parseStatement(stmt: ts.Statement): IRDecl | IRDecl[] | null {
    if (ts.isFunctionDeclaration(stmt))  return this.parseFnDecl(stmt);
    if (ts.isClassDeclaration(stmt))     return this.parseClassDecl(stmt);
    if (ts.isInterfaceDeclaration(stmt)) return this.parseInterface(stmt);
    if (ts.isTypeAliasDeclaration(stmt)) return this.parseTypeAlias(stmt);
    if (ts.isEnumDeclaration(stmt))      return this.parseEnum(stmt);
    if (ts.isVariableStatement(stmt))    return this.parseVarStmt(stmt);
    if (ts.isModuleDeclaration(stmt))    return this.parseNamespace(stmt);
    if (ts.isExportDeclaration(stmt))    return this.parseExportDecl(stmt);
    if (ts.isExportAssignment(stmt))     return this.parseExportAssignment(stmt);
    if (ts.isExpressionStatement(stmt)) {
      const e = this.parseExpr(stmt.expression);
      return { tag: 'VarDecl', name: '_main', type: TyUnit, value: e, mutable: false };
    }
    return null;
  }

  // Re-export: export { X } from './mod'  or  export * from './mod'
  private parseExportDecl(node: ts.ExportDeclaration): IRDecl[] | null {
    if (!node.moduleSpecifier) return null;
    const spec = (node.moduleSpecifier as ts.StringLiteral).text;
    const lean = this.tsModToLean(spec);
    this.imports.push({ module: lean });
    return null;
  }

  // export default { fetch: ... } or export default class/function
  private parseExportAssignment(node: ts.ExportAssignment): IRDecl[] | null {
    if (node.isExportEquals) {
      // module.exports = ...
      const e = this.parseExpr(node.expression);
      return [{ tag: 'VarDecl', name: '_exports', type: TyUnit, value: e, mutable: false }];
    }
    // export default expr
    const expr = node.expression;
    if (ts.isObjectLiteralExpression(expr)) {
      // export default { fetch: handler, ... } → parse each property as a top-level def
      const decls: IRDecl[] = [];
      for (const prop of expr.properties) {
        if (ts.isPropertyAssignment(prop)) {
          const name = ts.isIdentifier(prop.name) ? prop.name.text : prop.name.getText(this.sf);
          if (ts.isArrowFunction(prop.initializer) || ts.isFunctionExpression(prop.initializer)) {
            const fn = prop.initializer;
            const tps = extractTypeParams(fn as ts.ArrowFunction);
            const ps  = this.parseParams(fn.parameters);
            const sig = this.checker.getSignatureFromDeclaration(fn)!;
            const ret = sig ? mapType(this.checker.getReturnTypeOfSignature(sig), this.checker) : TyUnit;
            const eff = inferNodeEffect(fn, this.checker);
            const body = ts.isBlock(fn.body as ts.Node)
              ? this.parseBlock(fn.body as ts.Block, eff)
              : this.parseExpr(fn.body as ts.Expression);
            decls.push({ tag: 'FuncDef', name, typeParams: tps, params: ps, retType: ret, effect: eff, body });
          } else {
            const ty  = mapType(this.checker.getTypeAtLocation(prop.initializer), this.checker);
            const val = this.parseExpr(prop.initializer);
            decls.push({ tag: 'VarDecl', name, type: ty, value: val, mutable: false });
          }
        } else if (ts.isMethodDeclaration(prop)) {
          // async fetch(...) { ... } in an object literal
          const name = ts.isIdentifier(prop.name) ? prop.name.text : prop.name.getText(this.sf);
          const tps  = extractTypeParams(prop);
          const ps   = this.parseParams(prop.parameters);
          const sig  = this.checker.getSignatureFromDeclaration(prop)!;
          const ret  = sig ? mapType(this.checker.getReturnTypeOfSignature(sig), this.checker) : TyUnit;
          const eff  = inferNodeEffect(prop, this.checker);
          const body = prop.body ? this.parseBlock(prop.body, eff) : holeExpr(ret);
          decls.push({ tag: 'FuncDef', name, typeParams: tps, params: ps, retType: ret, effect: eff, body });
        } else if (ts.isShorthandPropertyAssignment(prop)) {
          // { fetch } → already defined elsewhere, just reference
          const name = prop.name.text;
          const ty   = mapType(this.checker.getTypeAtLocation(prop.name), this.checker);
          decls.push({ tag: 'VarDecl', name: `_ref_${name}`, type: ty, value: varExpr(name, ty), mutable: false });
        }
      }
      return decls;
    }
    if (ts.isFunctionDeclaration(expr) || ts.isFunctionExpression(expr)) {
      return [this.parseFnDecl(expr as ts.FunctionDeclaration)];
    }
    if (ts.isClassDeclaration(expr)) {
      return this.parseClassDecl(expr as ts.ClassDeclaration);
    }
    const ty  = mapType(this.checker.getTypeAtLocation(expr), this.checker);
    const val = this.parseExpr(expr);
    return [{ tag: 'VarDecl', name: '_default', type: ty, value: val, mutable: false }];
  }

  // ─── Function declarations ─────────────────────────────────────────────────

  private parseFnDecl(node: ts.FunctionDeclaration): IRDecl {
    const name  = node.name?.text ?? 'anonymous';
    const tps   = extractTypeParams(node);
    const params = this.parseParams(node.parameters);
    const sig   = this.checker.getSignatureFromDeclaration(node)!;
    const ret   = sig ? mapType(this.checker.getReturnTypeOfSignature(sig), this.checker) : TyUnit;
    const eff   = inferNodeEffect(node, this.checker);
    const body  = node.body ? this.parseBlock(node.body, eff) : holeExpr(ret);
    const docComment = jsdocComment(node, this.sf);
    return { tag: 'FuncDef', name, typeParams: tps, params, retType: ret, effect: eff, body, comment: leadingComment(node, this.sf), docComment };
  }

  private parseParams(params: ts.NodeArray<ts.ParameterDeclaration>): IRParam[] {
    return params.map(p => {
      // Rest parameter: ...args → (args : Array T)
      if (p.dotDotDotToken && ts.isIdentifier(p.name)) {
        const sym = this.checker.getSymbolAtLocation(p.name);
        const elemTy = sym ? mapType(this.checker.getTypeOfSymbol(sym), this.checker) : TyRef('Any');
        const arrTy = elemTy.tag === 'Array' ? elemTy : TyArray(elemTy);
        return { name: p.name.text, type: arrTy, default_: undefined };
      }
      // Destructured parameter: { x, y } or [a, b] → opaque name _p
      if (!ts.isIdentifier(p.name)) {
        return { name: `_p${p.pos}`, type: TyRef('Any'), default_: undefined };
      }
      const name = p.name.text;
      const sym  = this.checker.getSymbolAtLocation(p.name);
      // Optional param (name?: T) gets Option type via TypeChecker
      const ty   = sym ? mapType(this.checker.getTypeOfSymbol(sym), this.checker) : TyRef('Any');
      return { name, type: ty, default_: p.initializer ? this.parseExpr(p.initializer) : undefined };
    });
  }

  // ─── Class declarations ────────────────────────────────────────────────────

  private parseClassDecl(node: ts.ClassDeclaration): IRDecl[] {
    const name  = node.name?.text ?? 'AnonClass';
    const isDO  = this.isDOClass(node);
    const decls: IRDecl[] = [];

    const stateFields = this.classStateFields(node);
    const stateType   = `${name}State`;
    if (stateFields.length > 0) {
      decls.push({
        tag: 'StructDef', name: stateType, typeParams: [],
        fields: stateFields, deriving: ['Repr', 'BEq'],
        comment: `State for ${name}`,
      });
    }

    // Collect parent class name for documentation
    const extendsClause = node.heritageClauses?.find(h => h.token === ts.SyntaxKind.ExtendsKeyword);
    const parentName = extendsClause?.types[0]?.expression.getText(this.sf);

    const methods: IRDecl[] = [];
    for (const m of node.members) {
      if (ts.isConstructorDeclaration(m)) {
        const d = this.parseCtor(m, name, stateType, isDO);
        if (d) methods.push(d);
      } else if (ts.isMethodDeclaration(m)) {
        const d = this.parseMethod(m, name, stateType, isDO);
        if (d) methods.push(d);
      } else if (ts.isGetAccessorDeclaration(m)) {
        const d = this.parseGetter(m, name, stateType);
        if (d) methods.push(d);
      } else if (ts.isSetAccessorDeclaration(m)) {
        const d = this.parseSetter(m, name, stateType);
        if (d) methods.push(d);
      }
    }
    if (isDO) decls.push({ tag: 'Namespace', name, decls: methods });
    else       decls.push(...methods);
    return decls;
  }

  // Getter: get field() { return this.field; }  →  def get_field (self : T) : RetType := self.field
  private parseGetter(node: ts.GetAccessorDeclaration, className: string, stateType: string): IRDecl | null {
    const fieldName = node.name?.getText(this.sf) ?? 'unknown';
    const sig  = this.checker.getSignatureFromDeclaration(node);
    const ret  = sig ? mapType(this.checker.getReturnTypeOfSignature(sig), this.checker) : TyUnit;
    const self: IRParam = { name: 'self', type: TyRef(className) };
    const body = node.body ? this.parseBlock(node.body, Pure) : { tag: 'FieldAccess' as const, obj: varExpr('self', TyRef(className)), field: fieldName, type: ret, effect: Pure };
    return { tag: 'FuncDef', name: `get_${fieldName}`, typeParams: [], params: [self], retType: ret, effect: Pure, body };
  }

  // Setter: set field(v) { this.field = v; }  →  def set_field (self : T) (v : FT) : T := { self with field := v }
  private parseSetter(node: ts.SetAccessorDeclaration, className: string, stateType: string): IRDecl | null {
    const fieldName = node.name?.getText(this.sf) ?? 'unknown';
    const params    = this.parseParams(node.parameters);
    const self: IRParam = { name: 'self', type: TyRef(className) };
    const valType = params[0]?.type ?? TyUnit;
    const valName = params[0]?.name ?? 'v';
    const retType = TyRef(className);
    // Emit `{ self with fieldName := v }` — Lean 4 record update syntax.
    // We use a StructLit that the codegen recognises as a "with-update" when it has
    // exactly one field and a `_base` field pointing to `self`.
    const body: IRExpr = {
      tag: 'StructLit',
      typeName: className,
      fields: [
        { name: '_base', value: varExpr('self', TyRef(className)) },
        { name: fieldName, value: varExpr(valName, valType) },
      ],
      type: retType, effect: Pure,
    };
    return { tag: 'FuncDef', name: `set_${fieldName}`, typeParams: [], params: [self, ...params], retType, effect: Pure, body };
  }

  private isDOClass(node: ts.ClassDeclaration): boolean {
    return (node.heritageClauses ?? []).some(h =>
      h.types.some(t => t.expression.getText(this.sf).includes('DurableObject'))
    ) || node.members.some(m =>
      ts.isConstructorDeclaration(m) &&
      m.parameters.some(p => p.type?.getText(this.sf).includes('DurableObjectState'))
    );
  }

  private classStateFields(node: ts.ClassDeclaration): Array<{ name: string; type: IRType; mutable?: boolean }> {
    const out: Array<{ name: string; type: IRType; mutable?: boolean }> = [];
    for (const m of node.members) {
      if (!ts.isPropertyDeclaration(m)) continue;
      if (m.modifiers?.some(mod => mod.kind === ts.SyntaxKind.StaticKeyword)) continue;
      const name    = m.name?.getText(this.sf) ?? '';
      if (!name || name.startsWith('#')) continue;
      const typeStr = m.type?.getText(this.sf) ?? '';
      if (typeStr.includes('DurableObjectState') || typeStr === 'Env') continue;
      const sym = m.name ? this.checker.getSymbolAtLocation(m.name) : undefined;
      const ty  = sym ? mapType(this.checker.getTypeOfSymbol(sym), this.checker) : TyRef('Any');
      out.push({ name, type: ty, mutable: true });
    }
    return out;
  }

  private parseCtor(node: ts.ConstructorDeclaration, className: string, stateType: string, isDO: boolean): IRDecl | null {
    const params = this.parseParams(node.parameters);
    const eff    = inferNodeEffect(node, this.checker);

    if (isDO) {
      // For DO classes the constructor initialises persistent state from non-DO params.
      // We synthesise a clean init that returns the state struct, filtering out
      // DurableObjectState/Env params (they go to the Lean runtime, not the app state).
      const stateFields = this.classStateFields(node.parent as ts.ClassDeclaration);
      const appParams   = params.filter(p => {
        const t = p.type;
        if (t.tag === 'TypeRef' && (t.name === 'DurableObjectState' || t.name === 'Env')) return false;
        return true;
      });
      // Build a struct literal initialising each state field to its default
      const fields = stateFields.map(f => ({
        name: f.name,
        value: appParams.find(p => p.name === f.name)
          ? varExpr(f.name, f.type)
          : holeExpr(f.type),
      }));
      const retType = TyRef(stateType);
      const body: IRExpr = fields.length > 0
        ? { tag: 'StructLit', typeName: stateType, fields, type: retType, effect: Pure }
        : { tag: 'StructLit', typeName: stateType, fields: [], type: retType, effect: Pure };
      return {
        tag: 'FuncDef', name: `${className}.init`, typeParams: [],
        params: appParams,
        retType, effect: Pure, body,
      };
    }

    const self: IRParam = { name: 'self', type: TyRef(className) };
    const body = node.body ? this.parseBlock(node.body, eff) : holeExpr(TyUnit);
    return {
      tag: 'FuncDef', name: `${className}.init`, typeParams: [],
      params: [self, ...params],
      retType: TyUnit, effect: eff, body,
    };
  }

  private parseMethod(node: ts.MethodDeclaration, className: string, stateType: string, isDO: boolean): IRDecl | null {
    const name    = node.name?.getText(this.sf) ?? 'unknown';
    const isStatic = node.modifiers?.some(m => m.kind === ts.SyntaxKind.StaticKeyword);
    const tps     = extractTypeParams(node);
    const sig     = this.checker.getSignatureFromDeclaration(node)!;
    const ret     = sig ? mapType(this.checker.getReturnTypeOfSignature(sig), this.checker) : TyUnit;
    const eff     = inferNodeEffect(node, this.checker);
    const params  = this.parseParams(node.parameters);
    const self: IRParam = { name: 'self', type: TyRef(isDO ? stateType : className) };
    const allParams = isStatic ? params : [self, ...params];
    const body = node.body ? this.parseBlock(node.body, eff) : holeExpr(ret);
    return { tag: 'FuncDef', name: isStatic ? `${className}.${name}` : name, typeParams: tps, params: allParams, retType: ret, effect: eff, body };
  }

  // ─── Interface ─────────────────────────────────────────────────────────────

  private parseInterface(node: ts.InterfaceDeclaration): IRDecl | IRDecl[] {
    const name       = node.name.text;
    const typeParams = extractTypeParams(node);
    const fields     = extractStructFields(node, this.checker);
    const comment    = leadingComment(node, this.sf);

    // Check for extends clause → generate a structure that includes parent fields
    const extendsNames: string[] = [];
    for (const h of node.heritageClauses ?? []) {
      for (const t of h.types) {
        extendsNames.push(t.expression.getText(this.sf));
      }
    }

    // Check for index signatures (e.g., [key: string]: T) → use AssocMap instead
    const hasIndex = node.members.some(m => ts.isIndexSignatureDeclaration(m));
    if (hasIndex && fields.length === 0) {
      // Pure index signature → type alias to AssocMap
      const indexSig = node.members.find(m => ts.isIndexSignatureDeclaration(m)) as ts.IndexSignatureDeclaration | undefined;
      const valType = indexSig?.type ? mapType(this.checker.getTypeAtLocation(indexSig.type), this.checker) : TyRef('Any');
      return { tag: 'TypeAlias', name, typeParams, body: TyMap(TyString, valType), comment };
    }

    const decls: IRDecl[] = [];
    const struct: IRDecl = {
      tag: 'StructDef', name, typeParams,
      fields: fields.map(f => ({ name: f.name, type: f.type, mutable: f.mutable })),
      deriving: ['Repr', 'BEq'],
      comment,
      extends_: extendsNames[0],  // First parent for documentation
    };
    decls.push(struct);
    return decls.length === 1 ? decls[0] : decls;
  }

  // ─── Type alias ────────────────────────────────────────────────────────────

  private parseTypeAlias(node: ts.TypeAliasDeclaration): IRDecl | IRDecl[] {
    const name = node.name.text;
    const tps  = extractTypeParams(node);
    const ty   = this.checker.getTypeAtLocation(node);

    if (ty.isUnion()) {
      const disc = detectDiscriminatedUnion(ty as ts.UnionType, this.checker);
      if (disc) {
        return {
          tag: 'InductiveDef', name, typeParams: tps,
          ctors: disc.variants.map(v => ({
            name: cap(v.literal),
            fields: v.fields.map(f => ({ name: f.name, type: f.type })),
          })),
          comment: leadingComment(node, this.sf),
        };
      }
      // String literal union → simple inductive
      const members = (ty as ts.UnionType).types;
      if (members.every(m => m.flags & ts.TypeFlags.StringLiteral)) {
        return {
          tag: 'InductiveDef', name, typeParams: tps,
          ctors: members.map(m => ({ name: cap((m as ts.StringLiteralType).value), fields: [] })),
          comment: leadingComment(node, this.sf),
        };
      }
    }

    // Branded type
    if (ty.isIntersection()) {
      const isBranded = ty.types.some(t =>
        (t.flags & ts.TypeFlags.Object) &&
        (t as ts.ObjectType).getProperties().some(p => p.name.startsWith('__brand') || p.name.startsWith('_brand'))
      );
      if (isBranded) {
        return {
          tag: 'StructDef', name, typeParams: tps,
          fields: [{ name: 'val', type: TyString }],
          deriving: ['Repr', 'BEq', 'DecidableEq'],
        };
      }
    }

    return { tag: 'TypeAlias', name, typeParams: tps, body: mapType(ty, this.checker), comment: leadingComment(node, this.sf) };
  }

  // ─── Enum ──────────────────────────────────────────────────────────────────

  private parseEnum(node: ts.EnumDeclaration): IRDecl | IRDecl[] {
    const enumName = node.name.text;
    const members  = node.members.map(m => ({
      name:  ts.isIdentifier(m.name) ? m.name.text : m.name.getText(this.sf),
      value: m.initializer ? m.initializer.getText(this.sf).replace(/['"]/g, '') : null,
    }));

    const isStringEnum = members.some(m => m.value !== null && isNaN(Number(m.value)));
    const inductive: IRDecl = {
      tag: 'InductiveDef', name: enumName, typeParams: [],
      ctors: members.map(m => ({ name: m.name, fields: [] })),
      comment: leadingComment(node, this.sf),
    };

    if (!isStringEnum) return inductive;

    // String enum: also emit a toString function
    const toStringCases: IRCase[] = members.map(m => ({
      pattern: { tag: 'PCtor', ctor: `${enumName}.${m.name}`, args: [] } as IRPattern,
      body: litStr(m.value ?? m.name),
    }));
    const toStringFn: IRDecl = {
      tag: 'FuncDef', name: `${enumName}.toString`, typeParams: [],
      params: [{ name: 'e', type: TyRef(enumName) }],
      retType: TyString, effect: Pure,
      body: { tag: 'Match', scrutinee: varExpr('e', TyRef(enumName)), cases: toStringCases, type: TyString, effect: Pure },
    };
    return [inductive, toStringFn];
  }

  // ─── Variable statement ────────────────────────────────────────────────────

  private parseVarStmt(node: ts.VariableStatement): IRDecl[] {
    const isConst = !!(node.declarationList.flags & ts.NodeFlags.Const);
    const out: IRDecl[] = [];
    for (const d of node.declarationList.declarations) {
      if (!ts.isIdentifier(d.name)) continue;
      const name = d.name.text;
      const ty   = mapType(this.checker.getTypeAtLocation(d), this.checker);
      if (d.initializer && (ts.isArrowFunction(d.initializer) || ts.isFunctionExpression(d.initializer))) {
        const fn = d.initializer;
        const tps = extractTypeParams(fn as ts.ArrowFunction);
        const ps  = this.parseParams(fn.parameters);
        const sig = this.checker.getSignatureFromDeclaration(fn)!;
        const ret = sig ? mapType(this.checker.getReturnTypeOfSignature(sig), this.checker) : TyUnit;
        const eff = inferNodeEffect(fn, this.checker);
        const body = ts.isBlock(fn.body as ts.Node)
          ? this.parseBlock(fn.body as ts.Block, eff)
          : this.parseExpr(fn.body as ts.Expression);
        out.push({ tag: 'FuncDef', name, typeParams: tps, params: ps, retType: ret, effect: eff, body });
      } else {
        const val = d.initializer ? this.parseExpr(d.initializer) : holeExpr(ty);
        out.push({ tag: 'VarDecl', name, type: ty, value: val, mutable: !isConst });
      }
    }
    return out;
  }

  // ─── Namespace ─────────────────────────────────────────────────────────────

  private parseNamespace(node: ts.ModuleDeclaration): IRDecl {
    const inner: IRDecl[] = [];
    if (node.body && ts.isModuleBlock(node.body)) {
      for (const s of node.body.statements) {
        const d = this.parseStatement(s);
        if (d) (Array.isArray(d) ? inner.push(...d) : inner.push(d));
      }
    }
    return { tag: 'Namespace', name: node.name.text, decls: inner };
  }

  // ─── Block → expression (CPS early-return) ────────────────────────────────

  parseBlock(block: ts.Block, eff: Effect): IRExpr {
    return this.parseStmts(block.statements, eff);
  }

  private parseStmts(stmts: ReadonlyArray<ts.Statement>, eff: Effect): IRExpr {
    if (stmts.length === 0) return litUnit();
    const [head, ...rest] = stmts;
    return this.parseStmt(head, rest, eff);
  }

  private parseStmt(stmt: ts.Statement, rest: ReadonlyArray<ts.Statement>, eff: Effect): IRExpr {
    const cont = () => rest.length > 0 ? this.parseStmts(rest, eff) : litUnit();

    // return
    if (ts.isReturnStatement(stmt)) {
      const v = stmt.expression ? this.parseExpr(stmt.expression) : litUnit();
      return { tag: 'Return', value: v, type: v.type, effect: v.effect };
    }

    // variable declaration (first declarator only in stmt context)
     if (ts.isVariableStatement(stmt)) {
       const decl = stmt.declarationList.declarations[0];
       if (decl && ts.isIdentifier(decl.name)) {
         const name = decl.name.text;
         const ty   = mapType(this.checker.getTypeAtLocation(decl), this.checker);
         const val  = decl.initializer ? this.parseExpr(decl.initializer) : holeExpr(ty);
         const body = cont();
         const combined = combineEffects([val.effect, body.effect]);
         if (!isPure(val.effect) && hasAsync(eff)) {
           return { tag: 'Bind', name, monad: val, body, type: body.type, effect: combined };
         }
         return { tag: 'Let', name, annot: ty, value: val, body, type: body.type, effect: combined };
       }
       // Destructuring: const { x, y } = obj  →  let x := obj.x; let y := obj.y; body
       if (decl && ts.isObjectBindingPattern(decl.name) && decl.initializer) {
         const rhs = this.parseExpr(decl.initializer);
         // Build a chain of lets for each binding element
         let body = cont();
         const elems = [...decl.name.elements].reverse();
         for (const el of elems) {
           const propName = el.propertyName
             ? (ts.isIdentifier(el.propertyName) ? el.propertyName.text : el.propertyName.getText(this.sf))
             : (ts.isIdentifier(el.name) ? el.name.text : `_el${el.pos}`);
           const bindName = ts.isIdentifier(el.name) ? el.name.text : `_el${el.pos}`;
           const ty = mapType(this.checker.getTypeAtLocation(el.name), this.checker);
           const fieldVal: IRExpr = { tag: 'FieldAccess', obj: rhs, field: propName, type: ty, effect: rhs.effect };
           body = { tag: 'Let', name: bindName, annot: ty, value: fieldVal, body, type: body.type, effect: combineEffects([rhs.effect, body.effect]) };
         }
         return body;
       }
       // Array destructuring: const [a, b] = arr  →  let a := arr[0]!; let b := arr[1]!
       if (decl && ts.isArrayBindingPattern(decl.name) && decl.initializer) {
         const rhs = this.parseExpr(decl.initializer);
         let body = cont();
         const elems = [...decl.name.elements].reverse();
         elems.forEach((el, revIdx) => {
           const idx = elems.length - 1 - revIdx;
           if (ts.isOmittedExpression(el)) return;
           const bindName = ts.isBindingElement(el) && ts.isIdentifier(el.name) ? el.name.text : `_ai${idx}`;
           const ty = mapType(this.checker.getTypeAtLocation(el), this.checker);
           const indexVal: IRExpr = { tag: 'IndexAccess', obj: rhs, index: litNat(idx), type: ty, effect: rhs.effect };
           body = { tag: 'Let', name: bindName, annot: ty, value: indexVal, body, type: body.type, effect: combineEffects([rhs.effect, body.effect]) };
         });
         return body;
       }
     }

    // if (CPS early-return)
    if (ts.isIfStatement(stmt)) return this.parseIf(stmt, rest, eff);

    // for-of
    if (ts.isForOfStatement(stmt)) {
      const iter    = this.parseExpr(stmt.expression);
      const binding = ts.isVariableDeclarationList(stmt.initializer)
        ? (stmt.initializer.declarations[0].name as ts.Identifier).text : '_x';
      const body = ts.isBlock(stmt.statement)
        ? this.parseBlock(stmt.statement, eff)
        : this.parseStmt(stmt.statement as ts.Statement, [], eff);
      const loop: IRExpr = {
        tag: 'App',
        fn: varExpr('Array.forM', TyFn([TyArray(TyUnit), TyFn([TyUnit], TyUnit)], TyUnit)),
        args: [iter, { tag: 'Lambda', params: [{ name: binding, type: TyUnit }], body, type: TyFn([TyUnit], TyUnit), effect: body.effect }],
        type: TyUnit, effect: combineEffects([iter.effect, body.effect]),
      };
      const c = cont();
      return c.tag === 'LitUnit' ? loop : seq(loop, c);
    }

    // for
     if (ts.isForStatement(stmt)) {
       const loop = this.parseFor(stmt, eff);
       const c = cont();
       return c.tag === 'LitUnit' ? loop : seq(loop, c);
     }

     // for-in: for (const k in obj) — iterate over keys
     if (ts.isForInStatement(stmt)) {
       const obj     = this.parseExpr(stmt.expression);
       const binding = ts.isVariableDeclarationList(stmt.initializer)
         ? (stmt.initializer.declarations[0].name as ts.Identifier).text : '_k';
       const body = ts.isBlock(stmt.statement)
         ? this.parseBlock(stmt.statement, eff)
         : this.parseStmt(stmt.statement as ts.Statement, [], eff);
       const keysExpr: IRExpr = { tag: 'App', fn: varExpr('AssocMap.keys'), args: [obj], type: TyArray(TyString), effect: Pure };
       const loop: IRExpr = {
         tag: 'App',
         fn: varExpr('Array.forM', TyFn([TyArray(TyString), TyFn([TyString], TyUnit)], TyUnit)),
         args: [keysExpr, { tag: 'Lambda', params: [{ name: binding, type: TyString }], body, type: TyFn([TyString], TyUnit), effect: body.effect }],
         type: TyUnit, effect: combineEffects([obj.effect, body.effect]),
       };
       const c = cont();
       return c.tag === 'LitUnit' ? loop : seq(loop, c);
     }

     // while
     if (ts.isWhileStatement(stmt)) {
      const loop = this.parseWhile(stmt, eff);
      const c = cont();
      return c.tag === 'LitUnit' ? loop : seq(loop, c);
    }

    // throw
    if (ts.isThrowStatement(stmt)) {
      const err = stmt.expression ? this.parseExpr(stmt.expression) : litStr('error');
      return { tag: 'Throw', error: err, type: TyNever, effect: exceptEffect(TyString) };
    }

    // try
    if (ts.isTryStatement(stmt)) return this.parseTry(stmt, rest, eff);

    // switch
    if (ts.isSwitchStatement(stmt)) {
      const m = this.parseSwitch(stmt);
      const c = cont();
      return c.tag === 'LitUnit' ? m : seq(m, c);
    }

    // block
    if (ts.isBlock(stmt)) {
      const inner = this.parseBlock(stmt, eff);
      const c = cont();
      return c.tag === 'LitUnit' ? inner : seq(inner, c);
    }

    // expression statement
    if (ts.isExpressionStatement(stmt)) {
      const e = this.parseExpr(stmt.expression);
      const c = cont();
      return c.tag === 'LitUnit' ? e : seq(e, c);
    }

    return cont();
  }

  private parseIf(stmt: ts.IfStatement, rest: ReadonlyArray<ts.Statement>, eff: Effect): IRExpr {
    const cond  = this.parseExpr(stmt.expression);
    const then_ = ts.isBlock(stmt.thenStatement)
      ? this.parseBlock(stmt.thenStatement, eff)
      : this.parseStmt(stmt.thenStatement as ts.Statement, [], eff);

    const thenRets = branchReturns(then_);

    if (thenRets && rest.length > 0) {
      // CPS: if cond then <return> else <rest>
      const else_ = stmt.elseStatement
        ? (ts.isBlock(stmt.elseStatement) ? this.parseBlock(stmt.elseStatement, eff) : this.parseStmt(stmt.elseStatement as ts.Statement, rest, eff))
        : this.parseStmts(rest, eff);
      return { tag: 'IfThenElse', cond, then: then_, else_, type: else_.type, effect: combineEffects([cond.effect, then_.effect, else_.effect]) };
    }

    const else_ = stmt.elseStatement
      ? (ts.isBlock(stmt.elseStatement) ? this.parseBlock(stmt.elseStatement, eff) : this.parseStmt(stmt.elseStatement as ts.Statement, [], eff))
      : litUnit();

    const ifExpr: IRExpr = { tag: 'IfThenElse', cond, then: then_, else_, type: else_.type, effect: combineEffects([cond.effect, then_.effect, else_.effect]) };

    if (rest.length === 0) return ifExpr;
    const c = this.parseStmts(rest, eff);
    return seq(ifExpr, c);
  }

  private parseSwitch(node: ts.SwitchStatement): IRExpr {
    const scrutinee = this.parseExpr(node.expression);
    const cases: IRCase[] = [];
    let hasDefault = false;
    for (const cl of node.caseBlock.clauses) {
      if (ts.isCaseClause(cl)) {
        const caseExpr = this.parseExpr(cl.expression);
        const pat = exprToPat(caseExpr);
        // Fall-through: propagate body from next non-empty clause when this one is empty
        const body = this.parseSwitchCaseBody(cl, node.caseBlock.clauses);
        // Always include the case (even if body is LitUnit — the pattern is still meaningful)
        // Exception: skip if there's a next clause with the same body (deduplication)
        cases.push({ pattern: pat, body });
      } else {
        hasDefault = true;
        const body = this.parseStmts(cl.statements, Pure);
        cases.push({ pattern: { tag: 'PWild' }, body });
      }
    }
    // Add wildcard if no default
    if (!hasDefault && cases.length > 0) {
      cases.push({ pattern: { tag: 'PWild' }, body: litUnit() });
    }
    return { tag: 'Match', scrutinee, cases, type: cases[0]?.body.type ?? TyUnit, effect: combineEffects(cases.map(c => c.body.effect)) };
  }

  private parseSwitchCaseBody(cl: ts.CaseClause, allClauses: ts.NodeArray<ts.CaseOrDefaultClause>): IRExpr {
    // Filter out break statements — they are control-flow in JS, not needed in Lean match.
    const stmts = Array.from(cl.statements).filter(s => !ts.isBreakStatement(s) && !ts.isContinueStatement(s));

    // If this clause has no statements (fall-through pattern like `case 'N': case 'S': return ...`),
    // find the next sibling clause that has statements and use its body.
    if (stmts.length === 0) {
      const idx = allClauses.indexOf(cl);
      for (let i = idx + 1; i < allClauses.length; i++) {
        const next = allClauses[i];
        const nextStmts = Array.from(next.statements).filter(s => !ts.isBreakStatement(s) && !ts.isContinueStatement(s));
        if (nextStmts.length > 0) {
          return this.parseStmts(nextStmts, Pure);
        }
      }
      return litUnit();
    }

    return this.parseStmts(stmts, Pure);
  }

  private parseTry(node: ts.TryStatement, rest: ReadonlyArray<ts.Statement>, eff: Effect): IRExpr {
    const body = this.parseBlock(node.tryBlock, eff);
    const errName = node.catchClause?.variableDeclaration?.name
      ? (node.catchClause.variableDeclaration.name as ts.Identifier).text : '_e';
    const handler = node.catchClause?.block
      ? this.parseBlock(node.catchClause.block, eff)
      : varExpr(errName);
    const tryCatch: IRExpr = { tag: 'TryCatch', body, errName, handler, type: body.type, effect: body.effect };
    if (rest.length === 0) return tryCatch;
    return seq(tryCatch, this.parseStmts(rest, eff));
  }

  private parseFor(node: ts.ForStatement, eff: Effect): IRExpr {
    const init   = node.initializer && ts.isVariableDeclarationList(node.initializer)
      ? node.initializer.declarations[0] : null;
    const iName  = (init && ts.isIdentifier(init.name)) ? init.name.text : '_i';
    const iVal   = init?.initializer ? this.parseExpr(init.initializer) : litNat(0);
    const cond   = node.condition ? this.parseExpr(node.condition) : litBool(true);
    const body   = ts.isBlock(node.statement)
      ? this.parseBlock(node.statement, eff)
      : this.parseStmt(node.statement as ts.Statement, [], eff);
    const incrParsed: IRExpr = node.incrementor
      ? this.parseExpr(node.incrementor)
      : { tag: 'BinOp', op: 'Add', left: varExpr(iName, TyNat), right: litNat(1), type: TyNat, effect: Pure };
    // When the incrementor parsed as an Assign (i++ / i += n), extract just the new value
    // so the recursive call receives the updated counter, not a `let i := ...` statement.
    const incrArg: IRExpr = (incrParsed.tag === 'Assign' && incrParsed.target.tag === 'Var')
      ? incrParsed.value
      : incrParsed;
    const lName  = `_loop_${node.pos}`;
    const recurse: IRExpr = { tag: 'App', fn: varExpr(lName), args: [incrArg], type: TyUnit, effect: Pure };
    const loopBody: IRExpr = {
      tag: 'IfThenElse', cond, then: seq(body, recurse),
      else_: litUnit(), type: TyUnit, effect: combineEffects([cond.effect, body.effect]),
    };
    return {
      tag: 'Let', name: lName,
      value: { tag: 'Lambda', params: [{ name: iName, type: TyNat }], body: loopBody, type: TyFn([TyNat], TyUnit), effect: body.effect },
      body: { tag: 'App', fn: varExpr(lName), args: [iVal], type: TyUnit, effect: Pure },
      type: TyUnit, effect: body.effect,
    };
  }

  private parseWhile(node: ts.WhileStatement, eff: Effect): IRExpr {
    const cond  = this.parseExpr(node.expression);
    const body  = ts.isBlock(node.statement)
      ? this.parseBlock(node.statement, eff)
      : this.parseStmt(node.statement as ts.Statement, [], eff);
    const lName = `_while_${node.pos}`;
    const recurse: IRExpr = { tag: 'App', fn: varExpr(lName), args: [], type: TyUnit, effect: Pure };
    const lBody: IRExpr = {
      tag: 'IfThenElse', cond, then: seq(body, recurse),
      else_: litUnit(), type: TyUnit, effect: combineEffects([cond.effect, body.effect]),
    };
    return {
      tag: 'Let', name: lName,
      value: { tag: 'Lambda', params: [], body: lBody, type: TyFn([], TyUnit), effect: body.effect },
      body: { tag: 'App', fn: varExpr(lName), args: [], type: TyUnit, effect: Pure },
      type: TyUnit, effect: body.effect,
    };
  }

  // ─── Expressions ──────────────────────────────────────────────────────────

  parseExpr(node: ts.Expression): IRExpr {
    const ty = mapType(this.checker.getTypeAtLocation(node), this.checker);

    if (ts.isNumericLiteral(node)) {
      const v = Number(node.text);
      return Number.isInteger(v) && v >= 0
        ? { tag: 'LitNat', value: v, type: TyNat, effect: Pure }
        : { tag: 'LitFloat', value: v, type: TyFloat, effect: Pure };
    }
    if (ts.isStringLiteral(node) || ts.isNoSubstitutionTemplateLiteral(node))
      return litStr(node.text);
    if (ts.isTemplateExpression(node)) return this.parseTemplate(node);
    if (node.kind === ts.SyntaxKind.TrueKeyword)  return litBool(true);
    if (node.kind === ts.SyntaxKind.FalseKeyword) return litBool(false);
    if (node.kind === ts.SyntaxKind.NullKeyword || node.kind === ts.SyntaxKind.UndefinedKeyword)
      return { tag: 'LitNull', type: TyOption(TyUnit), effect: Pure };
    if (ts.isIdentifier(node))
      return varExpr(node.text === 'undefined' ? 'none' : node.text, ty);
    if (node.kind === ts.SyntaxKind.ThisKeyword)
      return varExpr('self', ty);
    if (ts.isPropertyAccessExpression(node)) return this.parsePropAccess(node, ty);
    if (ts.isElementAccessExpression(node)) {
      const obj   = this.parseExpr(node.expression);
      const index = this.parseExpr(node.argumentExpression);
      // Optional element access node?.["key"]
      if ((node as any).questionDotToken) {
        return { tag: 'App', fn: varExpr('Array.get?'), args: [obj, index], type: TyOption(ty), effect: Pure };
      }
      return { tag: 'IndexAccess', obj, index, type: ty, effect: Pure };
    }
    if (ts.isCallExpression(node))       return this.parseCall(node, ty);
    if (ts.isNewExpression(node))        return this.parseNew(node, ty);
    if (ts.isArrowFunction(node) || ts.isFunctionExpression(node)) return this.parseLambda(node);
    if (ts.isBinaryExpression(node)) {
      // Special binary operators handled before generic parseBinary
      if (node.operatorToken.kind === ts.SyntaxKind.InstanceOfKeyword) {
        const expr = this.parseExpr(node.left);
        const testTy = mapType(this.checker.getTypeAtLocation(node.right), this.checker);
        return { tag: 'IsType', expr, testType: testTy, type: TyBool, effect: expr.effect };
      }
      if (node.operatorToken.kind === ts.SyntaxKind.InKeyword) {
        const key = this.parseExpr(node.left);
        const obj = this.parseExpr(node.right);
        return { tag: 'App', fn: varExpr('AssocMap.contains'), args: [obj, key], type: TyBool, effect: Pure };
      }
      if (node.operatorToken.kind === ts.SyntaxKind.CommaToken) {
        const left  = this.parseExpr(node.left);
        const right = this.parseExpr(node.right);
        return { tag: 'Sequence', stmts: [left, right], type: right.type, effect: combineEffects([left.effect, right.effect]) };
      }
      return this.parseBinary(node, ty);
    }
    if (ts.isPrefixUnaryExpression(node))  return this.parsePrefix(node, ty);
    if (ts.isPostfixUnaryExpression(node)) return this.parsePostfix(node);
    if (ts.isConditionalExpression(node)) {
      const cond  = this.parseExpr(node.condition);
      const then_ = this.parseExpr(node.whenTrue);
      const else_ = this.parseExpr(node.whenFalse);
      return { tag: 'IfThenElse', cond, then: then_, else_, type: then_.type, effect: combineEffects([cond.effect, then_.effect, else_.effect]) };
    }
    if (ts.isObjectLiteralExpression(node)) return this.parseObjLit(node, ty);
    if (ts.isArrayLiteralExpression(node)) {
      const elems = node.elements.map(e =>
        ts.isSpreadElement(e) ? this.parseExpr(e.expression) : this.parseExpr(e)
      );
      return { tag: 'ArrayLit', elems, type: TyArray(elems[0]?.type ?? TyUnit), effect: combineEffects(elems.map(e => e.effect)) };
    }
    if (ts.isAwaitExpression(node)) {
      const inner = this.parseExpr(node.expression);
      return { tag: 'Await', expr: inner, type: ty, effect: Async };
    }
    if (ts.isAsExpression(node) || ts.isTypeAssertionExpression(node)) {
      const inner = this.parseExpr(node.expression);
      // `as const` is transparent
      return { tag: 'Cast', expr: inner, targetType: ty, type: ty, effect: inner.effect };
    }
    if (ts.isSatisfiesExpression(node)) return this.parseExpr(node.expression);
    if (ts.isParenthesizedExpression(node)) return this.parseExpr(node.expression);
    if (ts.isNonNullExpression(node))       return this.parseExpr(node.expression);
    if (ts.isVoidExpression(node)) {
      const inner = this.parseExpr(node.expression);
      return isPure(inner.effect) ? litUnit() : seq(inner, litUnit());
    }
    if (ts.isSpreadElement(node)) return this.parseExpr(node.expression);
    if (ts.isTypeOfExpression(node)) {
      const inner = this.parseExpr(node.expression);
      return { tag: 'App', fn: varExpr('TSLean.typeOf'), args: [inner], type: TyString, effect: Pure };
    }
    // Tagged template expressions (tagged`...`) → treat as regular template
    if (ts.isTaggedTemplateExpression(node)) {
      const template = node.template;
      if (ts.isNoSubstitutionTemplateLiteral(template)) return litStr(template.text);
      if (ts.isTemplateExpression(template)) return this.parseTemplate(template);
      return holeExpr(ty);
    }
    // Delete expression: delete obj.prop
    if (ts.isDeleteExpression(node)) return litBool(true);

    // Destructuring assignment: [a, b] = ... or { x } = ...
    if (node.kind === ts.SyntaxKind.ObjectLiteralExpression) return this.parseObjLit(node as ts.ObjectLiteralExpression, ty);

    return holeExpr(ty);
  }

  private parsePropAccess(node: ts.PropertyAccessExpression, ty: IRType): IRExpr {
    const obj   = this.parseExpr(node.expression);
    const field = node.name.text;
    if (node.expression.kind === ts.SyntaxKind.ThisKeyword)
      return { tag: 'FieldAccess', obj: varExpr('self', obj.type), field, type: ty, effect: Pure };

    // Optional chaining: obj?.field  →  Option.map (·.field) obj
    // When obj is already an Option we chain: Option.bind obj (fun o => some o.field)
    if (node.questionDotToken) {
      const accessor: IRExpr = { tag: 'Lambda', params: [{ name: '_oc', type: obj.type }],
        body: { tag: 'FieldAccess', obj: varExpr('_oc', obj.type), field, type: ty, effect: Pure },
        type: TyFn([obj.type], ty), effect: Pure };
      return { tag: 'App', fn: varExpr('Option.map'), args: [accessor, obj], type: TyOption(ty), effect: obj.effect };
    }

    return { tag: 'FieldAccess', obj, field, type: ty, effect: Pure };
  }

  private parseCall(node: ts.CallExpression, ty: IRType): IRExpr {
    if (ts.isPropertyAccessExpression(node.expression))
      return this.parseMethodCall(node, node.expression, ty);
    const fn   = this.parseExpr(node.expression);
    const args = node.arguments.map(a => this.parseExpr(a));
    return { tag: 'App', fn, args, type: ty, effect: combineEffects([fn.effect, ...args.map(a => a.effect)]) };
  }

  private parseMethodCall(node: ts.CallExpression, acc: ts.PropertyAccessExpression, ty: IRType): IRExpr {
    const obj    = this.parseExpr(acc.expression);
    const method = acc.name.text;
    const args   = node.arguments.map(a => this.parseExpr(a));
    const allEff = combineEffects([obj.effect, ...args.map(a => a.effect)]);
    // DO storage operations
    const storageTarget = this.isStorageAccess(acc.expression);
    if (storageTarget) {
      const fn = `Storage.${method}`;
      return { tag: 'App', fn: varExpr(fn), args: [obj, ...args], type: ty, effect: Async };
    }
    return {
      tag: 'App',
      fn: { tag: 'FieldAccess', obj, field: method, type: TyFn(args.map(a => a.type), ty), effect: Pure },
      args, type: ty, effect: allEff,
    };
  }

  private isStorageAccess(node: ts.Expression): boolean {
    const text = node.getText(this.sf);
    return text.includes('.storage') || text === 'storage' || text.includes('this.state.storage');
  }

  private parseNew(node: ts.NewExpression, ty: IRType): IRExpr {
    const name = node.expression.getText(this.sf);
    const args = (node.arguments ?? []).map(a => this.parseExpr(a));
    if (name === 'Map')      return varExpr('AssocMap.empty', ty);
    if (name === 'Set')      return varExpr('AssocSet.empty', ty);
    if (name === 'Array')    return { tag: 'ArrayLit', elems: [], type: ty, effect: Pure };
    if (name === 'Error' || name.endsWith('Error'))
      return { tag: 'App', fn: varExpr('TSError.mk'), args, type: ty, effect: Pure };
    if (name === 'Response')
      return { tag: 'App', fn: varExpr('mkResponse'), args, type: ty, effect: Pure };
    return { tag: 'CtorApp', ctor: name, args, type: ty, effect: combineEffects(args.map(a => a.effect)) };
  }

  private parseLambda(node: ts.ArrowFunction | ts.FunctionExpression): IRExpr {
    const params = this.parseParams(node.parameters);
    const eff    = inferNodeEffect(node, this.checker);
    const body   = ts.isBlock(node.body as ts.Node)
      ? this.parseBlock(node.body as ts.Block, eff)
      : this.parseExpr(node.body as ts.Expression);
    const sig    = this.checker.getSignatureFromDeclaration(node)!;
    const ret    = sig ? mapType(this.checker.getReturnTypeOfSignature(sig), this.checker) : body.type;
    return { tag: 'Lambda', params, body, type: TyFn(params.map(p => p.type), ret, eff), effect: eff };
  }

  private parseBinary(node: ts.BinaryExpression, ty: IRType): IRExpr {
    const op = node.operatorToken.kind;
    if (op === ts.SyntaxKind.EqualsToken || isCompoundAssign(op)) {
      const target = this.parseExpr(node.left);
      const rhs    = this.parseExpr(node.right);
      const val    = isCompoundAssign(op) ? mkBinOp(compoundOp(op), target, rhs) : rhs;
      return { tag: 'Assign', target, value: val, type: TyUnit, effect: stateEffect(TyUnit) };
    }
    const left  = this.parseExpr(node.left);
    const right = this.parseExpr(node.right);
    const irOp  = tsBinOp(op);
    if (!irOp) return holeExpr(ty);
    return { tag: 'BinOp', op: irOp, left, right, type: ty, effect: combineEffects([left.effect, right.effect]) };
  }

  private parsePrefix(node: ts.PrefixUnaryExpression, ty: IRType): IRExpr {
    const operand = this.parseExpr(node.operand);
    switch (node.operator) {
      case ts.SyntaxKind.ExclamationToken: return { tag: 'UnOp', op: 'Not', operand, type: TyBool, effect: operand.effect };
      case ts.SyntaxKind.MinusToken:       return { tag: 'UnOp', op: 'Neg', operand, type: operand.type, effect: operand.effect };
      case ts.SyntaxKind.TildeToken:       return { tag: 'UnOp', op: 'BitNot', operand, type: ty, effect: operand.effect };
      case ts.SyntaxKind.PlusPlusToken:
        return { tag: 'Assign', target: operand, value: mkBinOp('Add', operand, litNat(1)), type: TyUnit, effect: stateEffect(TyUnit) };
      case ts.SyntaxKind.MinusMinusToken:
        return { tag: 'Assign', target: operand, value: mkBinOp('Sub', operand, litNat(1)), type: TyUnit, effect: stateEffect(TyUnit) };
      default: return operand;
    }
  }

  private parsePostfix(node: ts.PostfixUnaryExpression): IRExpr {
    const operand = this.parseExpr(node.operand);
    if (node.operator === ts.SyntaxKind.PlusPlusToken)
      return { tag: 'Assign', target: operand, value: mkBinOp('Add', operand, litNat(1)), type: TyUnit, effect: stateEffect(TyUnit) };
    return { tag: 'Assign', target: operand, value: mkBinOp('Sub', operand, litNat(1)), type: TyUnit, effect: stateEffect(TyUnit) };
  }

  private parseObjLit(node: ts.ObjectLiteralExpression, ty: IRType): IRExpr {
    const typeName = ty.tag === 'TypeRef' ? ty.name : ty.tag === 'Structure' ? ty.name : 'AnonStruct';

    // Separate spread elements from named fields
    const spreadExprs: IRExpr[] = [];
    const namedFields: Array<{ name: string; value: IRExpr }> = [];

    for (const prop of node.properties) {
      if (ts.isPropertyAssignment(prop)) {
        const name = ts.isIdentifier(prop.name) ? prop.name.text : prop.name.getText(this.sf);
        namedFields.push({ name, value: this.parseExpr(prop.initializer) });
      } else if (ts.isShorthandPropertyAssignment(prop)) {
        namedFields.push({ name: prop.name.text, value: varExpr(prop.name.text) });
      } else if (ts.isSpreadAssignment(prop)) {
        spreadExprs.push(this.parseExpr(prop.expression));
      }
    }

    const allEffect = combineEffects([...spreadExprs.map(e => e.effect), ...namedFields.map(f => f.value.effect)]);

    // Pattern: { ...base, field: v } → structUpdate(base, [{field: v}], ty)
    // This correctly generates `{ base with field := v }` in Lean 4.
    if (spreadExprs.length === 1 && namedFields.length > 0) {
      return {
        tag: 'StructUpdate',
        base: spreadExprs[0],
        fields: namedFields,
        type: ty, effect: allEffect,
      };
    }

    // Multiple spreads or spread-only: best effort — use the last spread as base
    if (spreadExprs.length > 1 && namedFields.length > 0) {
      // Chain: { ...a, ...b, f: v } → { (merge a b) with f := v }
      const mergedBase = spreadExprs.reduce((acc, e) => ({
        tag: 'App' as const,
        fn: varExpr('AssocMap.mergeWith (fun _ b => b)'),
        args: [acc, e],
        type: ty, effect: combineEffects([acc.effect, e.effect]),
      }));
      return { tag: 'StructUpdate', base: mergedBase, fields: namedFields, type: ty, effect: allEffect };
    }

    if (spreadExprs.length > 0 && namedFields.length === 0) {
      // Pure spread: { ...obj } → obj (identity/clone)
      return spreadExprs.length === 1 ? spreadExprs[0] : {
        tag: 'App', fn: varExpr('id'), args: spreadExprs, type: ty, effect: allEffect,
      };
    }

    // No spread: plain struct literal
    return { tag: 'StructLit', typeName, fields: namedFields, type: ty, effect: allEffect };
  }

  private parseTemplate(node: ts.TemplateExpression): IRExpr {
    const parts: IRExpr[] = [litStr(node.head.text)];
    for (const span of node.templateSpans) {
      parts.push(this.parseExpr(span.expression));
      parts.push(litStr(span.literal.text));
    }
    return parts.filter(p => !(p.tag === 'LitString' && p.value === ''))
      .reduce((acc, p) => ({
        tag: 'BinOp', op: 'Concat', left: acc, right: p,
        type: TyString, effect: combineEffects([acc.effect, p.effect]),
      }));
  }
}

// ─── Helpers ──────────────────────────────────────────────────────────────────

function seq(a: IRExpr, b: IRExpr): IRExpr {
  if (b.tag === 'LitUnit') return a;
  if (a.tag === 'LitUnit') return b;
  if (a.tag === 'Sequence') return { tag: 'Sequence', stmts: [...a.stmts, b], type: b.type, effect: combineEffects([a.effect, b.effect]) };
  return { tag: 'Sequence', stmts: [a, b], type: b.type, effect: combineEffects([a.effect, b.effect]) };
}

function mkBinOp(op: BinOp, left: IRExpr, right: IRExpr): IRExpr {
  return { tag: 'BinOp', op, left, right, type: left.type, effect: Pure };
}

function branchReturns(e: IRExpr): boolean {
  if (e.tag === 'Return' || e.tag === 'Throw') return true;
  if (e.tag === 'Sequence') return branchReturns(e.stmts[e.stmts.length - 1]);
  if (e.tag === 'Let')      return branchReturns(e.body);
  if (e.tag === 'IfThenElse') return branchReturns(e.then) && branchReturns(e.else_);
  return false;
}

function exprToPat(e: IRExpr): IRPattern {
  if (e.tag === 'LitString') return { tag: 'PString', value: e.value };
  if (e.tag === 'LitNat')    return { tag: 'PLit', value: e.value };
  if (e.tag === 'LitBool')   return { tag: 'PLit', value: e.value };
  if (e.tag === 'LitNull')   return { tag: 'PNone' };
  if (e.tag === 'Var')       return { tag: 'PVar', name: e.name };
  return { tag: 'PWild' };
}

function isCompoundAssign(kind: ts.SyntaxKind): boolean {
  return kind === ts.SyntaxKind.PlusEqualsToken    || kind === ts.SyntaxKind.MinusEqualsToken  ||
         kind === ts.SyntaxKind.AsteriskEqualsToken || kind === ts.SyntaxKind.SlashEqualsToken  ||
         kind === ts.SyntaxKind.PercentEqualsToken  || kind === ts.SyntaxKind.AmpersandEqualsToken ||
         kind === ts.SyntaxKind.BarEqualsToken      || kind === ts.SyntaxKind.CaretEqualsToken;
}

function compoundOp(kind: ts.SyntaxKind): BinOp {
  switch (kind) {
    case ts.SyntaxKind.PlusEqualsToken:     return 'Add';
    case ts.SyntaxKind.MinusEqualsToken:    return 'Sub';
    case ts.SyntaxKind.AsteriskEqualsToken: return 'Mul';
    case ts.SyntaxKind.SlashEqualsToken:    return 'Div';
    case ts.SyntaxKind.PercentEqualsToken:  return 'Mod';
    default:                                return 'Add';
  }
}

function tsBinOp(kind: ts.SyntaxKind): BinOp | null {
  switch (kind) {
    case ts.SyntaxKind.PlusToken:                    return 'Add';
    case ts.SyntaxKind.MinusToken:                   return 'Sub';
    case ts.SyntaxKind.AsteriskToken:                return 'Mul';
    case ts.SyntaxKind.SlashToken:                   return 'Div';
    case ts.SyntaxKind.PercentToken:                 return 'Mod';
    case ts.SyntaxKind.EqualsEqualsToken:
    case ts.SyntaxKind.EqualsEqualsEqualsToken:      return 'Eq';
    case ts.SyntaxKind.ExclamationEqualsToken:
    case ts.SyntaxKind.ExclamationEqualsEqualsToken: return 'Ne';
    case ts.SyntaxKind.LessThanToken:                return 'Lt';
    case ts.SyntaxKind.LessThanEqualsToken:          return 'Le';
    case ts.SyntaxKind.GreaterThanToken:             return 'Gt';
    case ts.SyntaxKind.GreaterThanEqualsToken:       return 'Ge';
    case ts.SyntaxKind.AmpersandAmpersandToken:      return 'And';
    case ts.SyntaxKind.BarBarToken:                  return 'Or';
    case ts.SyntaxKind.QuestionQuestionToken:        return 'NullCoalesce';
    case ts.SyntaxKind.AmpersandToken:               return 'BitAnd';
    case ts.SyntaxKind.BarToken:                     return 'BitOr';
    case ts.SyntaxKind.CaretToken:                   return 'BitXor';
    case ts.SyntaxKind.LessThanLessThanToken:        return 'Shl';
    case ts.SyntaxKind.GreaterThanGreaterThanToken:  return 'Shr';
    default:                                         return null;
  }
}

function cap(s: string): string {
  return s ? s[0].toUpperCase() + s.slice(1) : s;
}

function fileToModuleName(filePath: string): string {
  const base  = path.basename(filePath, '.ts');
  const parts = base.split(/[-_]/).map(cap);
  return 'TSLean.Generated.' + parts.join('');
}

function leadingComment(node: ts.Node, sf: ts.SourceFile): string | undefined {
  const ranges = ts.getLeadingCommentRanges(sf.getFullText(), node.getFullStart());
  if (!ranges?.length) return undefined;
  return ranges.map(r => sf.getFullText().slice(r.pos, r.end)).join('\n');
}

/** Extract JSDoc comment text (/** ... *\/) from a node.
 *  Strips @param/@returns/@throws tags — these use a different Lean 4 syntax.
 *  Returns just the summary description.
 */
function jsdocComment(node: ts.Node, sf: ts.SourceFile): string | undefined {
  const ranges = ts.getLeadingCommentRanges(sf.getFullText(), node.getFullStart());
  if (!ranges?.length) return undefined;
  for (const r of ranges) {
    const text = sf.getFullText().slice(r.pos, r.end);
    if (text.startsWith('/**')) {
      const lines = text
        .replace(/^\/\*\*\s*/, '')
        .replace(/\s*\*\/$/, '')
        .split('\n')
        .map(l => l.replace(/^\s*\*\s?/, '').trim());
      // Keep only non-tag lines (before any @param/@returns/@throws etc.)
      const descLines: string[] = [];
      for (const line of lines) {
        if (line.startsWith('@')) break;  // Stop at first tag
        if (line) descLines.push(line);
      }
      const desc = descLines.join(' ').trim();
      return desc || undefined;
    }
  }
  return undefined;
}

/** Check if a statement has a const/let/var with an interface/object type that acts as index signature */
function hasIndexSignature(node: ts.Node, checker: ts.TypeChecker): boolean {
  if (!ts.isInterfaceDeclaration(node) && !ts.isTypeLiteralNode(node)) return false;
  const members = ts.isInterfaceDeclaration(node) ? node.members : (node as ts.TypeLiteralNode).members;
  return members.some(m => ts.isIndexSignatureDeclaration(m));
}
