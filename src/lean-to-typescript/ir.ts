import ts from 'typescript';
import type { LeanToTypeScriptClosureEntry, LeanToTypeScriptDeclarationRole } from './artifact.js';
import { compareCodePoints } from './ordering.js';

export const LEAN_TO_TYPESCRIPT_SCHEMA_VERSION = 1;
export const LEAN_TO_TYPESCRIPT_FRAGMENT_VERSION = 'tslean-structural-first-order-v4';

/**
 * The Lean module grammar the compiler admits: dot-separated segments beginning with `[A-Za-z_]`.
 * A module name selects the Lake module, the Lean import, the generated file path, and the
 * provenance identity, so it is validated once here and reused wherever a module name arrives.
 */
export function isLeanModuleName(value: string): boolean {
  return /^[A-Za-z_][\w'!?]*(?:\.[A-Za-z_][\w'!?]*)*$/u.test(value);
}

export type LeanType =
  | { readonly kind: 'boolean' }
  | { readonly kind: 'named'; readonly name: string }
  | { readonly kind: 'option'; readonly inner: LeanType };

export type LeanExpression =
  | { readonly kind: 'variable'; readonly index: number }
  | { readonly kind: 'boolean'; readonly value: boolean }
  | { readonly kind: 'let'; readonly name: string; readonly value: LeanExpression; readonly body: LeanExpression }
  | { readonly kind: 'field'; readonly target: LeanExpression; readonly field: string }
  | {
      readonly kind: 'if';
      readonly condition: LeanExpression;
      readonly consequent: LeanExpression;
      readonly alternate: LeanExpression;
    }
  | { readonly kind: 'equals'; readonly left: LeanExpression; readonly right: LeanExpression }
  | { readonly kind: 'and' | 'or'; readonly left: LeanExpression; readonly right: LeanExpression }
  | { readonly kind: 'not'; readonly operand: LeanExpression }
  | { readonly kind: 'some'; readonly value: LeanExpression }
  | { readonly kind: 'none' }
  | {
      readonly kind: 'variant';
      readonly type: string;
      readonly name: string;
      readonly arguments: readonly LeanExpression[];
    }
  | {
      readonly kind: 'record';
      readonly type: string;
      readonly fields: readonly { readonly name: string; readonly value: LeanExpression }[];
    }
  | {
      readonly kind: 'match';
      readonly type: string;
      readonly scrutinee: LeanExpression;
      readonly cases: readonly { readonly constructor: string; readonly value: LeanExpression }[];
    }
  | { readonly kind: 'call'; readonly function: string; readonly arguments: readonly LeanExpression[] };

export interface LeanDocumented {
  readonly doc?: string;
}

export interface LeanField extends LeanDocumented {
  readonly name: string;
  readonly type: LeanType;
}

export interface LeanEnumConstructor extends LeanDocumented {
  readonly name: string;
  readonly fields: readonly LeanField[];
}

/** Where a declaration is written, in its own Lean source. Lines are 1-based, columns 0-based. */
export interface LeanSpan {
  readonly startLine: number;
  readonly startColumn: number;
  readonly endLine: number;
  readonly endColumn: number;
}

interface LeanDeclared extends LeanDocumented {
  readonly name: string;
  /** The Lean module that declares it, which decides the generated file that carries it. */
  readonly module: string;
  readonly span: LeanSpan;
}

export type LeanDeclaration =
  | ({
      readonly kind: 'enum';
      readonly constructors: readonly LeanEnumConstructor[];
    } & LeanDeclared)
  | ({
      readonly kind: 'record';
      readonly fields: readonly LeanField[];
    } & LeanDeclared)
  | ({
      readonly kind: 'function';
      readonly parameters: readonly { readonly name: string; readonly type: LeanType }[];
      readonly result: LeanType;
      /** Present exactly when Lean proved the definition recurses structurally on that parameter. */
      readonly recursion?: { readonly argument: number };
      readonly body: LeanExpression;
    } & LeanDeclared);

export interface LeanSemanticProgram {
  readonly schemaVersion: 1;
  readonly fragmentVersion: typeof LEAN_TO_TYPESCRIPT_FRAGMENT_VERSION;
  readonly roots: readonly string[];
  /**
   * Every constant reachable from the roots and what the compiler did with it. The exporter
   * refuses anything it can neither emit, erase, nor admit at the runtime boundary, so this
   * accounts for the whole closure rather than the part that reached a generated file.
   */
  readonly closure: readonly LeanToTypeScriptClosureEntry[];
  readonly declarations: readonly LeanDeclaration[];
}

export function decodeLeanSemanticProgram(value: unknown): LeanSemanticProgram {
  const program = object(value, 'semantic program');
  exactKeys(program, ['schemaVersion', 'fragmentVersion', 'roots', 'closure', 'declarations'], 'semantic program');
  if (program['schemaVersion'] !== LEAN_TO_TYPESCRIPT_SCHEMA_VERSION) {
    throw new TypeError(`unsupported Lean semantic IR schema ${String(program['schemaVersion'])}`);
  }
  if (program['fragmentVersion'] !== LEAN_TO_TYPESCRIPT_FRAGMENT_VERSION) {
    throw new TypeError(`unsupported Lean fragment ${String(program['fragmentVersion'])}`);
  }
  const roots = stringArray(program['roots'], 'semantic program roots');
  const declarations = array(program['declarations'], 'semantic program declarations').map((declaration, index) =>
    decodeDeclaration(declaration, `declarations[${index}]`),
  );
  requireUnique(roots, 'semantic program roots');
  requireUnique(
    declarations.map((declaration) => declaration.name),
    'semantic program declarations',
  );
  const closure = array(program['closure'], 'semantic program closure').map((entry, index) =>
    decodeClosureEntry(entry, `closure[${index}]`),
  );
  assertClosureAccountsFor(closure, declarations);
  const decoded: LeanSemanticProgram = {
    schemaVersion: LEAN_TO_TYPESCRIPT_SCHEMA_VERSION,
    fragmentVersion: LEAN_TO_TYPESCRIPT_FRAGMENT_VERSION,
    roots,
    closure,
    declarations,
  };
  validateProgramReferences(decoded);
  return decoded;
}

function decodeClosureEntry(value: unknown, location: string): LeanToTypeScriptClosureEntry {
  const entry = object(value, location);
  exactKeys(entry, ['declaration', 'module', 'role', 'reason'], location);
  const role = entry['role'];
  if (role !== 'emitted' && role !== 'erased' && role !== 'runtime-boundary') {
    throw new TypeError(`${location}.role is unsupported: ${String(role)}`);
  }
  const reason = entry['reason'];
  if (typeof reason !== 'string') throw new TypeError(`${location}.reason must be a string`);
  if ((role === 'emitted') !== (reason === '')) {
    throw new TypeError(`${location}.reason must be empty exactly for an emitted declaration`);
  }
  const module = entry['module'];
  if (module !== '' && !isLeanModuleName(string(module, `${location}.module`))) {
    throw new TypeError(`${location}.module is not a Lean module name: ${String(module)}`);
  }
  return {
    declaration: qualifiedName(entry['declaration'], `${location}.declaration`),
    module: module === '' ? '' : string(module, `${location}.module`),
    role: role satisfies LeanToTypeScriptDeclarationRole,
    reason,
  };
}

/**
 * The closure is the compiler's own account of what it reached. It has to be ordered, unique, and
 * cover every emitted declaration exactly once under the `emitted` role, so a generated tree can
 * never carry a declaration the audit record does not mention.
 */
function assertClosureAccountsFor(
  closure: readonly LeanToTypeScriptClosureEntry[],
  declarations: readonly LeanDeclaration[],
): void {
  for (let index = 1; index < closure.length; index += 1) {
    const previous = closure[index - 1];
    const current = closure[index];
    if (previous === undefined || current === undefined) throw new TypeError('semantic program closure is sparse');
    if (compareCodePoints(previous.declaration, current.declaration) >= 0) {
      throw new TypeError('semantic program closure must be strictly ordered and unique');
    }
  }
  const emitted = new Set(closure.filter((entry) => entry.role === 'emitted').map((entry) => entry.declaration));
  for (const declaration of declarations) {
    if (!emitted.has(declaration.name)) {
      throw new TypeError(`semantic program closure does not record ${declaration.name} as emitted`);
    }
    const entry = closure.find((candidate) => candidate.declaration === declaration.name);
    if (entry !== undefined && entry.module !== declaration.module) {
      throw new TypeError(`semantic program closure disagrees on the module of ${declaration.name}`);
    }
  }
  if (emitted.size !== declarations.length) {
    throw new TypeError('semantic program closure records an emitted declaration that was not exported');
  }
}

/**
 * A qualified Lean name becomes its final component in TypeScript. Two different Lean modules can
 * legally declare `Config`; one generated module that imports both could not name them without an
 * aliasing policy the checked fragment has not specified. Refuse the collision before emission,
 * naming both sources instead of collapsing one into an arbitrary Map entry.
 */
function assertDistinctEmittedDeclarationNames(declarations: readonly LeanDeclaration[]): void {
  const owners = new Map<string, LeanDeclaration>();
  for (const declaration of [...declarations].sort((left, right) => compareCodePoints(left.name, right.name))) {
    const emitted = localName(declaration.name);
    const existing = owners.get(emitted);
    if (existing !== undefined && existing.module !== declaration.module) {
      throw new TypeError(
        `${existing.name} (${existing.module}) and ${declaration.name} (${declaration.module}) both emit ${emitted}; rename one before compiling this module tree`,
      );
    }
    owners.set(emitted, declaration);
  }
}
function validateProgramReferences(program: LeanSemanticProgram): void {
  const declarations = new Map(program.declarations.map((declaration) => [declaration.name, declaration]));
  const functions = new Map(
    program.declarations
      .filter(
        (declaration): declaration is Extract<LeanDeclaration, { kind: 'function' }> => declaration.kind === 'function',
      )
      .map((declaration) => [declaration.name, declaration]),
  );
  assertDistinctEmittedDeclarationNames(program.declarations);
  for (const declaration of program.declarations) {
    bindingIdentifier(localName(declaration.name), `declaration ${declaration.name}`);
  }

  for (const root of program.roots) {
    if (!functions.has(root)) throw new TypeError(`semantic program root is not a function: ${root}`);
  }
  const validateType = (type: LeanType, location: string): void => {
    if (type.kind === 'option') validateType(type.inner, `${location}.inner`);
    if (type.kind === 'named') {
      const declaration = declarations.get(type.name);
      if (declaration === undefined || declaration.kind === 'function') {
        throw new TypeError(`${location} references unknown data type ${type.name}`);
      }
    }
  };
  const booleanType: LeanType = { kind: 'boolean' };
  const requireType = (actual: LeanType, expected: LeanType | undefined, location: string): LeanType => {
    if (expected !== undefined && !sameType(actual, expected)) {
      throw new TypeError(`${location} has type ${renderType(actual)}; expected ${renderType(expected)}`);
    }
    return actual;
  };
  const checkExpression = (
    expression: LeanExpression,
    scope: readonly LeanType[],
    expected: LeanType | undefined,
    location: string,
  ): LeanType => {
    switch (expression.kind) {
      case 'variable': {
        const type = scope[expression.index];
        if (type === undefined) {
          throw new TypeError(`${location} has unbound de Bruijn index ${expression.index}`);
        }
        return requireType(type, expected, location);
      }
      case 'let': {
        const valueType = checkExpression(expression.value, scope, undefined, `${location}.value`);
        return checkExpression(expression.body, [valueType, ...scope], expected, `${location}.body`);
      }
      case 'field': {
        const targetType = checkExpression(expression.target, scope, undefined, `${location}.target`);
        if (targetType.kind !== 'named') {
          throw new TypeError(`${location}.target is not a record`);
        }
        const declaration = declarations.get(targetType.name);
        if (declaration === undefined || declaration.kind !== 'record') {
          throw new TypeError(`${location}.target is not a record`);
        }
        const field = declaration.fields.find((candidate) => candidate.name === expression.field);
        if (field === undefined) {
          throw new TypeError(`${location} references unknown field ${targetType.name}.${expression.field}`);
        }
        return requireType(field.type, expected, location);
      }
      case 'if': {
        checkExpression(expression.condition, scope, booleanType, `${location}.condition`);
        if (expected !== undefined) {
          checkExpression(expression.consequent, scope, expected, `${location}.consequent`);
          checkExpression(expression.alternate, scope, expected, `${location}.alternate`);
          return expected;
        }
        const consequent = checkExpression(expression.consequent, scope, undefined, `${location}.consequent`);
        checkExpression(expression.alternate, scope, consequent, `${location}.alternate`);
        return consequent;
      }
      case 'equals':
      case 'and':
      case 'or':
        checkExpression(expression.left, scope, booleanType, `${location}.left`);
        checkExpression(expression.right, scope, booleanType, `${location}.right`);
        return requireType(booleanType, expected, location);
      case 'not':
        checkExpression(expression.operand, scope, booleanType, `${location}.operand`);
        return requireType(booleanType, expected, location);
      case 'some': {
        if (expected?.kind === 'option') {
          checkExpression(expression.value, scope, expected.inner, `${location}.value`);
          return expected;
        }
        const type: LeanType = {
          kind: 'option',
          inner: checkExpression(expression.value, scope, undefined, `${location}.value`),
        };
        return requireType(type, expected, location);
      }
      case 'none':
        if (expected?.kind !== 'option') {
          throw new TypeError(`${location} requires an expected Option type`);
        }
        return expected;
      case 'variant': {
        const declaration = declarations.get(expression.type);
        if (declaration === undefined || declaration.kind !== 'enum') {
          throw new TypeError(`${location} references unknown enum ${expression.type}`);
        }
        const constructor = declaration.constructors.find((candidate) => candidate.name === expression.name);
        if (constructor === undefined) {
          throw new TypeError(`${location} references unknown constructor ${expression.type}.${expression.name}`);
        }
        if (constructor.fields.length !== expression.arguments.length) {
          throw new TypeError(
            `${location} passes ${expression.arguments.length} fields to ${expression.type}.${expression.name}; expected ${constructor.fields.length}`,
          );
        }
        expression.arguments.forEach((argument, index) => {
          const field = constructor.fields[index];
          if (field === undefined) throw new TypeError(`${location} has an unmatched constructor field`);
          checkExpression(argument, scope, field.type, `${location}.arguments[${index}]`);
        });
        return requireType({ kind: 'named', name: expression.type }, expected, location);
      }
      case 'match': {
        const declaration = declarations.get(expression.type);
        if (declaration === undefined || declaration.kind !== 'enum') {
          throw new TypeError(`${location} references unknown enum ${expression.type}`);
        }
        checkExpression(expression.scrutinee, scope, { kind: 'named', name: expression.type }, `${location}.scrutinee`);
        const constructors = declaration.constructors.map((constructor) => constructor.name);
        const decided = expression.cases.map((entry) => entry.constructor);
        if (
          decided.length !== constructors.length ||
          constructors.some((constructor, index) => constructor !== decided[index])
        ) {
          throw new TypeError(
            `${location} does not decide every constructor of ${expression.type} exactly once in declaration order`,
          );
        }
        // A payload-carrying alternative binds its constructor's fields, innermost binder last,
        // so the arm's scope is the constructor's field types reversed onto the enclosing scope.
        const armScope = (index: number): readonly LeanType[] => {
          const constructor = declaration.constructors[index];
          if (constructor === undefined) throw new TypeError(`${location} has an unmatched alternative`);
          return constructor.fields
            .map((field) => field.type)
            .reverse()
            .concat(scope);
        };
        if (expected !== undefined) {
          expression.cases.forEach((entry, index) =>
            checkExpression(entry.value, armScope(index), expected, `${location}.cases[${index}].value`),
          );
          return expected;
        }
        const [first, ...rest] = expression.cases;
        if (first === undefined) throw new TypeError(`${location} decides no constructor`);
        const result = checkExpression(first.value, armScope(0), undefined, `${location}.cases[0].value`);
        rest.forEach((entry, index) =>
          checkExpression(entry.value, armScope(index + 1), result, `${location}.cases[${index + 1}].value`),
        );
        return result;
      }
      case 'record': {
        const declaration = declarations.get(expression.type);
        if (declaration === undefined || declaration.kind !== 'record') {
          throw new TypeError(`${location} references unknown record ${expression.type}`);
        }
        const expectedFields = declaration.fields.map((field) => field.name).sort(compareCodePoints);
        const actualFields = expression.fields.map((field) => field.name).sort(compareCodePoints);
        if (
          expectedFields.length !== actualFields.length ||
          expectedFields.some((field, index) => field !== actualFields[index])
        ) {
          throw new TypeError(`${location} fields do not match record ${expression.type}`);
        }
        expression.fields.forEach((field, index) => {
          const fieldType = declaration.fields.find((candidate) => candidate.name === field.name)?.type;
          if (fieldType === undefined) throw new TypeError(`${location} has an unknown record field`);
          checkExpression(field.value, scope, fieldType, `${location}.fields[${index}].value`);
        });
        return requireType({ kind: 'named', name: expression.type }, expected, location);
      }
      case 'call': {
        const declaration = functions.get(expression.function);
        if (declaration === undefined) {
          throw new TypeError(`${location} references unknown function ${expression.function}`);
        }
        if (declaration.parameters.length !== expression.arguments.length) {
          throw new TypeError(
            `${location} passes ${expression.arguments.length} arguments to ${expression.function}; expected ${declaration.parameters.length}`,
          );
        }
        expression.arguments.forEach((argument, index) => {
          const parameter = declaration.parameters[index];
          if (parameter === undefined) throw new TypeError(`${location} has an unmatched argument`);
          checkExpression(argument, scope, parameter.type, `${location}.arguments[${index}]`);
        });
        return requireType(declaration.result, expected, location);
      }
      case 'boolean':
        return requireType(booleanType, expected, location);
    }
  };
  for (const declaration of program.declarations) {
    if (declaration.kind === 'function') validateStructuralRecursion(declaration, declarations);
    if (declaration.kind === 'record') {
      declaration.fields.forEach((field, index) =>
        validateType(field.type, `${declaration.name}.fields[${index}].type`),
      );
    }
    if (declaration.kind === 'enum') {
      for (const constructor of declaration.constructors) {
        constructor.fields.forEach((field, index) =>
          validateType(field.type, `${declaration.name}.${constructor.name}.fields[${index}].type`),
        );
      }
    }
    if (declaration.kind === 'function') {
      declaration.parameters.forEach((parameter, index) =>
        validateType(parameter.type, `${declaration.name}.parameters[${index}].type`),
      );
      validateType(declaration.result, `${declaration.name}.result`);
      checkExpression(
        declaration.body,
        declaration.parameters.map((parameter) => parameter.type).reverse(),
        declaration.result,
        `${declaration.name}.body`,
      );
    }
  }
}

type RecursionSlot = 'other' | 'recursive' | 'smaller';

/**
 * A self-call is admitted only where it passes a strictly smaller value at the parameter Lean
 * proved the recursion decreases on: the recursion parameter's own constructor fields, taken from
 * a match on it. That is the same structural argument Lean checked, restated over the emitted
 * program, so the generated recursion terminates for the reason the Lean definition does.
 */
function validateStructuralRecursion(
  declaration: Extract<LeanDeclaration, { kind: 'function' }>,
  declarations: ReadonlyMap<string, LeanDeclaration>,
): void {
  const recursion = declaration.recursion;
  if (recursion === undefined) {
    if (callsSelf(declaration)) {
      throw new TypeError(`${declaration.name} calls itself without a structural recursion argument`);
    }
    return;
  }
  const parameter = declaration.parameters[recursion.argument];
  if (parameter === undefined || parameter.type.kind !== 'named') {
    throw new TypeError(`${declaration.name} recurses on a parameter that carries no inductive data`);
  }
  const recursiveType = parameter.type.name;
  const data = declarations.get(recursiveType);
  if (data === undefined || data.kind !== 'enum') {
    throw new TypeError(`${declaration.name} recurses on ${recursiveType}, which is not an inductive data type`);
  }
  const initial: RecursionSlot[] = declaration.parameters.map((_, index) =>
    index === recursion.argument ? 'recursive' : 'other',
  );
  initial.reverse();
  const visit = (expression: LeanExpression, scope: readonly RecursionSlot[]): void => {
    switch (expression.kind) {
      case 'call': {
        if (expression.function === declaration.name) {
          const decreasing = expression.arguments[recursion.argument];
          if (decreasing === undefined || decreasing.kind !== 'variable' || scope[decreasing.index] !== 'smaller') {
            throw new TypeError(
              `${declaration.name} recurses on a value that is not a constructor field of its ${recursiveType} argument`,
            );
          }
        }
        expression.arguments.forEach((argument) => visit(argument, scope));
        return;
      }
      case 'match': {
        visit(expression.scrutinee, scope);
        const scrutinee = expression.scrutinee;
        const decides =
          expression.type === recursiveType &&
          scrutinee.kind === 'variable' &&
          (scope[scrutinee.index] === 'recursive' || scope[scrutinee.index] === 'smaller');
        const enumeration = declarations.get(expression.type);
        expression.cases.forEach((entry, index) => {
          const constructor =
            enumeration !== undefined && enumeration.kind === 'enum' ? enumeration.constructors[index] : undefined;
          const fields = constructor?.fields ?? [];
          const bindings: RecursionSlot[] = fields.map((field) =>
            decides && field.type.kind === 'named' && field.type.name === recursiveType ? 'smaller' : 'other',
          );
          bindings.reverse();
          visit(entry.value, [...bindings, ...scope]);
        });
        return;
      }
      case 'let':
        visit(expression.value, scope);
        visit(expression.body, ['other', ...scope]);
        return;
      case 'field':
        visit(expression.target, scope);
        return;
      case 'if':
        visit(expression.condition, scope);
        visit(expression.consequent, scope);
        visit(expression.alternate, scope);
        return;
      case 'equals':
      case 'and':
      case 'or':
        visit(expression.left, scope);
        visit(expression.right, scope);
        return;
      case 'not':
        visit(expression.operand, scope);
        return;
      case 'some':
        visit(expression.value, scope);
        return;
      case 'record':
        expression.fields.forEach((field) => visit(field.value, scope));
        return;
      case 'variant':
        expression.arguments.forEach((argument) => visit(argument, scope));
        return;
      case 'variable':
      case 'boolean':
      case 'none':
        return;
    }
  };
  visit(declaration.body, initial);
  if (!callsSelf(declaration)) {
    throw new TypeError(`${declaration.name} declares a structural recursion argument but never recurses`);
  }
}

function callsSelf(declaration: Extract<LeanDeclaration, { kind: 'function' }>): boolean {
  let found = false;
  const visit = (expression: LeanExpression): void => {
    switch (expression.kind) {
      case 'call':
        if (expression.function === declaration.name) found = true;
        expression.arguments.forEach(visit);
        return;
      case 'match':
        visit(expression.scrutinee);
        expression.cases.forEach((entry) => visit(entry.value));
        return;
      case 'let':
        visit(expression.value);
        visit(expression.body);
        return;
      case 'field':
        visit(expression.target);
        return;
      case 'if':
        visit(expression.condition);
        visit(expression.consequent);
        visit(expression.alternate);
        return;
      case 'equals':
      case 'and':
      case 'or':
        visit(expression.left);
        visit(expression.right);
        return;
      case 'not':
        visit(expression.operand);
        return;
      case 'some':
        visit(expression.value);
        return;
      case 'record':
        expression.fields.forEach((field) => visit(field.value));
        return;
      case 'variant':
        expression.arguments.forEach(visit);
        return;
      case 'variable':
      case 'boolean':
      case 'none':
        return;
    }
  };
  visit(declaration.body);
  return found;
}

function sameType(left: LeanType, right: LeanType): boolean {
  if (left.kind !== right.kind) return false;
  switch (left.kind) {
    case 'boolean':
      return true;
    case 'named':
      return right.kind === 'named' && left.name === right.name;
    case 'option':
      return right.kind === 'option' && sameType(left.inner, right.inner);
  }
}

function renderType(type: LeanType): string {
  switch (type.kind) {
    case 'boolean':
      return 'Bool';
    case 'named':
      return type.name;
    case 'option':
      return `Option (${renderType(type.inner)})`;
  }
}

function decodeDeclaration(value: unknown, location: string): LeanDeclaration {
  const declaration = object(value, location);
  const kind = string(declaration['kind'], `${location}.kind`);
  const name = qualifiedName(declaration['name'], `${location}.name`);
  const module = moduleName(declaration['module'], `${location}.module`);
  const span = decodeSpan(declaration['span'], `${location}.span`);
  switch (kind) {
    case 'enum': {
      exactKeys(declaration, ['kind', 'name', 'module', 'span', 'constructors'], location, ['doc']);
      const constructors = array(declaration['constructors'], `${location}.constructors`).map(
        (constructor, index): LeanEnumConstructor => {
          const constructorLocation = `${location}.constructors[${index}]`;
          const decoded = object(constructor, constructorLocation);
          exactKeys(decoded, ['name', 'fields'], constructorLocation, ['doc']);
          return {
            name: identifier(decoded['name'], `${constructorLocation}.name`),
            fields: decodeFields(decoded['fields'], constructorLocation),
            ...documentation(decoded, constructorLocation),
          };
        },
      );
      if (constructors.length === 0) throw new TypeError(`${location} has no constructors`);
      requireUnique(
        constructors.map((constructor) => constructor.name),
        `${location}.constructors`,
      );
      return { kind, name, module, span, constructors, ...documentation(declaration, location) };
    }
    case 'record': {
      exactKeys(declaration, ['kind', 'name', 'module', 'span', 'fields'], location, ['doc']);
      return {
        kind,
        name,
        module,
        span,
        fields: decodeFields(declaration['fields'], location),
        ...documentation(declaration, location),
      };
    }
    case 'function': {
      exactKeys(declaration, ['kind', 'name', 'module', 'span', 'parameters', 'result', 'body'], location, [
        'doc',
        'recursion',
      ]);
      const parameters = array(declaration['parameters'], `${location}.parameters`).map((parameter, index) => {
        const decoded = object(parameter, `${location}.parameters[${index}]`);
        exactKeys(decoded, ['name', 'type'], `${location}.parameters[${index}]`);
        return {
          name: string(decoded['name'], `${location}.parameters[${index}].name`),
          type: decodeType(decoded['type'], `${location}.parameters[${index}].type`),
        };
      });
      return {
        kind,
        name,
        module,
        span,
        parameters,
        result: decodeType(declaration['result'], `${location}.result`),
        ...decodeRecursion(declaration, parameters.length, location),
        body: decodeExpression(declaration['body'], `${location}.body`),
        ...documentation(declaration, location),
      };
    }
    default:
      throw new TypeError(`${location}.kind is unsupported: ${kind}`);
  }
}

function decodeSpan(value: unknown, location: string): LeanSpan {
  const span = object(value, location);
  exactKeys(span, ['startLine', 'startColumn', 'endLine', 'endColumn'], location);
  const decoded = {
    startLine: line(span['startLine'], `${location}.startLine`),
    startColumn: column(span['startColumn'], `${location}.startColumn`),
    endLine: line(span['endLine'], `${location}.endLine`),
    endColumn: column(span['endColumn'], `${location}.endColumn`),
  };
  if (
    decoded.endLine < decoded.startLine ||
    (decoded.endLine === decoded.startLine && decoded.endColumn < decoded.startColumn)
  ) {
    throw new TypeError(`${location} ends before it starts`);
  }
  return decoded;
}

function line(value: unknown, location: string): number {
  if (!Number.isSafeInteger(value) || Number(value) < 1) throw new TypeError(`${location} must be a 1-based line`);
  return Number(value);
}

function column(value: unknown, location: string): number {
  if (!Number.isSafeInteger(value) || Number(value) < 0) throw new TypeError(`${location} must be a column offset`);
  return Number(value);
}

function decodeRecursion(
  declaration: Record<string, unknown>,
  parameterCount: number,
  location: string,
): { readonly recursion?: { readonly argument: number } } {
  if (!Object.hasOwn(declaration, 'recursion')) return {};
  const recursion = object(declaration['recursion'], `${location}.recursion`);
  exactKeys(recursion, ['argument'], `${location}.recursion`);
  const argument = recursion['argument'];
  if (!Number.isSafeInteger(argument) || Number(argument) < 0 || Number(argument) >= parameterCount) {
    throw new TypeError(`${location}.recursion.argument is not one of the declared parameters`);
  }
  return { recursion: { argument: Number(argument) } };
}

function decodeFields(value: unknown, location: string): readonly LeanField[] {
  const fields = array(value, `${location}.fields`).map((field, index) => {
    const fieldLocation = `${location}.fields[${index}]`;
    const decoded = object(field, fieldLocation);
    exactKeys(decoded, ['name', 'type'], fieldLocation, ['doc']);
    return {
      name: identifier(decoded['name'], `${fieldLocation}.name`),
      type: decodeType(decoded['type'], `${fieldLocation}.type`),
      ...documentation(decoded, fieldLocation),
    };
  });
  requireUnique(
    fields.map((field) => field.name),
    `${location}.fields`,
  );
  return fields;
}

function decodeType(value: unknown, location: string): LeanType {
  const type = object(value, location);
  const kind = string(type['kind'], `${location}.kind`);
  switch (kind) {
    case 'boolean':
      exactKeys(type, ['kind'], location);
      return { kind };
    case 'named':
      exactKeys(type, ['kind', 'name'], location);
      return { kind, name: qualifiedName(type['name'], `${location}.name`) };
    case 'option': {
      exactKeys(type, ['kind', 'inner'], location);
      const inner = decodeType(type['inner'], `${location}.inner`);
      if (inner.kind === 'option') {
        throw new TypeError(`${location} is a nested Option, which collapses under the v1 representation`);
      }
      return { kind, inner };
    }
    default:
      throw new TypeError(`${location}.kind is unsupported: ${kind}`);
  }
}

function decodeExpression(value: unknown, location: string): LeanExpression {
  const expression = object(value, location);
  const kind = string(expression['kind'], `${location}.kind`);
  switch (kind) {
    case 'variable': {
      exactKeys(expression, ['kind', 'index'], location);
      const index = expression['index'];
      if (!Number.isSafeInteger(index) || Number(index) < 0) {
        throw new TypeError(`${location}.index must be a nonnegative safe integer`);
      }
      return { kind, index: Number(index) };
    }
    case 'boolean':
      exactKeys(expression, ['kind', 'value'], location);
      if (typeof expression['value'] !== 'boolean') {
        throw new TypeError(`${location}.value must be boolean`);
      }
      return { kind, value: expression['value'] };
    case 'let':
      exactKeys(expression, ['kind', 'name', 'value', 'body'], location);
      return {
        kind,
        name: string(expression['name'], `${location}.name`),
        value: decodeExpression(expression['value'], `${location}.value`),
        body: decodeExpression(expression['body'], `${location}.body`),
      };
    case 'field':
      exactKeys(expression, ['kind', 'target', 'field'], location);
      return {
        kind,
        target: decodeExpression(expression['target'], `${location}.target`),
        field: identifier(expression['field'], `${location}.field`),
      };
    case 'if':
      exactKeys(expression, ['kind', 'condition', 'consequent', 'alternate'], location);
      return {
        kind,
        condition: decodeExpression(expression['condition'], `${location}.condition`),
        consequent: decodeExpression(expression['consequent'], `${location}.consequent`),
        alternate: decodeExpression(expression['alternate'], `${location}.alternate`),
      };
    case 'equals':
    case 'and':
    case 'or':
      exactKeys(expression, ['kind', 'left', 'right'], location);
      return {
        kind,
        left: decodeExpression(expression['left'], `${location}.left`),
        right: decodeExpression(expression['right'], `${location}.right`),
      };
    case 'not':
      exactKeys(expression, ['kind', 'operand'], location);
      return { kind, operand: decodeExpression(expression['operand'], `${location}.operand`) };
    case 'some':
      exactKeys(expression, ['kind', 'value'], location);
      return { kind, value: decodeExpression(expression['value'], `${location}.value`) };
    case 'none':
      exactKeys(expression, ['kind'], location);
      return { kind };
    case 'variant':
      exactKeys(expression, ['kind', 'type', 'name', 'arguments'], location);
      return {
        kind,
        type: qualifiedName(expression['type'], `${location}.type`),
        name: identifier(expression['name'], `${location}.name`),
        arguments: array(expression['arguments'], `${location}.arguments`).map((argument, index) =>
          decodeExpression(argument, `${location}.arguments[${index}]`),
        ),
      };
    case 'record': {
      exactKeys(expression, ['kind', 'type', 'fields'], location);
      const fields = array(expression['fields'], `${location}.fields`).map((field, index) => {
        const decoded = object(field, `${location}.fields[${index}]`);
        exactKeys(decoded, ['name', 'value'], `${location}.fields[${index}]`);
        return {
          name: identifier(decoded['name'], `${location}.fields[${index}].name`),
          value: decodeExpression(decoded['value'], `${location}.fields[${index}].value`),
        };
      });
      requireUnique(
        fields.map((field) => field.name),
        `${location}.fields`,
      );
      return {
        kind,
        type: qualifiedName(expression['type'], `${location}.type`),
        fields,
      };
    }
    case 'match': {
      exactKeys(expression, ['kind', 'type', 'scrutinee', 'cases'], location);
      const cases = array(expression['cases'], `${location}.cases`).map((entry, index) => {
        const decoded = object(entry, `${location}.cases[${index}]`);
        exactKeys(decoded, ['constructor', 'value'], `${location}.cases[${index}]`);
        return {
          constructor: identifier(decoded['constructor'], `${location}.cases[${index}].constructor`),
          value: decodeExpression(decoded['value'], `${location}.cases[${index}].value`),
        };
      });
      if (cases.length === 0) throw new TypeError(`${location} decides no constructor`);
      requireUnique(
        cases.map((entry) => entry.constructor),
        `${location}.cases`,
      );
      return {
        kind,
        type: qualifiedName(expression['type'], `${location}.type`),
        scrutinee: decodeExpression(expression['scrutinee'], `${location}.scrutinee`),
        cases,
      };
    }
    case 'call':
      exactKeys(expression, ['kind', 'function', 'arguments'], location);
      return {
        kind,
        function: qualifiedName(expression['function'], `${location}.function`),
        arguments: array(expression['arguments'], `${location}.arguments`).map((argument, index) =>
          decodeExpression(argument, `${location}.arguments[${index}]`),
        ),
      };
    default:
      throw new TypeError(`${location}.kind is unsupported: ${kind}`);
  }
}

function object(value: unknown, location: string): Record<string, unknown> {
  if (!isRecord(value)) {
    throw new TypeError(`${location} must be an object`);
  }
  return value;
}

function isRecord(value: unknown): value is Record<string, unknown> {
  return typeof value === 'object' && value !== null && !Array.isArray(value);
}

function array(value: unknown, location: string): readonly unknown[] {
  if (!Array.isArray(value)) throw new TypeError(`${location} must be an array`);
  return value;
}

function string(value: unknown, location: string): string {
  if (typeof value !== 'string' || value.length === 0) {
    throw new TypeError(`${location} must be a nonempty string`);
  }
  return value;
}

function identifier(value: unknown, location: string): string {
  const decoded = string(value, location);
  if (!/^[$A-Z_a-z][$\w]*$/u.test(decoded)) {
    throw new TypeError(`${location} is not a TypeScript-safe identifier: ${decoded}`);
  }
  return decoded;
}

function bindingIdentifier(value: unknown, location: string): string {
  const decoded = identifier(value, location);
  const scanner = ts.createScanner(ts.ScriptTarget.Latest, false, ts.LanguageVariant.Standard, decoded);
  const token = scanner.scan();
  if (token !== ts.SyntaxKind.Identifier || scanner.scan() !== ts.SyntaxKind.EndOfFileToken) {
    throw new TypeError(`${location} is not a safe TypeScript binding name: ${decoded}`);
  }
  if (decoded === 'arguments' || decoded === 'eval') {
    throw new TypeError(`${location} is not a safe TypeScript binding name: ${decoded}`);
  }
  return decoded;
}

function qualifiedName(value: unknown, location: string): string {
  const decoded = string(value, location);
  for (const [index, part] of decoded.split('.').entries()) {
    identifier(part, `${location} part ${index}`);
  }
  return decoded;
}

function moduleName(value: unknown, location: string): string {
  const decoded = string(value, location);
  if (!isLeanModuleName(decoded)) throw new TypeError(`${location} is not a Lean module name: ${decoded}`);
  return decoded;
}

function stringArray(value: unknown, location: string): readonly string[] {
  return array(value, location).map((item, index) => string(item, `${location}[${index}]`));
}

function exactKeys(
  value: Record<string, unknown>,
  required: readonly string[],
  location: string,
  optional: readonly string[] = [],
): void {
  const admitted = new Set([...required, ...optional]);
  const unexpected = Object.keys(value).some((key) => !admitted.has(key));
  const missing = required.some((key) => !Object.hasOwn(value, key));
  if (unexpected || missing) {
    const canonical = [...required].sort(compareCodePoints).join(', ');
    const admittedOptional = [...optional].sort(compareCodePoints).join(', ');
    const suffix = optional.length === 0 ? '' : ` with optional ${admittedOptional}`;
    throw new TypeError(`${location} fields must be exactly ${canonical}${suffix}`);
  }
}

function documentation(value: Record<string, unknown>, location: string): LeanDocumented {
  if (!Object.hasOwn(value, 'doc')) return {};
  const doc = string(value['doc'], `${location}.doc`);
  if (doc.length === 0) throw new TypeError(`${location}.doc must not be empty`);
  if (doc.includes('*/')) throw new TypeError(`${location}.doc must not close a block comment`);
  return { doc };
}

function requireUnique(values: readonly string[], location: string): void {
  if (new Set(values).size !== values.length) throw new TypeError(`${location} contains duplicates`);
}

function localName(name: string): string {
  const part = name.split('.').at(-1);
  if (part === undefined) throw new TypeError('empty Lean name');
  return part;
}
