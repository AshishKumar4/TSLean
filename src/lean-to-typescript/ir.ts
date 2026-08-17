import ts from 'typescript';
import { compareCodePoints } from './ordering.js';

export const LEAN_TO_TYPESCRIPT_SCHEMA_VERSION = 1;
export const LEAN_TO_TYPESCRIPT_FRAGMENT_VERSION = 'tslean-pure-first-order-v2';

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
  | { readonly kind: 'variant'; readonly type: string; readonly name: string }
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

export interface LeanEnumConstructor extends LeanDocumented {
  readonly name: string;
}

export type LeanDeclaration =
  | ({
      readonly kind: 'enum';
      readonly name: string;
      readonly constructors: readonly LeanEnumConstructor[];
    } & LeanDocumented)
  | ({
      readonly kind: 'record';
      readonly name: string;
      readonly fields: readonly ({ readonly name: string; readonly type: LeanType } & LeanDocumented)[];
    } & LeanDocumented)
  | ({
      readonly kind: 'function';
      readonly name: string;
      readonly parameters: readonly { readonly name: string; readonly type: LeanType }[];
      readonly result: LeanType;
      readonly body: LeanExpression;
    } & LeanDocumented);

export interface LeanSemanticProgram {
  readonly schemaVersion: 1;
  readonly fragmentVersion: typeof LEAN_TO_TYPESCRIPT_FRAGMENT_VERSION;
  readonly roots: readonly string[];
  readonly declarations: readonly LeanDeclaration[];
}

export function decodeLeanSemanticProgram(value: unknown): LeanSemanticProgram {
  const program = object(value, 'semantic program');
  exactKeys(program, ['schemaVersion', 'fragmentVersion', 'roots', 'declarations'], 'semantic program');
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
  const decoded: LeanSemanticProgram = {
    schemaVersion: LEAN_TO_TYPESCRIPT_SCHEMA_VERSION,
    fragmentVersion: LEAN_TO_TYPESCRIPT_FRAGMENT_VERSION,
    roots,
    declarations,
  };
  validateProgramReferences(decoded);
  return decoded;
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
  requireUnique(
    program.declarations.map((declaration) => localName(declaration.name)),
    'TypeScript declaration names',
  );
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
        if (!declaration.constructors.some((candidate) => candidate.name === expression.name)) {
          throw new TypeError(`${location} references unknown constructor ${expression.type}.${expression.name}`);
        }
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
        if (expected !== undefined) {
          expression.cases.forEach((entry, index) =>
            checkExpression(entry.value, scope, expected, `${location}.cases[${index}].value`),
          );
          return expected;
        }
        const [first, ...rest] = expression.cases;
        if (first === undefined) throw new TypeError(`${location} decides no constructor`);
        const result = checkExpression(first.value, scope, undefined, `${location}.cases[0].value`);
        rest.forEach((entry, index) =>
          checkExpression(entry.value, scope, result, `${location}.cases[${index + 1}].value`),
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
    if (declaration.kind === 'record') {
      declaration.fields.forEach((field, index) =>
        validateType(field.type, `${declaration.name}.fields[${index}].type`),
      );
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
  switch (kind) {
    case 'enum': {
      exactKeys(declaration, ['kind', 'name', 'constructors'], location, ['doc']);
      const constructors = array(declaration['constructors'], `${location}.constructors`).map(
        (constructor, index): LeanEnumConstructor => {
          const decoded = object(constructor, `${location}.constructors[${index}]`);
          exactKeys(decoded, ['name'], `${location}.constructors[${index}]`, ['doc']);
          return {
            name: identifier(decoded['name'], `${location}.constructors[${index}].name`),
            ...documentation(decoded, `${location}.constructors[${index}]`),
          };
        },
      );
      if (constructors.length === 0) throw new TypeError(`${location} has no constructors`);
      requireUnique(
        constructors.map((constructor) => constructor.name),
        `${location}.constructors`,
      );
      return { kind, name, constructors, ...documentation(declaration, location) };
    }
    case 'record': {
      exactKeys(declaration, ['kind', 'name', 'fields'], location, ['doc']);
      const fields = array(declaration['fields'], `${location}.fields`).map((field, index) => {
        const decoded = object(field, `${location}.fields[${index}]`);
        exactKeys(decoded, ['name', 'type'], `${location}.fields[${index}]`, ['doc']);
        return {
          name: identifier(decoded['name'], `${location}.fields[${index}].name`),
          type: decodeType(decoded['type'], `${location}.fields[${index}].type`),
          ...documentation(decoded, `${location}.fields[${index}]`),
        };
      });
      requireUnique(
        fields.map((field) => field.name),
        `${location}.fields`,
      );
      return { kind, name, fields, ...documentation(declaration, location) };
    }
    case 'function': {
      exactKeys(declaration, ['kind', 'name', 'parameters', 'result', 'body'], location, ['doc']);
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
        parameters,
        result: decodeType(declaration['result'], `${location}.result`),
        body: decodeExpression(declaration['body'], `${location}.body`),
        ...documentation(declaration, location),
      };
    }
    default:
      throw new TypeError(`${location}.kind is unsupported: ${kind}`);
  }
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
      exactKeys(expression, ['kind', 'type', 'name'], location);
      return {
        kind,
        type: qualifiedName(expression['type'], `${location}.type`),
        name: identifier(expression['name'], `${location}.name`),
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
