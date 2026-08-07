export type JsonValue = null | boolean | number | string | JsonValue[] | { [key: string]: JsonValue };

const supportedSchemaKeywords = new Set([
  '$defs', '$id', '$ref', '$schema', 'additionalProperties', 'allOf', 'const', 'description', 'else', 'enum', 'if',
  'items', 'maxItems', 'maximum', 'minItems', 'minLength', 'maxLength', 'minimum', 'not', 'oneOf', 'pattern', 'properties', 'required',
  'then', 'title', 'type',
]);

export function isJsonObject(value: JsonValue | undefined): value is { [key: string]: JsonValue } {
  return typeof value === 'object' && value !== null && !Array.isArray(value);
}

function sameJson(left: JsonValue, right: JsonValue): boolean {
  return JSON.stringify(left) === JSON.stringify(right);
}

function resolveReference(rootSchema: JsonValue, reference: string): JsonValue | undefined {
  if (!reference.startsWith('#/')) return undefined;
  let current: JsonValue | undefined = rootSchema;
  for (const segment of reference.slice(2).split('/')) {
    if (!isJsonObject(current)) return undefined;
    current = current[segment.replaceAll('~1', '/').replaceAll('~0', '~')];
  }
  return current;
}

export function validateJsonSchema(
  value: JsonValue,
  currentSchema: JsonValue,
  rootSchema: JsonValue,
  path: string,
  errors: string[],
): void {
  if (!isJsonObject(currentSchema)) {
    errors.push(`${path}: schema node must be an object`);
    return;
  }
  for (const keyword of Object.keys(currentSchema)) {
    if (!supportedSchemaKeywords.has(keyword)) errors.push(`${path}: unsupported schema keyword ${keyword}`);
  }
  if (typeof currentSchema.$ref === 'string') {
    const referenced = resolveReference(rootSchema, currentSchema.$ref);
    if (referenced === undefined) errors.push(`${path}: unresolved schema reference ${currentSchema.$ref}`);
    else validateJsonSchema(value, referenced, rootSchema, path, errors);
  }
  if (Array.isArray(currentSchema.allOf)) {
    for (const branch of currentSchema.allOf) validateJsonSchema(value, branch, rootSchema, path, errors);
  }
  if (Array.isArray(currentSchema.oneOf)) {
    const matches = currentSchema.oneOf.filter((branch) => {
      const branchErrors: string[] = [];
      validateJsonSchema(value, branch, rootSchema, path, branchErrors);
      return branchErrors.length === 0;
    }).length;
    if (matches !== 1) errors.push(`${path}: expected exactly one matching schema, found ${matches}`);
  }
  if (currentSchema.if !== undefined) {
    const conditionErrors: string[] = [];
    validateJsonSchema(value, currentSchema.if, rootSchema, path, conditionErrors);
    const branch = conditionErrors.length === 0 ? currentSchema.then : currentSchema.else;
    if (branch !== undefined) validateJsonSchema(value, branch, rootSchema, path, errors);
  }
  if (currentSchema.not !== undefined) {
    const negatedErrors: string[] = [];
    validateJsonSchema(value, currentSchema.not, rootSchema, path, negatedErrors);
    if (negatedErrors.length === 0) errors.push(`${path}: must not match negated schema`);
  }

  const expectedType = currentSchema.type;
  if (typeof expectedType === 'string') {
    const matches = expectedType === 'object' ? isJsonObject(value)
      : expectedType === 'array' ? Array.isArray(value)
        : expectedType === 'string' ? typeof value === 'string'
          : expectedType === 'number' ? typeof value === 'number'
            : expectedType === 'integer' ? typeof value === 'number' && Number.isInteger(value)
              : expectedType === 'boolean' ? typeof value === 'boolean'
                : expectedType === 'null' ? value === null : false;
    if (!matches) {
      errors.push(`${path}: expected ${expectedType}`);
      return;
    }
  }
  if (currentSchema.const !== undefined && !sameJson(value, currentSchema.const)) errors.push(`${path}: does not equal const value`);
  if (Array.isArray(currentSchema.enum) && !currentSchema.enum.some((candidate) => sameJson(value, candidate))) {
    errors.push(`${path}: is not an allowed enum value`);
  }
  if (typeof value === 'number' && typeof currentSchema.minimum === 'number' && value < currentSchema.minimum) {
    errors.push(`${path}: is below minimum ${currentSchema.minimum}`);
  }
  if (typeof value === 'number' && typeof currentSchema.maximum === 'number' && value > currentSchema.maximum) {
    errors.push(`${path}: is above maximum ${currentSchema.maximum}`);
  }
  if (typeof value === 'string') {
    if (typeof currentSchema.minLength === 'number' && value.length < currentSchema.minLength) errors.push(`${path}: is too short`);
    if (typeof currentSchema.maxLength === 'number' && value.length > currentSchema.maxLength) errors.push(`${path}: is too long`);
    if (typeof currentSchema.pattern === 'string' && !new RegExp(currentSchema.pattern, 'u').test(value)) {
      errors.push(`${path}: does not match ${currentSchema.pattern}`);
    }
  }
  if (Array.isArray(value)) {
    if (typeof currentSchema.minItems === 'number' && value.length < currentSchema.minItems) errors.push(`${path}: has too few items`);
    if (typeof currentSchema.maxItems === 'number' && value.length > currentSchema.maxItems) errors.push(`${path}: has too many items`);
    if (currentSchema.items !== undefined) {
      value.forEach((item, index) => validateJsonSchema(item, currentSchema.items, rootSchema, `${path}[${index}]`, errors));
    }
  }
  if (isJsonObject(value)) {
    if (Array.isArray(currentSchema.required)) {
      for (const field of currentSchema.required) {
        if (typeof field === 'string' && !Object.hasOwn(value, field)) errors.push(`${path}: missing ${field}`);
      }
    }
    if (isJsonObject(currentSchema.properties)) {
      for (const [field, fieldValue] of Object.entries(value)) {
        const fieldSchema = currentSchema.properties[field];
        if (fieldSchema !== undefined) validateJsonSchema(fieldValue, fieldSchema, rootSchema, `${path}.${field}`, errors);
        else if (currentSchema.additionalProperties === false) errors.push(`${path}.${field}: additional property is not allowed`);
      }
    }
  }
}
