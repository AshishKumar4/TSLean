// Structured error reporting for the TSLean transpiler.
// Every diagnostic has a code, location, message, explanation, and optional suggestion.

// ─── Error codes ────────────────────────────────────────────────────────────────

export enum ErrorCode {
  // Parser errors (TSL001–TSL099)
  PARSE_UNKNOWN_NODE       = 'TSL001',
  PARSE_UNSUPPORTED_SYNTAX = 'TSL002',
  PARSE_MISSING_TYPE       = 'TSL003',
  PARSE_CYCLE_DETECTED     = 'TSL004',
  PARSE_INVALID_IMPORT     = 'TSL005',

  // Type errors (TSL100–TSL199)
  TYPE_UNRESOLVED          = 'TSL100',
  TYPE_INEXPRESSIBLE       = 'TSL101',
  TYPE_CONSTRAINT_LOST     = 'TSL102',
  TYPE_INTERSECTION_ERASED = 'TSL103',

  // Lowering errors (TSL200–TSL299)
  LOWER_SORRY_EMITTED      = 'TSL200',
  LOWER_TYPEOF_INSTANCEOF  = 'TSL201',
  LOWER_RUNTIME_API        = 'TSL202',
  LOWER_MUTATION_PATTERN   = 'TSL203',
  LOWER_GENERATOR          = 'TSL204',
  LOWER_INDUCTIVE_FIELD    = 'TSL205',

  // Project errors (TSL300–TSL399)
  PROJECT_FILE_NOT_FOUND   = 'TSL300',
  PROJECT_CIRCULAR_IMPORT  = 'TSL301',
  PROJECT_TSCONFIG_INVALID = 'TSL302',

  // Lean build errors (TSL400–TSL499)
  LEAN_BUILD_FAILED        = 'TSL400',
  LEAN_TYPE_MISMATCH       = 'TSL401',
}

// ─── Diagnostic ─────────────────────────────────────────────────────────────────

export interface SourceLocation {
  file: string;
  line: number;
  col: number;
}

export interface Diagnostic {
  code: ErrorCode;
  severity: 'error' | 'warning' | 'info';
  location?: SourceLocation;
  message: string;
  explanation?: string;
  suggestion?: string;
  sourceContext?: string;  // 3-line source window around the error
}

// ─── Diagnostic creation ────────────────────────────────────────────────────────

const EXPLANATIONS: Partial<Record<ErrorCode, string>> = {
  [ErrorCode.PARSE_UNKNOWN_NODE]: 'The parser encountered a TypeScript AST node it cannot translate to the IR.',
  [ErrorCode.TYPE_INEXPRESSIBLE]: 'This TypeScript type uses features (conditional types, mapped types, infer) that have no Lean 4 equivalent.',
  [ErrorCode.LOWER_SORRY_EMITTED]: 'The lowerer could not produce valid Lean for this expression and emitted sorry.',
  [ErrorCode.LOWER_TYPEOF_INSTANCEOF]: 'typeof and instanceof are runtime type checks with no Lean equivalent. Use pattern matching or type class dispatch.',
  [ErrorCode.LOWER_RUNTIME_API]: 'This calls a JS/Node runtime API that is not mapped to a Lean stub.',
  [ErrorCode.LOWER_GENERATOR]: 'Generators (function*/yield) are not expressible in pure Lean 4.',
  [ErrorCode.PROJECT_CIRCULAR_IMPORT]: 'Lean does not support circular imports. Extract shared types to break the cycle.',
};

const SUGGESTIONS: Partial<Record<ErrorCode, string>> = {
  [ErrorCode.PARSE_UNKNOWN_NODE]: 'File an issue or add a handler in src/parser/index.ts.',
  [ErrorCode.TYPE_INEXPRESSIBLE]: 'Use a concrete type alias or simplify the generic pattern.',
  [ErrorCode.LOWER_TYPEOF_INSTANCEOF]: 'Replace with discriminated union checks (e.g., tag field).',
  [ErrorCode.LOWER_RUNTIME_API]: 'Add a mapping to the stubMap in src/codegen/lower.ts.',
  [ErrorCode.LOWER_GENERATOR]: 'Refactor to use arrays or iterators.',
  [ErrorCode.PROJECT_CIRCULAR_IMPORT]: 'Move shared types/interfaces to a separate file.',
};

export function createDiagnostic(
  code: ErrorCode,
  message: string,
  opts: { location?: SourceLocation; severity?: 'error' | 'warning' | 'info'; suggestion?: string; sourceText?: string } = {},
): Diagnostic {
  const loc = opts.location;
  let sourceContext: string | undefined;
  if (loc && opts.sourceText) {
    sourceContext = extractSourceContext(opts.sourceText, loc.line);
  }
  return {
    code,
    severity: opts.severity ?? 'error',
    location: loc,
    message,
    explanation: EXPLANATIONS[code],
    suggestion: opts.suggestion ?? SUGGESTIONS[code],
    sourceContext,
  };
}

// ─── Formatting ─────────────────────────────────────────────────────────────────

export function formatDiagnostic(d: Diagnostic, color = true): string {
  const c = color ? {
    red: (s: string) => `\x1b[31m${s}\x1b[0m`,
    yellow: (s: string) => `\x1b[33m${s}\x1b[0m`,
    cyan: (s: string) => `\x1b[36m${s}\x1b[0m`,
    dim: (s: string) => `\x1b[2m${s}\x1b[0m`,
    bold: (s: string) => `\x1b[1m${s}\x1b[0m`,
  } : { red: (s: string) => s, yellow: (s: string) => s, cyan: (s: string) => s, dim: (s: string) => s, bold: (s: string) => s };

  const sevColor = d.severity === 'error' ? c.red : d.severity === 'warning' ? c.yellow : c.cyan;
  const lines: string[] = [];

  // Location + severity + code
  const loc = d.location ? `${d.location.file}:${d.location.line}:${d.location.col}` : '';
  lines.push(`${loc ? loc + ' ' : ''}${sevColor(d.severity)} ${c.dim(d.code)}: ${d.message}`);

  // Source context
  if (d.sourceContext) {
    lines.push('');
    for (const line of d.sourceContext.split('\n')) {
      lines.push(`  ${c.dim(line)}`);
    }
  }

  // Explanation
  if (d.explanation) {
    lines.push(`  ${c.dim('explanation:')} ${d.explanation}`);
  }

  // Suggestion
  if (d.suggestion) {
    lines.push(`  ${c.cyan('suggestion:')} ${d.suggestion}`);
  }

  return lines.join('\n');
}

function extractSourceContext(sourceText: string, line: number): string {
  const lines = sourceText.split('\n');
  const start = Math.max(0, line - 2);
  const end = Math.min(lines.length, line + 1);
  return lines.slice(start, end).map((l, i) => {
    const lineNum = start + i + 1;
    const marker = lineNum === line ? '>' : ' ';
    return `${marker} ${String(lineNum).padStart(4)} | ${l}`;
  }).join('\n');
}

// ─── Diagnostic collector ───────────────────────────────────────────────────────

export class DiagnosticCollector {
  private diagnostics: Diagnostic[] = [];

  add(d: Diagnostic): void { this.diagnostics.push(d); }

  get all(): readonly Diagnostic[] { return this.diagnostics; }
  get errors(): Diagnostic[] { return this.diagnostics.filter(d => d.severity === 'error'); }
  get warnings(): Diagnostic[] { return this.diagnostics.filter(d => d.severity === 'warning'); }
  get count(): number { return this.diagnostics.length; }

  formatAll(color = true): string {
    return this.diagnostics.map(d => formatDiagnostic(d, color)).join('\n\n');
  }

  summary(): string {
    const e = this.errors.length;
    const w = this.warnings.length;
    const parts: string[] = [];
    if (e > 0) parts.push(`${e} error(s)`);
    if (w > 0) parts.push(`${w} warning(s)`);
    return parts.join(', ') || 'no issues';
  }
}
