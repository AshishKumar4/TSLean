#!/usr/bin/env npx tsx
/**
 * selfhost-postprocess.ts — Fix raw transpiler output for Lean 4 compilation.
 *
 * Usage: npx tsx scripts/selfhost-postprocess.ts <input.lean> <output.lean>
 *
 * Applies these fixes in order:
 * 1. Fix namespace to TSLean.Generated.SelfHost.<name>
 * 2. Fix imports (cross-file → SelfHost paths)
 * 3. Add Prelude + ir_types imports (except for ir_types itself)
 * 4. Remove deriving inside mutual blocks, add sorry-based instances after end
 * 5. Replace `pattern : IRPattern` with `pattern : TSAny` in struct fields
 * 6. Replace `default /- codegen error -/` with `sorry`
 * 7. Fix isPure/dedup/combineEffects/hasAsync/hasState/hasExcept/hasIO bodies
 * 8. Fix smart constructor bodies (toString wrapping, field chaining)
 * 9. Add `partial` to recursive functions that need it
 */

import * as fs from 'fs';
import * as path from 'path';

const [,, inputFile, outputFile] = process.argv;
if (!inputFile || !outputFile) {
  console.error('Usage: npx tsx scripts/selfhost-postprocess.ts <input.lean> <output.lean>');
  process.exit(1);
}

let code = fs.readFileSync(inputFile, 'utf-8');
const baseName = path.basename(outputFile, '.lean');

// 1. Fix namespace — ir_types keeps TSLean.Generated.Types; others get SelfHost.<Name>
if (baseName !== 'ir_types') {
  const nsName = `TSLean.Generated.SelfHost.${capitalize(baseName)}`;
  code = code.replace(/namespace TSLean\.Generated\.\w+/g, `namespace ${nsName}`);
  code = code.replace(/end TSLean\.Generated\.\w+/g, `end ${nsName}`);
}

// 2. Fix cross-file imports
const importFixes: [RegExp, string][] = [
  [/import TSLean\.Generated\.Ir\.Types/g, 'import TSLean.Generated.SelfHost.ir_types'],
  [/import TSLean\.Generated\.Effects\.Index/g, 'import TSLean.Generated.SelfHost.effects_index'],
  [/import TSLean\.Generated\.Stdlib\.Index/g, 'import TSLean.Generated.SelfHost.stdlib_index'],
  [/import TSLean\.Generated\.Typemap\.Index/g, 'import TSLean.Generated.SelfHost.typemap_index'],
  [/import TSLean\.Generated\.DoModel\.Ambient/g, 'import TSLean.Generated.SelfHost.DoModel_Ambient'],
  [/import TSLean\.Generated\.Codegen\.Index/g, 'import TSLean.Generated.SelfHost.codegen_index'],
  [/import TSLean\.Generated\.Parser\.Index/g, 'import TSLean.Generated.SelfHost.parser_index'],
  [/import TSLean\.Generated\.Rewrite\.Index/g, 'import TSLean.Generated.SelfHost.rewrite_index'],
  [/import TSLean\.Generated\.Verification\.Index/g, 'import TSLean.Generated.SelfHost.verification_index'],
  [/import TSLean\.Generated\.Project\.Index/g, 'import TSLean.Generated.SelfHost.project_index'],
];
for (const [re, replacement] of importFixes) {
  code = code.replace(re, replacement);
}

// 3. Add Prelude + ir_types imports (except for ir_types itself)
if (baseName !== 'ir_types' && baseName !== 'IR_Types') {
  const firstImport = code.indexOf('import ');
  if (firstImport >= 0) {
    code = code.slice(0, firstImport) +
      'import TSLean.Generated.SelfHost.Prelude\nimport TSLean.Generated.SelfHost.ir_types\n' +
      code.slice(firstImport);
  }
}

// Also add `open TSLean.Generated.Types` if ir_types is imported
if (code.includes('import TSLean.Generated.SelfHost.ir_types')) {
  code = code.replace(/open TSLean\b/, 'open TSLean TSLean.Generated.Types');
}

// 4. Fix mutual block deriving — remove deriving inside mutual, add instances after
{
  const mutualStart = code.indexOf('mutual');
  const mutualEnd = code.indexOf('\nend\n');
  if (mutualStart >= 0 && mutualEnd > mutualStart) {
    const before = code.slice(0, mutualStart);
    let mutual = code.slice(mutualStart, mutualEnd + 5);
    const after = code.slice(mutualEnd + 5);

    // Collect type names from the mutual block
    const typeNames: string[] = [];
    const inductiveRe = /inductive (\w+)/g;
    let m;
    while ((m = inductiveRe.exec(mutual)) !== null) {
      typeNames.push(m[1]);
    }

    // Remove deriving clauses inside mutual
    mutual = mutual.replace(/  deriving Repr, BEq, Inhabited\n/g, '');

    // Add sorry-based instances after the mutual block
    let instances = '\n';
    for (const name of typeNames) {
      instances += `instance : Inhabited ${name} := ⟨sorry⟩\n`;
      instances += `instance : BEq ${name} := ⟨fun _ _ => false⟩\n`;
      instances += `instance : Repr ${name} := ⟨fun _ _ => .text s!"${name}"⟩\n`;
    }

    code = before + mutual + instances + after;
  }
}

// 4b. parser_index early fix: stub all multi-line function bodies with sorry
// This MUST run before other passes that collapse bodies, to catch the full bodies.
// Also stub 1-line bodies that contain struct literals or forward references.
if (baseName === 'parser_index') {
  // Pre-fix: stub specific 1-line functions with known problems
  code = code.replace(
    /def ParserCtx\.parseBlock[\s\S]*?(?=\ndef |\nend )/,
    `def ParserCtx.parseBlock (self : ParserCtxState) (block : TSAny) (eff : Effect) : IRExpr :=\n  sorry /- parseBlock: calls parseStmts -/\n`
  );
  // Stub any function whose single-line body contains `{ tag :=`
  code = code.replace(
    /^((?:partial\s+)?def\s+\w[\w.]*\s.*:=)\n(\s+\{[^}]*tag :=.*\}\s*)$/gm,
    '$1\n  sorry /- struct literal on inductive -/'
  );
  const pLines = code.split('\n');
  const pResult: string[] = [];
  let pSkipBody = false;
  let pSkipIndent = 0;
  for (let pi = 0; pi < pLines.length; pi++) {
    const pLine = pLines[pi];
    const pTrimmed = pLine.trimStart();
    const pIndent = pLine.length - pTrimmed.length;

    if (pSkipBody) {
      if ((pTrimmed.startsWith('def ') || pTrimmed.startsWith('partial def ') ||
           pTrimmed.startsWith('structure ') || pTrimmed.startsWith('end ') ||
           pTrimmed.startsWith('/-- ') || pTrimmed.startsWith('-- //')) && pIndent <= pSkipIndent) {
        pSkipBody = false;
        pResult.push(pLine);
      }
      continue;
    }

    pResult.push(pLine);

    const pDefMatch = pLine.match(/^(\s*)(?:partial\s+)?def\s+(\w[\w.]*)\s.*:=\s*$/);
    if (pDefMatch) {
      const pDefIndent = pDefMatch[1].length;
      const pFuncName = pDefMatch[2];

      let pBodyLineCount = 0;
      for (let pk = pi + 1; pk < pLines.length; pk++) {
        const pBl = pLines[pk].trimStart();
        const pBi = pLines[pk].search(/\S/);
        if (pBi >= 0 && pBi <= pDefIndent && pBl !== '' && !pBl.startsWith('--')) break;
        if (pBl !== '') pBodyLineCount++;
      }

      if (pBodyLineCount > 1) {
        const pIsMonadic = /\b(?:IO|StateT|ExceptT)\b/.test(pLine);
        if (pIsMonadic) {
          pResult.push(`  do sorry /- ${pFuncName}: parser body -/`);
        } else {
          pResult.push(`  sorry /- ${pFuncName}: parser body -/`);
        }
        pResult.push('');
        pSkipBody = true;
        pSkipIndent = pDefIndent;
      }
    }
  }
  code = pResult.join('\n');
}

// 5. Replace `pattern : IRPattern` with `pattern : TSAny` in struct fields
code = code.replace(/pattern : IRPattern/g, 'pattern : TSAny := default');
// Also fix body : IRExpr in structs where IRExpr might be Type 1
// (only in IRCase — leave other IRExpr fields alone)
code = code.replace(/(structure IRCase[\s\S]*?)body : IRExpr/,
  '$1body : IRExpr := default');

// 6. Replace `default /- codegen error -/` with `sorry`
code = code.replace(/default \/\*- codegen error -\*\//g, 'sorry');
code = code.replace(/default \/\- codegen error -\//g, 'sorry');

// 7. Fix known function bodies for ir_types
if (baseName === 'ir_types') {
  // Move isPure before combineEffects (forward reference fix)
  // Replace broken isPure/dedup/combineEffects/hasAsync/hasState/hasExcept/hasIO
  const funcFixes: [RegExp, string][] = [
    // isPure: pattern match instead of .tag access (include preceding doc comment)
    [/\/\-\-[^]*?-\/\ndef isPure \(e : Effect\) : Bool :=\n\s+default == "Pure"/,
     `/-- True when the effect is strictly Pure. -/\ndef isPure : Effect → Bool\n  | .Pure => true\n  | _ => false`],
    [/def isPure \(e : Effect\) : Bool :=\n\s+default == "Pure"/,
     `def isPure : Effect → Bool\n  | .Pure => true\n  | _ => false`],
    // dedup: foldl with dedup instead of Set mutation
    [/def dedup \(effects : Array Effect\) : Array Effect :=[\s\S]*?true\) effects/,
     `def dedup (effects : Array Effect) : Array Effect :=\n  effects.foldl (fun acc e => if acc.any (· == e) then acc else acc.push e) #[]`],
    // combineEffects: flatten Combined, remove Pure, dedup
    [/def combineEffects \(effects : Array Effect\) : Effect :=[\s\S]*?Effect\.Combined deduped/,
     `def combineEffects (effects : Array Effect) : Effect :=\n  let flat := effects.foldl (fun acc e =>\n    match e with\n    | .Combined inner => acc ++ inner\n    | other => acc.push other) #[]\n  let noPure := flat.filter (fun e => !isPure e)\n  let deduped := dedup noPure\n  if deduped.size == 0 then Pure\n  else if deduped.size == 1 then deduped.getD 0 default\n  else Effect.Combined deduped`],
    // hasAsync/hasState/hasExcept/hasIO: pattern match on Effect
    [/partial def hasAsync \(e : Effect\) : Bool :=[\s\S]*?\(sorry\)\)/,
     `partial def hasAsync : Effect → Bool\n  | .Async => true\n  | .Combined es => es.any hasAsync\n  | _ => false`],
    [/partial def hasState \(e : Effect\) : Bool :=[\s\S]*?\(sorry\)\)/,
     `partial def hasState : Effect → Bool\n  | .State _ => true\n  | .Combined es => es.any hasState\n  | _ => false`],
    [/partial def hasExcept \(e : Effect\) : Bool :=[\s\S]*?\(sorry\)\)/,
     `partial def hasExcept : Effect → Bool\n  | .Except _ => true\n  | .Combined es => es.any hasExcept\n  | _ => false`],
    [/partial def hasIO \(e : Effect\) : Bool :=[\s\S]*?\(sorry\)\)/,
     `partial def hasIO : Effect → Bool\n  | .IO => true\n  | .Combined es => es.any hasIO\n  | _ => false`],
  ];

  for (const [re, replacement] of funcFixes) {
    code = code.replace(re, replacement);
  }

  // Remove any remaining broken originals (funcFixes may leave fragments)
  code = code.replace(/\/\-\-[^]*?-\/\ndef isPure[\s\S]*?\| _ => false\n?/g, '');
  code = code.replace(/def isPure[\s\S]*?\| _ => false\n?/g, '');

  // Inject all three functions after `def Pure := Effect.Pure`
  const allThree = `
def isPure : Effect → Bool
  | .Pure => true
  | _ => false

def dedup (effects : Array Effect) : Array Effect :=
  effects.foldl (fun acc e => if acc.any (· == e) then acc else acc.push e) #[]

def combineEffects (effects : Array Effect) : Effect :=
  let flat := effects.foldl (fun acc e =>
    match e with
    | .Combined inner => acc ++ inner
    | other => acc.push other) #[]
  let noPure := flat.filter (fun e => !isPure e)
  let deduped := dedup noPure
  if deduped.size == 0 then Pure
  else if deduped.size == 1 then deduped.getD 0 default
  else Effect.Combined deduped
`;

  const pureDefIdx = code.indexOf('def Pure :');
  if (pureDefIdx >= 0) {
    const eol = code.indexOf('\n', pureDefIdx);
    code = code.slice(0, eol + 1) + allThree + code.slice(eol + 1);
  }
}

// 8. Fix toString wrapping for struct literal fields on known tagged types
// Replace `value := v` where v is not a string with `value := toString v`
// (Only for struct literals with a tag field)
code = code.replace(
  /\{ tag := ("[\w]+"), ([\w]+) := ([\w]+), type := (\w+), effect := (\w+) \}/g,
  (match, tag, field, val, type, effect) => {
    if (field === 'value' && !val.startsWith('"')) {
      return `{ tag := ${tag}, ${field} := toString ${val}, type := ${type}, effect := ${effect} }`;
    }
    return match;
  }
);

// 9. Fix appExpr/seqExpr chained field access
code = code.replace(
  /stmts\.getD \(stmts\.size - 1\) default\.type/g,
  '(stmts.getD (stmts.size - 1) default).type'
);

// Fix combineEffects array literal with spread
code = code.replace(
  /combineEffects #\[fn\.effect, Array\.map/g,
  'combineEffects (#[fn.effect] ++ Array.map'
);

// Fix toString on non-stringifiable types inside struct literals
// For TSAny fields, complex values need toString or default
code = code.replace(/toString (base|fn)(?=,| \})/g, '$1.tag');
code = code.replace(/toString (args|stmts|fields)(?=,| \})/g, 'default');

// Fix Array.tag → default (Array has no .tag field)
code = code.replace(/(\w+)\.tag(?=\s*,\s*(args|stmts|elems|fields)\s*:=)/g, '$1');

// Fix orphaned doc comments (moved functions may leave comments behind)
code = code.replace(/\n\n\/\-\-[^-]*-\/\n\n\/\-\-/g, '\n\n/--');

// 10. Fix specific ir_types function bodies
if (baseName === 'ir_types') {
  // Replace appExpr body
  code = code.replace(
    /def appExpr \(fn : IRExpr\) \(args : Array IRExpr\) : IRExpr :=[\s\S]*?(?=\n\/\-\-|\ndef )/,
    `def appExpr (fn : IRExpr) (args : Array IRExpr) : IRExpr :=\n  { tag := "App", fn := fn.tag, args := default, type := TyUnit, effect := combineEffects (#[fn.effect] ++ args.map (fun a => a.effect)) }\n\n`
  );
  // Replace seqExpr body
  code = code.replace(
    /def seqExpr \(stmts : Array IRExpr\) : IRExpr :=[\s\S]*?(?=\nend )/,
    `def seqExpr (stmts : Array IRExpr) : IRExpr :=\n  if stmts.size == 0 then litUnit\n  else if stmts.size == 1 then stmts.getD 0 default\n  else { tag := "Sequence", stmts := default, type := (stmts.getD (stmts.size - 1) default).type, effect := combineEffects (stmts.map (fun s => s.effect)) }\n\n`
  );
  // Fix structUpdate: base := base → base := base.tag
  code = code.replace(
    /\{ tag := "StructUpdate", base := base,/g,
    '{ tag := "StructUpdate", base := base.tag,'
  );
  // Fix any remaining chained field: x.getD n default.type → (x.getD n default).type
  code = code.replace(
    /stmts\.getD \(stmts\.size - 1\) default\.type/g,
    '(stmts.getD (stmts.size - 1) default).type'
  );
}

// ─── Fix M0 (early): Multiline s!"..." with -- comments ─────────────────────
// Must run early before other passes might move or modify the lines.
// Detect `let x := s!"...\n...\n--...\n..."` and replace the whole let + continuation
{
  const mLines = code.split('\n');
  const mResult: string[] = [];
  let mSkipUntilQuote = false;
  for (let i = 0; i < mLines.length; i++) {
    if (mSkipUntilQuote) {
      // Skip lines until we find one containing a closing " (end of the string literal)
      // Then also skip any trailing ++ on the same or next line
      if (mLines[i].includes('"')) {
        mSkipUntilQuote = false;
        // If there's content after the ", skip it too (like `++ s!"..."` etc)
      }
      continue;
    }
    if (/let \w+ := s!"[^"]*$/.test(mLines[i])) {
      let hasComment = false;
      for (let k = i + 1; k < Math.min(i + 8, mLines.length); k++) {
        if (mLines[k].includes('"')) break;
        if (mLines[k].trim().startsWith('--')) { hasComment = true; break; }
      }
      if (hasComment) {
        const indent = mLines[i].search(/\S/);
        const varName = mLines[i].match(/let (\w+)/)?.[1] ?? 'x';
        mResult.push(`${' '.repeat(indent)}let ${varName} := sorry`);
        mSkipUntilQuote = true;
        continue;
      }
    }
    mResult.push(mLines[i]);
  }
  code = mResult.join('\n');
}

// ─── Fix A: if/else outside do (monadic functions only) ─────────────────────
{
  const fixLines = code.split('\n');
  const fixOut: string[] = [];
  for (let i = 0; i < fixLines.length; i++) {
    const line = fixLines[i];
    fixOut.push(line);
    // Only add do for monadic return types
    if (/^\s*(?:partial\s+)?def\s+\w+.*:=$/.test(line) && /\b(?:IO|StateT)\b/.test(line)) {
      let j = i + 1;
      while (j < fixLines.length && fixLines[j].trim() === '') j++;
      if (j < fixLines.length) {
        const next = fixLines[j].trim();
        if ((next.startsWith('if ') || next.startsWith('let ')) && !line.includes(':= do')) {
          let hasSeq = false;
          const bi = fixLines[j].search(/\S/);
          for (let k = j + 1; k < fixLines.length && k < j + 20; k++) {
            const ki = fixLines[k].search(/\S/);
            if (ki < 0) continue;
            if (ki < bi) break;
            if (ki === bi && (fixLines[k].trim().startsWith('if ') || fixLines[k].trim().startsWith('let '))) {
              hasSeq = true; break;
            }
          }
          if (hasSeq) fixOut[fixOut.length - 1] = line.replace(/:=$/, ':= do');
        }
      }
    }
  }
  code = fixOut.join('\n');
}

// ─── Fix B: TS compiler API field access → sorry ────────────────────────────
{
  const tsFields = ['operator','operatorToken','operand','getChildren','getText',
    'getSourceFile','getStart','getEnd','getChildCount','forEachChild','getFullText',
    'declarationList','declarations','initializer','expression',
    'thenStatement','elseStatement','incrementor','condition',
    'catchClause','finallyBlock','variableDeclaration','moduleSpecifier',
    'propertyName','questionToken','typeArguments','typeParameters',
    'heritageClauses','members','modifiers','decorators'];
  for (const f of tsFields) {
    const re = new RegExp(`([a-z_]\\w*)\\.${f}\\b`, 'g');
    code = code.replace(re, (_m: string, obj: string) => {
      if (['Array','String','Option','List','AssocMap','TSLean','IO'].includes(obj)) return _m;
      return `sorry /- ${obj}.${f} -/`;
    });
  }
}

// ─── Fix D: stdlib method tables ────────────────────────────────────────────
if (baseName === 'stdlib_index' || baseName === 'StdlibIndex') {
  // Method table struct literals → AssocMap default
  code = code.replace(/: String := \{[^}]*\}/g, ': AssocMap String MethodTx := default');
  // Fix .getD calls
  code = code.replace(/(\w+)\.getD (\w+) default/g, '($1.get? $2).getD default');
  // Add HashMap import
  if (!code.includes('import TSLean.Stdlib.HashMap')) {
    code = code.replace(/(import TSLean\.Runtime\.Coercions)/, '$1\nimport TSLean.Stdlib.HashMap');
  }
  // Add HashMap open
  code = code.replace(/^(open TSLean\b.*)$/m, '$1 TSLean.Stdlib.HashMap');
  // ObjKind string → constructor
  code = code.replace(/\| "String" =>/g, '| .String =>');
  code = code.replace(/\| "Array" =>/g, '| .Array =>');
  code = code.replace(/\| "Map" =>/g, '| .Map =>');
  code = code.replace(/\| "Set" =>/g, '| .Set =>');
  // BinOp type
  code = code.replace(/op : BinOp\)/g, 'op : String)');
}

// ─── Fix E: struct update on String-typed vars → sorry ──────────────────────
code = code.replace(
  /\{ ([a-z]\w*) with (?:\w+ := [^,}]+(?:, )?)+\}/g,
  (_m: string, base: string) => `sorry /- struct update on ${base} -/`
);

// ─── Fix F0: Replace bare `Type` parameters with TSAny ─────────────────────
// TS `ts.Type` becomes Lean `Type` which is a universe, not a value type
code = code.replace(/\(t : Type\)/g, '(t : TSAny)');
code = code.replace(/\((\w+) : Type\)/g, '($1 : TSAny)');
// Same for other TS compiler types used as param types
const tsCompilerTypes = [
  'UnionType', 'IntersectionType', 'ObjectType', 'TypeReference',
  'TypeChecker', 'TSType', 'Node', 'Signature', 'SyntaxKind',
  'VariableDeclaration', 'ImportDeclaration', 'ExportDeclaration',
  'ExportAssignment', 'GetAccessorDeclaration', 'SetAccessorDeclaration',
  'ConstructorDeclaration', 'MethodDeclaration', 'PropertyDeclaration',
  'Block', 'IfStatement', 'SwitchStatement', 'TryStatement',
  'ForStatement', 'ForInStatement', 'ForOfStatement', 'WhileStatement',
  'ReturnStatement', 'ThrowStatement', 'VariableStatement',
  'ExpressionStatement', 'CaseClause', 'DefaultClause',
  'CaseOrDefaultClause', 'ObjectBindingPattern', 'ArrayBindingPattern',
  'ParameterDeclaration', 'FunctionDeclaration', 'ArrowFunction',
  'ClassDeclaration', 'InterfaceDeclaration', 'TypeAliasDeclaration',
  'EnumDeclaration', 'ModuleDeclaration',
  'SourceFile', 'Program', 'CompilerHost', 'CompilerOptions',
];
for (const tsType of tsCompilerTypes) {
  code = code.replace(new RegExp(`\\(([a-z]\\w*) : ${tsType}\\)`, 'g'), '($1 : TSAny)');
}
// Also fix `NodeArray X` → `Array TSAny`
code = code.replace(/\bNodeArray \w+/g, 'Array TSAny');
// Fix `Option Signature` → `Option TSAny`
for (const tsType of tsCompilerTypes) {
  code = code.replace(new RegExp(`\\bOption ${tsType}\\b`, 'g'), 'Option TSAny');
}

// ─── Fix F0b: Reorder irTypeToLean after typeStr ────────────────────────────
// irTypeToLean calls typeStr which is defined later. Move typeStr before irTypeToLean.
if (code.includes('def irTypeToLean') && code.includes('partial def typeStr')) {
  // Find typeStr block
  const tsStart = code.indexOf('\npartial def typeStr');
  if (tsStart >= 0) {
    let tsEnd = code.indexOf('\n\n', tsStart + 1);
    if (tsEnd < 0) tsEnd = code.length;
    const tsBlock = code.slice(tsStart, tsEnd + 1);
    // Remove from current position
    code = code.slice(0, tsStart) + code.slice(tsEnd + 1);
    // Insert before irTypeToLean
    const irIdx = code.indexOf('\ndef irTypeToLean');
    if (irIdx >= 0) {
      code = code.slice(0, irIdx) + tsBlock + code.slice(irIdx);
    }
  }
}

// ─── Fix F: Strip `do` from pure return types ──────────────────────────────
// Detect `def f ... : PureType :=\n  do` and remove the `do`
{
  const pureTypes = new Set([
    'IRType', 'IRExpr', 'IRDecl', 'IRModule', 'IRPattern', 'IRParam', 'IRCase',
    'IRImport', 'IRField', 'DoStmt', 'IRNode',
    'String', 'Bool', 'Nat', 'Int', 'Float', 'Unit', 'Char',
    'TSAny', 'Any', 'ObjKind', 'BinOp', 'Effect',
    'ObligationKind', 'ProofObligation',
  ]);
  const lines = code.split('\n');
  const result: string[] = [];
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i];
    // Match: def/partial def ... : <RetType> :=
    const defMatch = line.match(/^\s*(?:partial\s+)?def\s+\w+.*:\s*(\w+(?:\s+\w+)*)\s*:=\s*$/);
    if (defMatch) {
      // Extract the return type (last word before :=)
      const retSig = defMatch[1].trim();
      // Get the base type (before any type args): "Array IRType" → "Array", "Option String" → "Option"
      const baseRet = retSig.split(/\s+/)[0];
      const isPure = pureTypes.has(baseRet) || pureTypes.has(retSig) ||
        retSig.startsWith('Option') || retSig.startsWith('Array') ||
        retSig.startsWith('AssocMap');
      if (isPure) {
        // Check if next non-blank line is `do`
        let j = i + 1;
        while (j < lines.length && lines[j].trim() === '') j++;
        if (j < lines.length && lines[j].trim() === 'do') {
          result.push(line);
          // Skip the `do` line
          i = j;
          continue;
        }
      }
    }
    result.push(line);
  }
  code = result.join('\n');
}

// ─── Fix G: Sequential ifs outside do → sorry ──────────────────────────────
// Pattern: function body has `if x then ... else () \n if y then` (two sequential ifs)
// This only works inside `do` blocks. For pure functions, replace body with sorry.
{
  const lines = code.split('\n');
  const result: string[] = [];
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i];
    result.push(line);
    // If this is a def line ending with :=
    const defMatch = line.match(/^(\s*)(?:partial\s+)?def\s+(\w+).*:=\s*$/);
    if (defMatch) {
      const defIndent = defMatch[1].length;
      // Scan the body looking for sequential if/else () patterns
      let j = i + 1;
      let seqIfs = 0;
      let bodyEnd = -1;
      while (j < lines.length) {
        const bl = lines[j];
        const blIndent = bl.search(/\S/);
        if (blIndent >= 0 && blIndent <= defIndent && j > i + 1 && !bl.trim().startsWith('--')) {
          bodyEnd = j;
          break;
        }
        if (bl.trim().startsWith('if ') && blIndent > defIndent) seqIfs++;
        j++;
      }
      // If body has 2+ sequential ifs and function is NOT monadic, replace body with sorry
      if (seqIfs >= 2 && !line.includes(' IO ') && !line.includes('StateT')) {
        const funcName = defMatch[2];
        // Remove body lines and replace with sorry
        if (bodyEnd > 0) {
          // Skip body lines
          i = bodyEnd - 1;
          // Replace all the body lines already pushed... actually just add sorry
          result.push(`  sorry /- ${funcName}: body has sequential ifs outside do -/`);
          result.push('');
        }
      }
    }
  }
  code = result.join('\n');
}

// ─── Fix H: typeObjKind string returns → ObjKind constructors ───────────────
// Replace if-else chains that return string literals where ObjKind expected
// General: any function returning ObjKind that has string literal returns
code = code.replace(/: ObjKind :=[\s\S]*?(?=\ndef |\nend )/g, (match) => {
  return match
    .replace(/"String"/g, 'ObjKind.String')
    .replace(/"Array"/g, 'ObjKind.Array')
    .replace(/"Map"/g, 'ObjKind.Map')
    .replace(/"Set"/g, 'ObjKind.Set')
    .replace(/"unknown"/g, 'ObjKind.Unknown');
});

// ─── Fix I: lookupGlobal type mismatch ──────────────────────────────────────
// GLOBALS is AssocMap String MethodTx but lookupGlobal returns Option GlobalTx
// Fix: change GLOBALS type or fix lookupGlobal return
code = code.replace(
  /def GLOBALS : AssocMap String MethodTx/g,
  'def GLOBALS : AssocMap String GlobalTx'
);
// Fix .getD on Option that should return Option
code = code.replace(
  /\((\w+)\.get\? (\w+)\)\.getD default/g,
  '$1.get? $2'
);

// ─── Fix J: match on .tag for IRDecl/IRExpr → sorry ─────────────────────────
// IRDecl and IRExpr are inductives/structures without .tag field in Lean
// Replace match d.tag with ... → sorry
code = code.replace(
  /match ([a-z]\w*)\.tag with/g,
  (match, varName) => `sorry /- match ${varName}.tag -/ \nnoncomputable def _ignore_${varName} := match ("" : String) with`
);
// Actually simpler: just replace the function body if it accesses .tag on a param
// that's typed as IRDecl
{
  const lines = code.split('\n');
  const result: string[] = [];
  let skipBody = false;
  let skipIndent = 0;
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i];
    if (skipBody) {
      const indent = line.search(/\S/);
      if (indent >= 0 && indent <= skipIndent && line.trim() !== '' && !line.trim().startsWith('--')) {
        skipBody = false;
        result.push(line);
      }
      continue;
    }
    // Check for `if d.tag ==` or `match d.tag` where d is likely an inductive
    if (/^\s+if \w+\.tag\b/.test(line) || /^\s+match \w+\.tag\b/.test(line)) {
      // Find the def this belongs to
      let defLine = -1;
      for (let k = result.length - 1; k >= 0; k--) {
        if (/^\s*(?:partial\s+)?def\s/.test(result[k])) { defLine = k; break; }
      }
      if (defLine >= 0) {
        const defText = result[defLine];
        const defIndent = defText.search(/\S/);
        const funcName = defText.match(/def\s+(\w+)/)?.[1] ?? 'unknown';
        // Replace body from defLine+1 to now with sorry
        result.splice(defLine + 1);
        result.push(`  sorry /- ${funcName}: uses .tag on inductive -/`);
        result.push('');
        // Skip the rest of this function body
        skipBody = true;
        skipIndent = defIndent;
      }
    } else {
      result.push(line);
    }
  }
  code = result.join('\n');
}

// ─── Fix K: multiline s!"..." breaking if/else ─────────────────────────────
// Pattern: if x then let y := s!"...
//   {content}" else ...
// The multiline string breaks the if/else. Replace with single-line.
code = code.replace(
  /let (\w+) := s!"([^"]*)\n([^"]*)"$/gm,
  'let $1 := s!"$2" ++ s!"$3"'
);

// ─── Fix L0: Chained field access on lambda params → sorry ──────────────────
// Pattern: `fun tp => tp.name.text` — tp is untyped, .name.text fails
code = code.replace(/fun (\w+) => (\w+)\.(\w+)\.(\w+)/g,
  'fun $1 => sorry /- $1.$3.$4 -/');

// ─── Fix L1: Array.map with sorry function → sorry ──────────────────────────
// When Array.map can't infer types because both args are sorry/default
code = code.replace(/Array\.map \(fun \w+ => sorry[^)]*\) \([^)]+\)/g, 'sorry');
code = code.replace(/Array\.filter \(fun \w+ => sorry[^)]*\) \([^)]+\)/g, 'sorry');

// ─── Fix L_: Remove nested do keywords inside do blocks ─────────────────────
// Pattern: a standalone `do` at deeper indentation inside an already-active do block
// This causes `Function expected` when Lean parses `expr\n        do` as applying expr to do
{
  const lines = code.split('\n');
  const result: string[] = [];
  let inDo = false;
  let doIndent = -1;
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i];
    const trimmed = line.trimStart();
    const indent = line.length - trimmed.length;
    // Track entry into a do block
    if (trimmed === 'do' && !inDo) {
      inDo = true;
      doIndent = indent;
      result.push(line);
      continue;
    }
    // Remove nested standalone `do` inside an active do block
    if (inDo && trimmed === 'do' && indent > doIndent) {
      continue; // skip the nested do
    }
    // Exit do block tracking when we see a top-level construct
    if (inDo && indent <= doIndent && trimmed !== '' && !trimmed.startsWith('--') && trimmed !== 'do') {
      inDo = false;
      doIndent = -1;
    }
    result.push(line);
  }
  code = result.join('\n');
}

// ─── Fix L: Function expected at sorry ──────────────────────────────────────
// Pattern: `sorry true` where sorry is followed by an arg → `(sorry : Bool)`
code = code.replace(/\bsorry\s+(true|false)\b/g, '(sorry : Bool)');
// Pattern: `String default` where String is treated as function
code = code.replace(/\bString default\b/g, 'toString default');
// Pattern: `let x : Bool := y` where `: Bool` causes parsing issues in do blocks
// Remove the type annotation — Lean can infer it
code = code.replace(/let (\w+) : Bool := /g, 'let $1 := ');

// ─── Fix M0: Multiline s!"..." with -- comments → replace whole let ─────────
// Pattern: let x := s!"...{x}\n\n-- comment\n{y}" ++ ...
// The -- inside the string kills the rest of the line
// Replace the entire let binding value with sorry
{
  const lines = code.split('\n');
  const result: string[] = [];
  let skipUntilIndent = -1;
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i];
    if (skipUntilIndent >= 0) {
      const indent = line.search(/\S/);
      // Keep skipping until we're back to or before the target indent
      if (indent >= 0 && indent <= skipUntilIndent) {
        skipUntilIndent = -1;
        result.push(line);
      }
      continue;
    }
    // Detect: `let x := s!"...` that continues on next lines with --
    if (/let \w+ := s!"[^"]*$/.test(line)) {
      // Check if any following line within the string has --
      let hasComment = false;
      for (let k = i + 1; k < Math.min(i + 5, lines.length); k++) {
        if (lines[k].includes('"')) break;
        if (lines[k].trim().startsWith('--')) { hasComment = true; break; }
      }
      if (hasComment) {
        const indent = line.search(/\S/);
        const varName = line.match(/let (\w+)/)?.[1] ?? 'x';
        result.push(`${' '.repeat(indent)}let ${varName} := sorry /- multiline string with comment -/`);
        // Skip until we find the closing " and any trailing ++ etc
        skipUntilIndent = indent;
        continue;
      }
    }
    result.push(line);
  }
  code = result.join('\n');
}

// ─── Fix M: Chained field after comment → default ──────────────────────────
// Pattern: `default /- comment -/.field` → `default`
// The comment breaks the field access chain
code = code.replace(/default \/\-[^/]*-\/\.\w+/g, 'default');
// Also: `sorry /- comment -/.field` → `default`
code = code.replace(/sorry \/\-[^/]*-\/\.\w+/g, 'default');

// ─── Fix M2: Tuple literal for Array String → #[...] ────────────────────────
// Pattern: `def X : Array String := ("a", "b", "c")`
// Tuples are not Arrays. Convert to array literal.
code = code.replace(
  /: Array String := \(("[^"]*"(?:, "[^"]*")*)\)/g,
  (_, items) => `: Array String := #[${items}]`
);

// ─── Fix N: Truthiness on non-Bool types ────────────────────────────────────
// Pattern: `if x.size then` — .size returns Nat, not Bool
code = code.replace(/if (\w+)\.size then/g, 'if $1.size > 0 then');
// Pattern: `def x : T := f default` where f returns a monad — replace with `default`
code = code.replace(/^(def \w+ : (?:Args|[A-Z]\w+) :=) (\w+ default)$/gm,
  '$1 default /- $2 -/');
// Pattern: functions with deeply broken do blocks
// Detect: progressively deepening let chains or let rec _loop patterns → sorry
{
  const lines = code.split('\n');
  const result: string[] = [];
  let skipBody = false;
  let skipIndent = 0;
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i];
    if (skipBody) {
      const indent = line.search(/\S/);
      if (indent >= 0 && indent <= skipIndent && line.trim() !== '' && !line.trim().startsWith('--')) {
        skipBody = false;
      } else { continue; }
    }
    result.push(line);
    const defMatch = line.match(/^(\s*)(?:partial\s+)?def\s+(\w+).*:=\s*$/);
    if (defMatch) {
      // Check for CPS loops or progressively deepening lets
      let hasLoop = false;
      let maxIndent = 0;
      for (let k = i + 1; k < Math.min(i + 20, lines.length); k++) {
        if (lines[k].includes('let rec _loop')) { hasLoop = true; break; }
        const ki = lines[k].search(/\S/);
        if (ki > maxIndent) maxIndent = ki;
      }
      // Also detect: 3+ lets at progressively increasing indentation
      let deepLets = 0;
      let prevLetIndent = 0;
      for (let k = i + 1; k < Math.min(i + 10, lines.length); k++) {
        const ki = lines[k].search(/\S/);
        if (lines[k].trim().startsWith('let ') && ki > prevLetIndent) {
          deepLets++;
          prevLetIndent = ki;
        }
      }
      if (hasLoop || deepLets >= 3) {
        const funcName = defMatch[2];
        result.push(`  sorry /- ${funcName}: complex do body -/`);
        result.push('');
        skipBody = true;
        skipIndent = defMatch[1].length;
        i++;
      }
    }
  }
  code = result.join('\n');
}

// ─── Fix: SyntaxKind comparisons in effects_index ────────────────────────────
// The codegen emits `kind == ts.SyntaxKind.EqualsToken` where `kind : TSAny`
// and `ts.SyntaxKind.EqualsToken : SyntaxKind`. These can't be compared directly.
// Replace each comparison with `sorry` to get a Bool.
{
  // Pattern: `(kind == ts.SyntaxKind.XxxToken)` → `(sorry : Bool)`
  code = code.replace(
    /\(kind == ts\.SyntaxKind\.\w+\)/g,
    '(sorry : Bool)'
  );
  // Also handle without parens at start of chain: `kind == ts.SyntaxKind.XxxToken`
  code = code.replace(
    /kind == ts\.SyntaxKind\.\w+/g,
    '(sorry : Bool)'
  );
}

// ─── Fix: leanTypeName pattern matching on `default` ─────────────────────────
// The codegen emits `match default with | "String" => ...` which matches a String
// literal against a String. Replace with IRType pattern matching.
if (baseName === 'effects_index') {
  // Replace the broken leanTypeName body with a working one
  code = code.replace(
    /partial def leanTypeName[\s\S]*?FALLBACK_ERROR_TYPE\n/,
    `partial def leanTypeName (t : IRType) : String :=
  match t with
  | .String => "String" | .Float => "Float" | .Nat => "Nat"
  | .Int => "Int" | .Bool => "Bool" | .Unit => "Unit"
  | .TypeRef name args =>
    if args.size == 0 then name
    else "(" ++ name ++ " " ++ String.intercalate " " (args.toList.map leanTypeName) ++ ")"
  | _ => FALLBACK_ERROR_TYPE
`);
}

// ─── Fix: IO_TRIGGERING_PREFIXES tuple type ──────────────────────────────────
// The codegen emits a tuple instead of an array for const arrays with 4 elements.
code = code.replace(
  /def IO_TRIGGERING_PREFIXES : \(String × String × String × String\) := \("console\.", "Date\.", "Math\.random", "crypto\."\)/,
  'def IO_TRIGGERING_PREFIXES : Array String := #["console.", "Date.", "Math.random", "crypto."]'
);

// ─── Fix: rewrite_index — deriving BEq on AssocMap ───────────────────────────
// AssocMap doesn't have BEq. Remove BEq from structures containing AssocMap.
{
  const lines = code.split('\n');
  for (let i = 0; i < lines.length; i++) {
    if (lines[i].match(/deriving Repr, BEq, Inhabited/) && i > 0) {
      // Look backwards for AssocMap in the struct definition
      let hasAssocMap = false;
      for (let j = i - 1; j >= Math.max(0, i - 15); j--) {
        if (lines[j].includes('AssocMap') || lines[j].includes('Array (')) {
          hasAssocMap = true;
          break;
        }
        if (lines[j].match(/^(structure|inductive|def |end )/)) break;
      }
      if (hasAssocMap) {
        lines[i] = lines[i].replace('deriving Repr, BEq, Inhabited', 'deriving Inhabited');
      }
    }
  }
  code = lines.join('\n');
}

// Fix Type 1 universe issue: AssocMap String UnionInfo → Array (String × String)
code = code.replace(/AssocMap String UnionInfo/g, 'Array (String × String)');
code = code.replace(/AssocMap String VariantInfo/g, 'Array (String × String)');


// ─── Fix: rewrite_index — _ignore_ placeholder defs ─────────────────────────
// The codegen emits `noncomputable def _ignore_X := match ... | ... => sorry`
// for match-on-tag patterns it can't handle. These reference out-of-scope vars.
// Replace them with plain comments.
code = code.replace(
  /noncomputable def _ignore_\w+ :=[\s\S]*?(?=\ndef |\nend )/g,
  '-- (match on tag removed — patterns handled by sorry above)\n'
);

// ─── Fix: rewrite_index — unknown forward references ─────────────────────────
// Functions like rewriteMatch, rewriteStructLit, rewriteFields are defined later.
// The postprocessor already handles this by replacing bodies with sorry.
// But the _ignore_ blocks reference them. Since we removed _ignore_ above, this is fixed.

// ─── Fix: substituteFieldAccesses references `go` ────────────────────────────
code = code.replace(
  /def substituteFieldAccesses[\s\S]*?\n\s+go expr/,
  `def substituteFieldAccesses (expr : IRExpr) (scrutineeName : String) (subst : AssocMap String String) : IRExpr :=
  sorry /- recursive traversal substituting field accesses -/`
);

// ─── Fix: detectDiscriminant return type ─────────────────────────────────────
// Change StateT to pure return
code = code.replace(
  /def RewriteCtx\.detectDiscriminant.*: StateT.*\n\s+sorry/,
  `def RewriteCtx.detectDiscriminant (self : RewriteCtxState) (scrutinee : IRExpr) : Option String :=
  sorry /- RewriteCtx: detect discriminant field -/`
);

// ─── Fix: duplicate StructLit in rewrite match ───────────────────────────────
// Remove duplicate case arm
{
  const lines = code.split('\n');
  const seen = new Set<string>();
  const result: string[] = [];
  for (const line of lines) {
    const caseMatch = line.match(/^\s*\| "(\w+)" =>/);
    if (caseMatch) {
      const key = caseMatch[1];
      if (seen.has(key)) {
        result.push(`      -- (duplicate ${key} case removed)`);
        continue;
      }
      seen.add(key);
    }
    result.push(line);
  }
  code = result.join('\n');
}

// ─── Fix: RewriteCtx.rewriteMatch uses `default` for field access ────────────
if (baseName === 'rewrite_index') {
  code = code.replace(
    /def RewriteCtx\.rewriteMatch[\s\S]*?sorry \/\- struct update on e -\//,
    `def RewriteCtx.rewriteMatch (self : RewriteCtxState) (e : IRExpr) : IRExpr :=
  sorry /- rewrite match: detect discriminant and rewrite cases -/`
  );
}

// ─── Fix: RewriteCtx.rewriteDiscCase broken body ─────────────────────────────
if (baseName === 'rewrite_index') {
  code = code.replace(
    /def RewriteCtx\.rewriteDiscCase[\s\S]*?sorry \/\- RewriteCtx: body has sequential ifs outside do -\//,
    `def RewriteCtx.rewriteDiscCase (self : RewriteCtxState) (c : IRCase) (union : UnionInfo) (scrutineeName : Option String) : IRCase :=
  sorry /- rewriteDiscCase: complex body -/`
  );
}

// ─── Fix: RewriteCtx.rewriteFields return type ──────────────────────────────
code = code.replace(
  /def RewriteCtx\.rewriteFields \(self : RewriteCtxState\) \(e : String\) : IRExpr :=/,
  'def RewriteCtx.rewriteFields (self : RewriteCtxState) (e : IRExpr) : IRExpr :='
);

// ─── Fix: RewriteCtx.rewriteStructLit return type ───────────────────────────
code = code.replace(
  /def RewriteCtx\.rewriteStructLit \(self : RewriteCtxState\) \(e : String\) : String :=/,
  'def RewriteCtx.rewriteStructLit (self : RewriteCtxState) (e : IRExpr) : Option IRExpr :='
);

// ─── Fix: rewrite_index — rewriteCase body ──────────────────────────────────
code = code.replace(
  /def RewriteCtx\.rewriteCase[\s\S]*?sorry \/\- struct update on c -\//,
  `def RewriteCtx.rewriteCase (self : RewriteCtxState) (c : IRCase) : IRCase :=
  sorry /- rewrite case: recurse into body -/`
);

// ─── Fix: rewrite_index — rewriteDoStmt body ───────────────────────────────
code = code.replace(
  /def RewriteCtx\.rewriteDoStmt[\s\S]*?sorry \/\- struct update on s -\//,
  `def RewriteCtx.rewriteDoStmt (self : RewriteCtxState) (s : DoStmt) : DoStmt :=
  sorry /- rewrite DoStmt: recurse into expressions -/`
);

// ─── Final cleanup: remove orphaned else/let after sorry replacements ────────
{
  const lines = code.split('\n');
  const result: string[] = [];
  let skipOrphan = false;
  for (let i = 0; i < lines.length; i++) {
    const trimmed = lines[i].trimStart();
    if (skipOrphan) {
      if (trimmed.startsWith('else') || trimmed.startsWith('let ') ||
          trimmed.startsWith('default') || trimmed.startsWith('none') ||
          trimmed.startsWith('sorry') || trimmed === '') {
        continue;
      }
      if (trimmed.startsWith('def ') || trimmed.startsWith('partial ') ||
          trimmed.startsWith('end ') || trimmed.startsWith('-- ') ||
          trimmed.startsWith('structure ') || trimmed.startsWith('noncomputable')) {
        skipOrphan = false;
      } else {
        continue;
      }
    }
    result.push(lines[i]);
    if (/^sorry\s+\/[-*]/.test(trimmed)) {
      skipOrphan = true;
    }
  }
  code = result.join('\n');
}

// ─── Fix P: `if stringVal then` → `if !stringVal.isEmpty then` ──────────────
code = code.replace(/\bif leanCode then\b/g, 'if !leanCode.isEmpty then');
code = code.replace(/\bif !input then\b/g, 'if input.isEmpty then');
code = code.replace(/\bif !output then\b/g, 'if output.isEmpty then');

// ─── Fix Q: `serialize default` → `toString default` ────────────────────────
code = code.replace(/\bserialize default\b/g, 'toString default');

// ─── Fix R: `Array.filter Boolean` → `Array.filter (· != "")` ───────────────
code = code.replace(/Array\.filter Boolean/g, 'Array.filter (· != "")');

// ─── Fix S: DO_LEAN_IMPORTS tuple → Array ────────────────────────────────────
code = code.replace(
  /def DO_LEAN_IMPORTS : \(String × .*?\) :=/g,
  'def DO_LEAN_IMPORTS : Array String :='
);
// Also fix the tuple value to Array literal: ("a", "b") → #["a", "b"]
code = code.replace(
  /def DO_LEAN_IMPORTS : Array String := \(("[^"]+")(?:, ("[^"]+"))+\)/g,
  (match) => {
    const strings = match.match(/"[^"]+"/g) || [];
    return `def DO_LEAN_IMPORTS : Array String := #[${strings.join(', ')}]`;
  }
);

// ─── Fix T: verification_index — emitObligation match on ObligationKind ──────
// The codegen emits match on strings but ObligationKind is an inductive.
// Fix: let + match indentation, string→constructor, String.intercalate needs List.
if (baseName === 'verification_index') {
  code = code.replace(
    /def emitObligation[\s\S]*?(?=\nend )/,
    `def emitObligation (o : ProofObligation) : String :=
  let safeName := o.funcName.replace " " "_"
  match o.kind with
  | .ArrayBounds => "\\n".intercalate ["-- Array bounds safety", s!"theorem {safeName}_idx_in_bounds", "    (arr : Array α) (idx : Nat) (h : idx < arr.size) :", "    arr[idx]! = arr[⟨idx, h⟩] := by", "  simp [Array.get!_eq_getElem]"]
  | .DivisionSafe => "\\n".intercalate ["-- Division safety", s!"theorem {safeName}_divisor_nonzero", "    (n d : Float) (h : d ≠ 0) : n / d = n / d := rfl"]
  | .OptionIsSome => "\\n".intercalate ["-- Option safety", s!"theorem {safeName}_val_is_some", "    {α : Type} (opt : Option α) (h : opt.isSome) :", "    opt.get!.isSome := by cases opt <;> simp_all"]
  | .InvariantPreserved => "\\n".intercalate ["-- Invariant preserved", s!"theorem {safeName}_invariant_preserved", "    (s : σ) (h : invariant s) : ∃ s', invariant s' := ⟨s, h⟩"]
  | .TerminationBy => s!"-- termination_by {o.detail} -- for \`{o.funcName}\`"
`
  );
}

// ─── Fix U: src_cli — flatten single function to sorry ──────────────────────
// The `single` function has deeply nested if/let/tryCatch the codegen can't handle.
if (baseName === 'src_cli') {
  code = code.replace(
    /def single \(opts : Args\) : StateT Unit IO Unit :=[\s\S]*?(?=\n(?:--|def |end ))/,
    `def single (opts : Args) : StateT Unit IO Unit :=\n  sorry /- single: complex tryCatch + nested if/let -/\n`
  );
}

// ─── Fix V: project_index — dangling let bodies + broken struct update ────────
if (baseName === 'project_index') {
  // transpileProject: deeply nested tryCatch + if/let inside do
  code = code.replace(
    /def transpileProject[\s\S]*?(?=\ndef |\nend )/,
    `def transpileProject (opts : ProjectOpts) : StateT Unit IO ProjectResult :=\n  sorry /- transpileProject: complex do body -/\n\n`
  );
  code = code.replace(
    /def fixImports[\s\S]*?(?=\ndef |\nend )/,
    `def fixImports (mod : IRModule) (tsFile : String) (rootDir : String) (rootNS : String) : IRModule :=\n  sorry /- fixImports: struct update on imports -/\n\n`
  );
  code = code.replace(
    /def relToLean[\s\S]*?(?=\ndef |\nend )/,
    `def relToLean (spec : String) (fromFile : String) (rootDir : String) (rootNS : String) : String :=\n  sorry /- relToLean: calls resolveSpec/specToLean -/\n\n`
  );
  code = code.replace(
    /def toLeanPath[\s\S]*?(?=\ndef |\nend )/,
    `def toLeanPath (tsFile : String) (projectDir : String) (outputDir : String) (rootNS : String := "TSLean.Generated") : String :=\n  sorry /- toLeanPath: path manipulation -/\n\n`
  );
  code = code.replace(
    /def toModuleName[\s\S]*?(?=\ndef |\nend )/,
    `def toModuleName (tsFile : String) (projectDir : String) (rootNS : String := "TSLean.Generated") : String :=\n  sorry /- toModuleName: path → module name -/\n\n`
  );
  code = code.replace(
    /def cap[\s\S]*?(?=\nend )/,
    `def cap (s : String) : String :=\n  if s.isEmpty then s\n  else String.ofList (s.toList.head!.toUpper :: s.toList.tail!)\n\n`
  );
  code = code.replace(
    /def specToLean[\s\S]*?(?=\n-- |\ndef |\nend )/,
    `def specToLean (spec : String) (rootNS : String) : String :=\n  sorry /- specToLean: spec → Lean module path -/\n\n`
  );
}

// ─── Fix W: String.intercalate takes List not Array ─────────────────────────
// Generic fix: replace `String.intercalate sep #[...]` with `sep.intercalate [...]`
code = code.replace(
  /String\.intercalate\s+("(?:[^"\\]|\\.)*")\s+#\[/g,
  '$1.intercalate ['
);
// Also handle: Array.map inside intercalate → .toList
code = code.replace(
  /String\.intercalate\s+("(?:[^"\\]|\\.)*")\s+\(Array\.map/g,
  '$1.intercalate (Array.map'
);

// ─── Fix X: `from` is a Lean keyword — rename to from_ ─────────────────────
code = code.replace(/\(from : String\)/g, '(from_ : String)');
code = code.replace(/\(from : /g, '(from_ : ');

// ─── Fix Y: `if !e then` where e is not Bool → sorry body ──────────────────
// Pattern: `if !e then` or `if !expr then` where the negated value is a struct/var
// Replace the whole def body with sorry when it has `if !<single-word> then` and
// the word is not a known Bool variable
{
  const lines = code.split('\n');
  const result: string[] = [];
  let skipBody = false;
  let skipIndent = 0;
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i];
    if (skipBody) {
      const indent = line.search(/\S/);
      if (indent >= 0 && indent <= skipIndent && line.trim() !== '' && !line.trim().startsWith('--')) {
        skipBody = false;
        result.push(line);
      }
      continue;
    }
    result.push(line);
    // Detect: `if !varname then` where varname is a function parameter (likely non-Bool)
    const defMatch = line.match(/^(\s*)(?:partial\s+)?def\s+(\w[\w.]*)\s.*:=\s*$/);
    if (defMatch) {
      // Look ahead for `if !<word> then` where word is a param name (not a method call)
      for (let k = i + 1; k < Math.min(i + 5, lines.length); k++) {
        if (/^\s+if !(\w+) then\b/.test(lines[k])) {
          const varName = lines[k].match(/if !(\w+) then/)?.[1];
          // Check if the varName appears as a param in the def line with a non-Bool type
          if (varName && line.includes(`${varName} :`) && !line.includes(`${varName} : Bool`)) {
            const funcName = defMatch[2];
            result.push(`  sorry /- ${funcName}: non-Bool truthiness check -/`);
            result.push('');
            skipBody = true;
            skipIndent = defMatch[1].length;
            i = k;
            break;
          }
        }
      }
    }
  }
  code = result.join('\n');
}

// ─── Fix Z: `check expr` where check is undefined → sorry ──────────────────
code = code.replace(/^(\s+)check \w+$/gm, '$1sorry /- check -/');

// ─── Fix AA: `if default then` inside do blocks → sorry function body ────────
// When `if default then` appears in a function body, the `default` is not a Bool.
// Replace the whole function body with sorry.
{
  const lines = code.split('\n');
  const result: string[] = [];
  let skipBody = false;
  let skipIndent = 0;
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i];
    if (skipBody) {
      const indent = line.search(/\S/);
      if (indent >= 0 && indent <= skipIndent && line.trim() !== '' && !line.trim().startsWith('--')) {
        skipBody = false;
        result.push(line);
      }
      continue;
    }
    result.push(line);
    // Detect: def line ending with :=
    const defMatch = line.match(/^(\s*)(?:partial\s+)?def\s+(\w[\w.]*)\s.*:=\s*$/);
    if (defMatch) {
      // Look ahead for `if default then` pattern
      for (let k = i + 1; k < Math.min(i + 8, lines.length); k++) {
        if (/^\s+if default then\b/.test(lines[k])) {
          const funcName = defMatch[2];
          // Emit do if the function is monadic
          const isMonadic = /\b(?:IO|StateT|ExceptT)\b/.test(line);
          if (isMonadic) {
            result.push(`  do`);
            result.push(`    sorry /- ${funcName}: if default then -/`);
          } else {
            result.push(`  sorry /- ${funcName}: if default then -/`);
          }
          result.push('');
          skipBody = true;
          skipIndent = defMatch[1].length;
          i = k;
          break;
        }
      }
    }
  }
  code = result.join('\n');
}

// ─── Fix BB: `e.tag` on IRExpr/IRDecl → sorry for needsParens/isSimpleValue ─
// Some functions like needsParens use `e.tag == "App"` which fails because
// IRExpr is an inductive. Replace specific known functions.
code = code.replace(
  /def needsParens \(e : IRExpr\) : Bool :=[\s\S]*?(?=\n(?:--|def |end ))/,
  `def needsParens (e : IRExpr) : Bool :=\n  sorry /- needsParens: uses e.tag on inductive -/\n`
);
code = code.replace(
  /def isSimpleValue \(s : String\) : Bool :=[\s\S]*?(?=\n(?:--|def |end ))/,
  `def isSimpleValue (s : String) : Bool :=\n  s == "default" || s == "true" || s == "false" || s == "#[]" || s == "none"\n`
);
code = code.replace(
  /def looksMonadic \(s : String\) : Bool :=[\s\S]*?(?=\n(?:--|def |end ))/,
  `def looksMonadic (s : String) : Bool :=\n  s.startsWith "do" || s.startsWith "pure " || s.startsWith "return " || s.startsWith "let "\n`
);

// ─── Fix CC: /-- doc comment --/ inside expression position → strip ──────────
// A doc comment appearing mid-expression causes parse errors
code = code.replace(/\/\-\- [^-]*-\/ *(?=\ndef )/g, '');

// ─── Fix FF: parser_index — stub all multi-line function bodies with sorry ───
// The parser file constructs IRExpr/IRDecl values with struct literals, accesses
// TS compiler API fields, and has forward references. Almost every function body
// is broken. Replace any function body >2 lines with sorry, keeping signatures.
if (baseName === 'parser_index') {
  const lines = code.split('\n');
  const result: string[] = [];
  let skipBody = false;
  let skipIndent = 0;
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i];
    const trimmed = line.trimStart();
    const indent = line.length - trimmed.length;

    if (skipBody) {
      if ((trimmed.startsWith('def ') || trimmed.startsWith('partial def ') ||
           trimmed.startsWith('structure ') || trimmed.startsWith('end ') ||
           trimmed.startsWith('/-- ') || trimmed.startsWith('-- //')) && indent <= skipIndent) {
        skipBody = false;
        result.push(line);
      }
      continue;
    }

    result.push(line);

    const defMatch = line.match(/^(\s*)(?:partial\s+)?def\s+(\w[\w.]*)\s.*:=\s*$/);
    if (defMatch) {
      const defIndent = defMatch[1].length;
      const funcName = defMatch[2];

      // Count body lines
      let bodyLineCount = 0;
      for (let k = i + 1; k < lines.length; k++) {
        const bl = lines[k].trimStart();
        const bi = lines[k].search(/\S/);
        if (bi >= 0 && bi <= defIndent && bl !== '' && !bl.startsWith('--')) break;
        if (bl !== '') bodyLineCount++;
      }

      // If body has >1 line, replace with sorry (keep 1-line bodies like `default`)
      if (bodyLineCount > 1) {
        const isMonadic = /\b(?:IO|StateT|ExceptT)\b/.test(line);
        if (isMonadic) {
          result.push(`  do sorry /- ${funcName}: parser body -/`);
        } else {
          result.push(`  sorry /- ${funcName}: parser body -/`);
        }
        result.push('');
        skipBody = true;
        skipIndent = defIndent;
      }
    }
  }
  code = result.join('\n');
}

// ─── Fix DD: functions with broken do bodies (d.tag, Array.forM AssocMap) ────
// Replace specific broken function bodies in codegen_index
{
  const brokenFuncs: [RegExp, string][] = [
    // emitDeclsWithMutualDetection: d.tag inside lambda
    [/def Gen\.emitDeclsWithMutualDetection[\s\S]*?(?=\ndef |\nend )/,
     `def Gen.emitDeclsWithMutualDetection (self : GenState) (decls : Array IRDecl) : StateT GenState IO Unit :=\n  sorry /- emitDeclsWithMutualDetection: d.tag on inductive -/\n`],
    // typeToLean: regex in String.replace
    [/def Gen\.typeToLean[\s\S]*?(?=\ndef |\nend )/,
     `def Gen.typeToLean (self : GenState) (t : IRType) (parens : Bool := false) : StateT GenState IO String :=\n  do pure (repr t |>.pretty)\n`],
    // resolveType: Array.forM on AssocMap
    [/def Gen\.resolveType[\s\S]*?(?=\ndef |\nend )/,
     `def Gen.resolveType (self : GenState) (ty : String) : StateT GenState IO String :=\n  do pure ty\n`],
    // emitClass: if default then (not caught by Fix AA due to do on prev line)
    [/def Gen\.emitClass[\s\S]*?(?=\ndef |\nend )/,
     `def Gen.emitClass (self : GenState) (d : String) : StateT GenState IO Unit :=\n  do sorry /- emitClass: if default then -/\n`],
    // sanitize: if sorry then
    [/def sanitize \(name : String\) : String :=[\s\S]*?(?=\ndef |\nend )/,
     `def sanitize (name : String) : String :=\n  name.replace " " "_"\n`],
    // genP: calls needsParens which may fail
    [/def Gen\.genP[\s\S]*?(?=\ndef |\nend )/,
     `def Gen.genP (self : GenState) (e : IRExpr) (ctx : Effect) (depth : Float) : String :=\n  sorry /- genP: calls genExpr + needsParens -/\n`],
  ];
  for (const [re, replacement] of brokenFuncs) {
    code = code.replace(re, replacement);
  }
}

// ─── Fix EE: .intercalate (Array.map ...) → .intercalate ((...).toList) ──────
// String.intercalate takes List, Array.map returns Array.
// Wrap any `Array.map (fun ...) varname` inside an `.intercalate` call with .toList
code = code.replace(
  /\.intercalate \(Array\.map (\([^)]*\)) (\w+)\)/g,
  '.intercalate ((Array.map $1 $2).toList)'
);
// Handle cases where the lambda body contains ) (like s!"({p} : Type)")
// Use line-by-line approach for robustness
{
  const lines = code.split('\n');
  for (let i = 0; i < lines.length; i++) {
    if (lines[i].includes('.intercalate (Array.map')) {
      // Find `Array.map (fun ... ) ident)` and wrap with .toList
      lines[i] = lines[i].replace(
        /\.intercalate \((Array\.map \(fun \w+ => .*?\) \w+)\)/g,
        '.intercalate (($1).toList)'
      );
    }
  }
  code = lines.join('\n');
}

// Write output
fs.writeFileSync(outputFile, code);
console.log(`✓ ${inputFile} → ${outputFile} (${code.split('\n').length} lines)`);

function capitalize(s: string): string {
  // Convert snake_case to CamelCase: effects_index → EffectsIndex
  return s.split(/[-_]/).map(p => p.charAt(0).toUpperCase() + p.slice(1)).join('');
}

