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

// Write output
fs.writeFileSync(outputFile, code);
console.log(`✓ ${inputFile} → ${outputFile} (${code.split('\n').length} lines)`);

function capitalize(s: string): string {
  // Convert snake_case to CamelCase: effects_index → EffectsIndex
  return s.split('_').map(p => p.charAt(0).toUpperCase() + p.slice(1)).join('');
}
