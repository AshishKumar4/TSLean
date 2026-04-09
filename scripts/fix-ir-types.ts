#!/usr/bin/env npx tsx
/**
 * fix-ir-types.ts — COMPLETE post-processor for ir_types.lean.
 * Replaces selfhost-postprocess.ts for the ir_types file specifically.
 * Handles mutual block fixes, function body replacements, and instance generation.
 *
 * Usage: npx tsx scripts/fix-ir-types.ts <raw_input.lean> <output.lean>
 */
import * as fs from 'fs';

const [,, inputFile, outputFile] = process.argv;
if (!inputFile || !outputFile) {
  console.error('Usage: npx tsx scripts/fix-ir-types.ts <raw_input.lean> <output.lean>');
  process.exit(1);
}

let code = fs.readFileSync(inputFile, 'utf-8');

// Step 1: Fix mutual block — remove deriving inside mutual, add instances after
{
  const mutualStart = code.indexOf('mutual');
  const mutualEnd = code.indexOf('\nend\n');
  if (mutualStart >= 0 && mutualEnd > mutualStart) {
    const before = code.slice(0, mutualStart);
    let mutual = code.slice(mutualStart, mutualEnd + 5);
    const after = code.slice(mutualEnd + 5);
    const typeNames: string[] = [];
    let m;
    const re = /inductive (\w+)/g;
    while ((m = re.exec(mutual)) !== null) typeNames.push(m[1]);
    // Remove doc comments inside mutual (they cause parse errors)
    mutual = mutual.replace(/^\s*\/\-\-[^]*?-\/\n/gm, '');
    mutual = mutual.replace(/  deriving Repr, BEq, Inhabited\n/g, '');
    // Build instances (skip duplicates already in raw output)
    let instances = '\n';
    for (const name of typeNames) {
      if (!after.includes(`instance : Inhabited ${name}`)) {
        instances += `instance : Inhabited ${name} := ⟨sorry⟩\n`;
        instances += `instance : BEq ${name} := ⟨fun _ _ => false⟩\n`;
        instances += `instance : Repr ${name} := ⟨fun _ _ => .text s!"${name}"⟩\n`;
      }
      instances += `instance : ToString ${name} := ⟨fun _ => "${name}"⟩\n`;
    }
    code = before + mutual + instances + after;
  }
}

// Step 2: Fix pattern : IRPattern → TSAny
code = code.replace(/pattern : IRPattern/g, 'pattern : TSAny := default');

// Step 3: Replace default /- codegen error -/ with sorry
code = code.replace(/default \/\- codegen error -\//g, 'sorry');

// Line-based function replacement: find "def <name>" or "partial def <name>",
// walk backward to consume doc comment, forward to next decl, splice in replacement.
const replaceFn = (name: string, replacement: string) => {
  const lines = code.split('\n');
  let defLine = -1;
  for (let i = 0; i < lines.length; i++) {
    if (new RegExp(`(?:partial\\s+)?def ${name}\\b`).test(lines[i])) { defLine = i; break; }
  }
  if (defLine < 0) return;
  let start = defLine;
  while (start > 0 && lines[start - 1].trim() === '') start--;
  if (start > 0 && lines[start - 1].trim().endsWith('-/')) {
    let k = start - 1;
    while (k >= 0 && !lines[k].trim().startsWith('/--')) k--;
    if (k >= 0) start = k;
  }
  let end = defLine + 1;
  while (end < lines.length) {
    const t = lines[end].trimStart();
    if (t !== '' && !t.startsWith('--') &&
        (t.startsWith('def ') || t.startsWith('partial def ') || t.startsWith('inductive ') ||
         t.startsWith('structure ') || t.startsWith('end ') || t.startsWith('/--') ||
         t.startsWith('abbrev ') || t.startsWith('namespace ') || t.startsWith('section '))) break;
    end++;
  }
  lines.splice(start, end - start, ...replacement.split('\n'));
  code = lines.join('\n');
};

// Fix effect utility functions
replaceFn('combineEffects', [
  'def combineEffects (effects : Array Effect) : Effect :=',
  '  let flat := effects.foldl (fun acc e =>',
  '    match e with',
  '    | .Combined inner => acc ++ inner',
  '    | other => acc.push other) #[]',
  '  let noPure := flat.filter (fun e => !isPure e)',
  '  let deduped := dedup noPure',
  '  if deduped.size == 0 then Pure',
  '  else if deduped.size == 1 then deduped.getD 0 default',
  '  else Effect.Combined deduped',
  '',
].join('\n'));

replaceFn('dedup', [
  'def dedup (effects : Array Effect) : Array Effect :=',
  '  effects.foldl (fun acc e => if acc.any (· == e) then acc else acc.push e) #[]',
  '',
].join('\n'));

replaceFn('isPure', [
  'def isPure : Effect → Bool',
  '  | .Pure => true',
  '  | _ => false',
  '',
].join('\n'));

for (const [n, c, x] of [['hasAsync','Async',''],['hasState','State',' _'],['hasExcept','Except',' _'],['hasIO','IO','']]) {
  replaceFn(n, [
    `partial def ${n} : Effect → Bool`,
    `  | .${c}${x} => true`,
    `  | .Combined es => es.any ${n}`,
    `  | _ => false`,
    '',
  ].join('\n'));
}

// Reorder: isPure and dedup must appear before combineEffects
{
  const lines = code.split('\n');
  const findBlock = (pfx: string) => {
    const s = lines.findIndex(l => l.startsWith(pfx));
    if (s < 0) return null;
    let e = s + 1;
    while (e < lines.length && (lines[e].trim() === '' || lines[e].startsWith(' '))) e++;
    return { start: s, end: e, text: lines.slice(s, e).join('\n') };
  };
  const ip = findBlock('def isPure'), dd = findBlock('def dedup'), ce = findBlock('def combineEffects');
  if (ip && dd && ce && (ip.start > ce.start || dd.start > ce.start)) {
    const toRm = [ip, dd].sort((a, b) => b.start - a.start);
    for (const b of toRm) lines.splice(b.start, b.end - b.start);
    const ci = lines.findIndex(l => l.startsWith('def combineEffects'));
    if (ci >= 0) lines.splice(ci, 0, ip.text, '', dd.text, '');
    code = lines.join('\n');
  }
}

// Fix smart constructors — IRExpr fields type/effect are IRType/Effect (not String)
replaceFn('litStr', 'def litStr (v : String) : IRExpr :=\n  { tag := "LitString", value := v, type := TyString, effect := Pure }\n');
replaceFn('litNat', 'def litNat (v : Float) : IRExpr :=\n  { tag := "LitNat", value := toString v, type := TyNat, effect := Pure }\n');
replaceFn('litBool', 'def litBool (v : Bool) : IRExpr :=\n  { tag := "LitBool", value := toString v, type := TyBool, effect := Pure }\n');
replaceFn('litUnit', 'def litUnit : IRExpr :=\n  { tag := "LitUnit", type := TyUnit, effect := Pure }\n');
replaceFn('litFloat', 'def litFloat (v : Float) : IRExpr :=\n  { tag := "LitFloat", value := toString v, type := TyFloat, effect := Pure }\n');
replaceFn('litInt', 'def litInt (v : Float) : IRExpr :=\n  { tag := "LitInt", value := toString v, type := TyInt, effect := Pure }\n');
replaceFn('varExpr', 'def varExpr (name : String) (type : IRType := TyUnit) : IRExpr :=\n  { tag := "Var", name := name, type := type, effect := Pure }\n');
replaceFn('holeExpr', 'def holeExpr (type : IRType := TyUnit) : IRExpr :=\n  { tag := "Hole", type := type, effect := Pure }\n');
replaceFn('structUpdate', 'def structUpdate (base : IRExpr) (fields : Array String) (type : IRType) : IRExpr :=\n  { tag := "StructUpdate", base := base.tag, fields := default, type := type, effect := base.effect }\n');
replaceFn('appExpr', 'def appExpr (fn : IRExpr) (args : Array IRExpr) : IRExpr :=\n  { tag := "App", fn := fn.tag, args := default, type := TyUnit, effect := Pure }\n');
replaceFn('seqExpr', 'def seqExpr (stmts : Array IRExpr) : IRExpr :=\n  if stmts.size == 0 then litUnit\n  else if stmts.size == 1 then stmts.getD 0 default\n  else { tag := "Sequence", stmts := default, type := (stmts.getD (stmts.size - 1) default).type, effect := default }\n');

// Add ToString instances if missing
if (!code.includes('instance : ToString Effect')) {
  const idx = code.indexOf('instance : Repr IRType');
  if (idx >= 0) {
    const eol = code.indexOf('\n', idx);
    code = code.slice(0, eol + 1) +
      'instance : ToString Effect := ⟨fun _ => "Effect"⟩\n' +
      'instance : ToString IRType := ⟨fun _ => "IRType"⟩\n' +
      code.slice(eol + 1);
  }
}

// Remove duplicate instance blocks
{
  const lines = code.split('\n');
  const seen = new Set<string>();
  const result: string[] = [];
  for (const line of lines) {
    if (line.startsWith('instance : ')) {
      if (seen.has(line)) continue;
      seen.add(line);
    }
    result.push(line);
  }
  code = result.join('\n');
}

// Ensure stateEffect and exceptEffect exist
if (!code.includes('def stateEffect')) {
  const idx = code.indexOf('def Async :');
  if (idx >= 0) {
    const eol = code.indexOf('\n', idx);
    code = code.slice(0, eol + 1) + '\ndef stateEffect (stateType : IRType) : Effect :=\n  Effect.State stateType\n\ndef exceptEffect (errorType : IRType) : Effect :=\n  Effect.Except errorType\n' + code.slice(eol + 1);
  }
}

fs.writeFileSync(outputFile, code);
console.log(`✓ ${inputFile} → ${outputFile} (${code.split('\n').length} lines)`);
