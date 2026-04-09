#!/usr/bin/env npx tsx
/**
 * selfhost-postprocess.ts - Fix raw transpiler output for Lean 4 compilation.
 * Usage: npx tsx scripts/selfhost-postprocess.ts <input.lean> <output.lean>
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

// Step 1: Fix namespace
if (baseName !== 'ir_types' && baseName !== 'IR_Types') {
  const nsName = `TSLean.Generated.SelfHost.${capitalize(baseName)}`;
  code = code.replace(/namespace TSLean\.Generated\.\w+/g, `namespace ${nsName}`);
  code = code.replace(/end TSLean\.Generated\.\w+/g, `end ${nsName}`);
}

// Step 2: Fix cross-file imports
for (const [from, to] of Object.entries({
  'TSLean.Generated.Ir.Types': 'TSLean.Generated.SelfHost.ir_types',
  'TSLean.Generated.Effects.Index': 'TSLean.Generated.SelfHost.effects_index',
  'TSLean.Generated.Stdlib.Index': 'TSLean.Generated.SelfHost.stdlib_index',
  'TSLean.Generated.Typemap.Index': 'TSLean.Generated.SelfHost.typemap_index',
  'TSLean.Generated.Codegen.Index': 'TSLean.Generated.SelfHost.codegen_index',
  'TSLean.Generated.Parser.Index': 'TSLean.Generated.SelfHost.parser_index',
  'TSLean.Generated.Rewrite.Index': 'TSLean.Generated.SelfHost.rewrite_index',
  'TSLean.Generated.Verification.Index': 'TSLean.Generated.SelfHost.verification_index',
  'TSLean.Generated.Project.Index': 'TSLean.Generated.SelfHost.project_index',
})) code = code.replaceAll(`import ${from}`, `import ${to}`);

// Step 3: Add Prelude + ir_types imports
if (baseName !== 'ir_types' && baseName !== 'IR_Types') {
  const i = code.indexOf('import ');
  if (i >= 0) code = code.slice(0, i) + 'import TSLean.Generated.SelfHost.Prelude\nimport TSLean.Generated.SelfHost.ir_types\n' + code.slice(i);
}
if (code.includes('import TSLean.Generated.SelfHost.ir_types'))
  code = code.replace(/open TSLean\b/, 'open TSLean TSLean.Generated.Types');

// Step 4: Fix mutual blocks - line-by-line processing
{
  const lines = code.split('\n');
  const out: string[] = [];
  let inMut = false, inDoc = false;
  const names: string[] = [];
  for (let i = 0; i < lines.length; i++) {
    const L = lines[i];
    if (L.trim() === 'mutual') { inMut = true; names.length = 0; out.push(L); continue; }
    if (inMut && L.trim() === 'end') {
      inMut = false; out.push(L); out.push('');
      for (const n of names) {
        out.push(`instance : Inhabited ${n} := \u27E8sorry\u27E9`);
        out.push(`instance : BEq ${n} := \u27E8fun _ _ => false\u27E9`);
        out.push(`instance : Repr ${n} := \u27E8fun _ _ => .text s!"${n}"\u27E9`);
      }
      out.push(''); continue;
    }
    if (inMut) {
      const m = L.match(/^inductive (\w+)|^structure (\w+)/);
      if (m) names.push(m[1] || m[2]);
      if (L.trim().startsWith('deriving ')) continue;
      if (L.trim().startsWith('/--')) { inDoc = true; if (L.includes('-/')) inDoc = false; continue; }
      if (inDoc) { if (L.includes('-/')) inDoc = false; continue; }
    }
    out.push(L);
  }
  code = out.join('\n');
}

// Step 5: Fix ir_types specific functions BEFORE default->sorry
if (baseName === 'ir_types' || baseName === 'IR_Types') {
  // Replace a function body: find "def <name>" to next "\ndef " or "\npartial def "
  const replaceFnBody = (name: string, newBody: string) => {
    const marker = `def ${name}`;
    const idx = code.indexOf(marker);
    if (idx < 0) return;
    // Also consume preceding doc comment
    let start = idx;
    const before = code.slice(0, idx);
    const lastNL = before.lastIndexOf('\n');
    // Check if there's a doc comment ending on the line before
    const prevLines = before.split('\n');
    for (let j = prevLines.length - 1; j >= 0; j--) {
      const pl = prevLines[j].trim();
      if (pl === '' || pl.startsWith('--')) { start = before.lastIndexOf(prevLines[j]); continue; }
      if (pl.endsWith('-/')) {
        // Find matching /--
        for (let k = j; k >= 0; k--) {
          if (prevLines[k].trim().startsWith('/--')) {
            start = code.indexOf(prevLines[k], code.lastIndexOf('\n', start));
            break;
          }
        }
      }
      break;
    }
    // Find end of function: next line starting with def/partial def/inductive/structure/end/abbrev
    const rest = code.slice(idx);
    const endM = rest.match(/\n(?=\/\-\-|def |partial def |inductive |structure |end |abbrev )/);
    const end = endM ? idx + endM.index! : code.length;
    code = code.slice(0, start >= 0 ? start : idx) + newBody + code.slice(end);
  };

  replaceFnBody('isPure', '\ndef isPure : Effect \u2192 Bool\n  | .Pure => true\n  | _ => false\n');
  replaceFnBody('dedup', '\ndef dedup (effects : Array Effect) : Array Effect :=\n  effects.foldl (fun acc e => if acc.any (\u00B7 == e) then acc else acc.push e) #[]\n');
  replaceFnBody('combineEffects',
    '\ndef combineEffects (effects : Array Effect) : Effect :=\n' +
    '  let flat := effects.foldl (fun acc e =>\n' +
    '    match e with\n' +
    '    | .Combined inner => acc ++ inner\n' +
    '    | other => acc.push other) #[]\n' +
    '  let noPure := flat.filter (fun e => !isPure e)\n' +
    '  let deduped := dedup noPure\n' +
    '  if deduped.size == 0 then Pure\n' +
    '  else if deduped.size == 1 then deduped.getD 0 default\n' +
    '  else Effect.Combined deduped\n');

  // Reorder: isPure and dedup before combineEffects
  const isPure = code.match(/\ndef isPure[\s\S]*?\| _ => false\n/)?.[0];
  const dedup = code.match(/\ndef dedup[\s\S]*?#\[\]\n/)?.[0];
  if (isPure && dedup) {
    code = code.replace(isPure, '\n');
    code = code.replace(dedup, '\n');
    const ci = code.indexOf('\ndef combineEffects');
    if (ci >= 0) code = code.slice(0, ci) + isPure + dedup + code.slice(ci);
  }

  // Fix has* functions
  for (const [n, c, x] of [['hasAsync','Async',''],['hasState','State',' _'],['hasExcept','Except',' _'],['hasIO','IO','']]) {
    replaceFnBody(n, `\npartial def ${n} : Effect \u2192 Bool\n  | .${c}${x} => true\n  | .Combined es => es.any ${n}\n  | _ => false\n`);
  }
  replaceFnBody('stateType', '\ndef stateType : Effect \u2192 Option IRType\n  | .State t => some t\n  | .Combined es => es.findSome? stateType\n  | _ => none\n');
  replaceFnBody('exceptType', '\ndef exceptType : Effect \u2192 Option IRType\n  | .Except t => some t\n  | .Combined es => es.findSome? exceptType\n  | _ => none\n');
}

// Step 6: default /- ... -/ -> sorry
code = code.replace(/default \/\- codegen error -\//g, 'sorry');
code = code.replace(/default \/\- cross-file:.*?-\//g, 'sorry');
code = code.replace(/sorry \/\- complex body -\//g, 'sorry');
code = code.replace(/default \/\-[^/]*?-\//g, 'sorry');

// Step 7: Fix struct literals - toString wrap for type/effect fields
code = code.replace(
  /\{ tag := ("[^"]+"), (\w+) := (\w+), type := (\w+), effect := (\w+) \}/g,
  (_, tag, f, v, t, e) => {
    const fv = (f === 'value' && !['v','name'].includes(v)) ? `${f} := toString ${v}` : `${f} := ${v}`;
    return `{ tag := ${tag}, ${fv}, type := toString ${t}, effect := toString ${e} }`;
  });
code = code.replace(
  /\{ tag := ("[^"]+"), type := (\w+), effect := (\w+) \}/g,
  (_, tag, t, e) => `{ tag := ${tag}, type := toString ${t}, effect := toString ${e} }`);

// Step 8: Fix chained field access
code = code.replace(/stmts\.getD \(stmts\.size - 1\) default\.type/g, '(stmts.getD (stmts.size - 1) default).type');
code = code.replace(/combineEffects #\[fn\.effect, Array\.map/g, 'combineEffects (#[fn.effect] ++ Array.map');

// Step 9: Fix pattern : IRPattern
code = code.replace(/pattern : IRPattern(?!\s*:=)/g, 'pattern : TSAny := default');

fs.writeFileSync(outputFile, code);
console.log(`Done: ${inputFile} -> ${outputFile} (${code.split('\n').length} lines)`);

function capitalize(s: string): string {
  return s.split('_').map(p => p.charAt(0).toUpperCase() + p.slice(1)).join('');
}
