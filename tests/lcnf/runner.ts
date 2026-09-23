// Runs one compiled LCNF module against the cases its Lean driver wrote.
//
//   node --experimental-strip-types tests/lcnf/runner.ts <dir>/<name>.json [--repeat N]
//
// Arguments and expected results are in the R format (see lean/TSLean/Lcnf/Driver.lean): a prefix
// token stream over the JS representation. Decoding and rendering both use explicit stacks, so a
// 10^6-deep value never touches the JS call stack; only the compiled code under test does.
import { readFileSync } from "node:fs";
import { dirname, resolve } from "node:path";
import { pathToFileURL } from "node:url";
import { Closure, type Fn, type Obj, type Value } from "../../src/lcnf-runtime/index.ts";

interface Case {
  label: string;
  fn: string;
  args: string[];
  expect: string;
}

interface Manifest {
  module: string;
  cases: Case[];
}

function isFn(v: unknown): v is Fn {
  return typeof v === "function";
}

function isManifest(v: unknown): v is Manifest {
  return typeof v === "object" && v !== null && "module" in v && "cases" in v && Array.isArray(v.cases);
}

function decode(text: string): Value {
  const tokens = text.split(" ");
  // Pending objects: their tag, arity and fields so far.
  const stack: { tag: number; arity: number; fields: Value[] }[] = [];
  let result: Value = undefined;
  let done = false;
  for (const t of tokens) {
    if (done) throw new Error(`trailing token ${t}`);
    let v: Value;
    switch (t[0]) {
      case "n": v = BigInt(t.slice(1)); break;
      case "t": v = true; break;
      case "f": v = false; break;
      case "u": v = undefined; break;
      case "e": v = Number(t.slice(1)); break;
      case "o": {
        const [tag, arity] = t.slice(1).split(".").map(Number);
        if (tag === undefined || arity === undefined) throw new Error(`bad token ${t}`);
        if (arity > 0) { stack.push({ tag, arity, fields: [] }); continue; }
        v = { tag, fields: [] };
        break;
      }
      default: throw new Error(`bad token ${t}`);
    }
    // Place v, closing every object it completes.
    for (;;) {
      const top = stack[stack.length - 1];
      if (top === undefined) { result = v; done = true; break; }
      top.fields.push(v);
      if (top.fields.length < top.arity) break;
      stack.pop();
      const o: Obj = { tag: top.tag, fields: top.fields };
      v = o;
    }
  }
  if (!done) throw new Error("truncated value");
  return result;
}

function render(v: Value): string {
  const out: string[] = [];
  const todo: Value[] = [v];
  while (todo.length > 0) {
    const x = todo.pop();
    if (typeof x === "bigint") out.push(`n${x}`);
    else if (typeof x === "boolean") out.push(x ? "t" : "f");
    else if (typeof x === "number") out.push(`e${x}`);
    else if (x === undefined) out.push("u");
    else if (x instanceof Closure) out.push("c");
    else if (typeof x === "string") out.push(`s${JSON.stringify(x)}`);
    else {
      out.push(`o${x.tag}.${x.fields.length}`);
      for (let i = x.fields.length - 1; i >= 0; i--) todo.push(x.fields[i]);
    }
  }
  return out.join(" ");
}

function abbreviate(s: string): string {
  return s.length > 160 ? `${s.slice(0, 160)}… (${s.length} chars)` : s;
}

const [manifestPath, ...rest] = process.argv.slice(2);
if (manifestPath === undefined) throw new Error("usage: runner.ts <manifest.json> [--repeat N]");
const repeat = rest[0] === "--repeat" ? Number(rest[1]) : 1;
const manifest: unknown = JSON.parse(readFileSync(manifestPath, "utf8"));
if (!isManifest(manifest)) throw new Error(`${manifestPath} is not a manifest`);
// The module under test is generated per run and named by the manifest, so it cannot be a static import.
const mod: Record<string, unknown> = await import(pathToFileURL(resolve(dirname(manifestPath), manifest.module)).href);

let failures = 0;
for (const c of manifest.cases) {
  const f = mod[c.fn];
  if (!isFn(f)) throw new Error(`${c.label}: module has no function ${c.fn}`);
  const args = c.args.map(decode);
  let got: string;
  let ms = 0;
  try {
    // With --repeat, one untimed run first, so the figure is steady-state rather than cold.
    let r: Value = repeat > 1 ? f(...args) : undefined;
    const t0 = performance.now();
    for (let i = 0; i < repeat; i++) r = f(...args);
    ms = (performance.now() - t0) / repeat;
    got = render(r);
  } catch (e) {
    got = `<threw ${e instanceof Error ? `${e.name}: ${e.message}` : String(e)}>`;
  }
  if (got === c.expect) {
    console.log(`ok   ${c.label} (${ms.toFixed(3)} ms)`);
  } else {
    failures++;
    console.log(`FAIL ${c.label}: got ${abbreviate(got)}, expected ${abbreviate(c.expect)}`);
  }
}
console.log(`${manifest.cases.length - failures}/${manifest.cases.length} cases agree with #eval`);
process.exitCode = failures === 0 ? 0 : 1;
