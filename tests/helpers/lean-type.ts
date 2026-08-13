import { lowerModule } from '../../src/codegen/lower.js';
import { printTyStr, printDeclStr } from '../../src/codegen/printer.js';
import type { IRType, IRModule, TypeParam } from '../../src/ir/types.js';
import type { LeanDecl } from '../../src/codegen/lean-ast.js';

const PROBE = 'Probe';

/** `name: 'T'` suppresses the namespace wrapper, so decls stay at the top level. */
function lower(decls: IRModule['decls']): LeanDecl[] {
  return lowerModule({ name: 'T', imports: [], decls, comments: [], sourceFile: 'probe.ts' }).decls;
}

/**
 * Render an IR type through the transpiler's single IRType → Lean renderer
 * (`LowerCtx.lowerType`), as the text the printer emits for it.
 *
 * The renderer is a method on the lowering context because it consults that
 * context (type-alias arity, for one), so there is no free function to call and
 * deliberately no second entry point: a helper that built its own context would
 * be the very drift these tests exist to prevent. A struct field is the shortest
 * position that carries a type straight through `lowerType` with no
 * declaration-level policy layered on top.
 */
export function leanTypeOf(t: IRType): string {
  const decls = lower([{ tag: 'StructDef', name: PROBE, typeParams: [], fields: [{ name: 'f', type: t }] }]);
  const probe = decls.find(
    (d): d is Extract<LeanDecl, { tag: 'Structure' }> => d.tag === 'Structure' && d.name === PROBE,
  );
  if (!probe || probe.fields.length !== 1) {
    throw new Error(`leanTypeOf: expected one lowered structure named ${PROBE} with one field`);
  }
  return printTyStr(probe.fields[0].ty);
}

/**
 * Lower one type alias and return the declaration the printer emits for it.
 *
 * `lowerTypeAlias` decides more than `lowerType` does — whether the body is
 * erased, whether it is self-referential, and how many type parameters survive
 * into the signature — so those decisions need their own assertions at the
 * declaration level, not just at the type level.
 */
export function leanAliasOf(name: string, body: IRType, typeParams: TypeParam[] = []): string {
  const decls = lower([{ tag: 'TypeAlias', name, typeParams, body }]);
  const alias = decls.find((d) => d.tag === 'Abbrev' || d.tag === 'Structure');
  if (!alias) throw new Error(`leanAliasOf: ${name} lowered to no abbrev or structure`);
  return printDeclStr(alias).split('\n')[0];
}
