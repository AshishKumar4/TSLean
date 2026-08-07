import { validateFixture } from '../../scripts/differential-manifest-lib.mjs';
import type { Canonicalizer } from './canonical.js';
import type { Fixture } from './types.js';

function numberFromBits(bits: string): number {
  const buffer = new ArrayBuffer(8);
  const view = new DataView(buffer);
  view.setBigUint64(0, BigInt(bits), false);
  return view.getFloat64(0, false);
}

function stringFromUnits(units: number[]): string {
  let value = '';
  for (let index = 0; index < units.length; index += 1024) {
    value += String.fromCharCode(...units.slice(index, index + 1024));
  }
  return value;
}

export function materializeFixtures(fixtures: Fixture[], canonicalizer: Canonicalizer): Parameters<typeof structuredClone>[0][] {
  const symbols = new Map<string, symbol>();
  return fixtures.map((fixture) => {
    validateFixture(fixture);
    switch (fixture.kind) {
      case 'undefined': return undefined;
      case 'null': return null;
      case 'boolean': return fixture.value;
      case 'number': return numberFromBits(fixture.bits);
      case 'string': return stringFromUnits(fixture.units);
      case 'bigint': return BigInt(fixture.decimal);
      case 'symbol': {
        let symbol = symbols.get(fixture.identity);
        if (symbol === undefined) {
          symbol = Symbol.for(fixture.identity);
          symbols.set(fixture.identity, symbol);
          canonicalizer.registerSymbol(symbol, fixture.identity);
        }
        return symbol;
      }
      case 'graph': throw new Error('graph fixtures must be materialized inside a VM context');
    }
  });
}
