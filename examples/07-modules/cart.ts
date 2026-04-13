// 07-modules/cart.ts
// Shopping cart using types from ./types.ts

import { Item, formatPrice } from './types.js';

export function totalPrice(items: Item[]): number {
  return items.reduce((sum, item) => sum + item.price, 0);
}

export function addItem(items: Item[], item: Item): Item[] {
  return [...items, item];
}

export function removeItem(items: Item[], id: string): Item[] {
  return items.filter(item => item.id !== id);
}

export function summary(items: Item[]): string {
  const total = totalPrice(items);
  return `${items.length} items, total: ${formatPrice(total, 'USD')}`;
}
