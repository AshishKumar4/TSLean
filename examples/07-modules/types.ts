// 07-modules/types.ts
// Shared types for the multi-file example.

export interface Item {
  id: string;
  name: string;
  price: number;
}

export type Currency = 'USD' | 'EUR' | 'GBP';

export function formatPrice(amount: number, currency: Currency): string {
  return `${amount} ${currency}`;
}
