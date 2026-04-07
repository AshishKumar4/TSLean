export type UserId = string & { readonly __brand: 'UserId' };
export type RoomId = string & { readonly __brand: 'RoomId' };

export interface User { id: UserId; email: string; displayName: string; createdAt: number; roles: string[] }
export interface Room { id: RoomId; name: string; ownerId: UserId; createdAt: number; maxMembers: number }

export type ApiResponse<T> =
  | { ok: true; data: T }
  | { ok: false; error: string; code: number };

export function makeApiSuccess<T>(data: T): ApiResponse<T> { return { ok: true, data }; }
export function makeApiError<T>(error: string, code: number): ApiResponse<T> { return { ok: false, error, code }; }
