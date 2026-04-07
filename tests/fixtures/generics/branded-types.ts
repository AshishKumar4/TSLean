// Branded types → Lean newtype structures

type UserId       = string & { readonly __brand: 'UserId' };
type RoomId       = string & { readonly __brand: 'RoomId' };
type MessageId    = string & { readonly __brand: 'MessageId' };
type SessionToken = string & { readonly __brand: 'SessionToken' };
type EmailAddress = string & { readonly __brand: 'EmailAddress' };

function makeUserId(raw: string): UserId { return raw as UserId; }
function makeRoomId(raw: string): RoomId { return raw as RoomId; }
function makeSessionToken(raw: string): SessionToken { return raw as SessionToken; }
function getUserIdString(id: UserId): string { return id as string; }

interface UserProfile { id: UserId; email: EmailAddress; displayName: string }

function createUserProfile(id: UserId, email: EmailAddress, name: string): UserProfile {
  return { id, email, displayName: name };
}
