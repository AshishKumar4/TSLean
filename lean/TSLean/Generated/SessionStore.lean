-- TSLean.Generated.SessionStore
-- TypeScript → Lean 4 transpiled Durable Object for session management
-- Original TypeScript pattern: class SessionStoreDO extends DurableObject { ... }

import TSLean.DurableObjects.Model
import TSLean.DurableObjects.SessionStore
import TSLean.Runtime.Monad
import TSLean.Runtime.BrandedTypes

namespace TSLean.Generated.SessionStore
open TSLean TSLean.DO TSLean.DO.SessionStore

-- TypeScript: type SessionData = { userId: string, expiresAt: number, data: object }
abbrev SessionData := Session

-- TypeScript: type Store = SessionStore
abbrev Store := SessionStore

-- TypeScript: const defaultTTL = 3600 * 1000  (1 hour in ms)
def defaultTTL : Nat := 3600000

-- TypeScript: function createStore(): Store
def createStore : Store := SessionStore.empty

-- TypeScript: function setSession(store: Store, session: SessionData): Store
def setSession (store : Store) (s : SessionData) : Store := store.put s

-- TypeScript: function getSession(store : Store, tok: string): SessionData | null
def getSession (store : Store) (tok : SessionToken) : Option SessionData := store.get tok

-- TypeScript: function getFreshSession(store: Store, tok: string, now: number): SessionData | null
def getFreshSession (store : Store) (tok : SessionToken) (now : Nat) : Option SessionData :=
  store.getFresh tok now

-- TypeScript: function deleteSession(store: Store, tok: string): Store
def deleteSession (store : Store) (tok : SessionToken) : Store := store.delete tok

-- TypeScript: function isValid(store: Store, tok: string, now: number): boolean
def isValid (store : Store) (tok : SessionToken) (now : Nat) : Bool :=
  (store.getFresh tok now).isSome

-- TypeScript: function pruneExpired(store: Store, now: number): Store
def pruneExpired (store : Store) (now : Nat) : Store := store.prune now

-- Theorems about the generated session store

theorem createStore_get_none (tok : SessionToken) :
    getSession createStore tok = none := empty_get_none tok

theorem setSession_get (store : Store) (s : SessionData) :
    getSession (setSession store s) s.token = some s := put_then_get store s

theorem deleteSession_get_none (store : Store) (tok : SessionToken) :
    getSession (deleteSession store tok) tok = none := delete_then_get store tok

theorem isValid_of_fresh (store : Store) (tok : SessionToken) (now : Nat)
    (s : SessionData) (h : getFreshSession store tok now = some s) :
    isValid store tok now = true := by
  simp only [isValid, getFreshSession] at *
  rw [h]; simp

theorem not_isValid_of_deleted (store : Store) (tok : SessionToken) (now : Nat) :
    isValid (deleteSession store tok) tok now = false := by
  simp only [isValid, getFreshSession, deleteSession, SessionStore.getFresh]
  rw [delete_then_get]; simp

theorem setSession_preserves_other (store : Store) (s : SessionData) (tok : SessionToken)
    (hne : tok ≠ s.token) :
    getSession (setSession store s) tok = getSession store tok :=
  put_preserves_other store s tok hne

theorem getFreshSession_no_stale (store : Store) (tok : SessionToken) (now : Nat)
    (s : SessionData) (h : getFreshSession store tok now = some s) :
    s.isFresh now = true := get_fresh_implies_fresh store tok now s h

theorem deleteSession_then_set_get (store : Store) (s : SessionData) :
    getSession (setSession (deleteSession store s.token) s) s.token = some s :=
  setSession_get _ s

theorem isValid_false_after_delete (store : Store) (tok : SessionToken) (now : Nat) :
    isValid (deleteSession store tok) tok now = false :=
  not_isValid_of_deleted store tok now

theorem pruneExpired_removes_old (store : Store) (now : Nat) (tok : SessionToken)
    (s : SessionData) (h : (pruneExpired store now).get tok = some s) :
    s.isFresh now = true := prune_removes_expired store tok now s h

end TSLean.Generated.SessionStore
