-- TSLean.Tests
-- Executable test suite using #eval. Every test that passes prints nothing;
-- failures are caught by the `assert!` macro which aborts with an error.

import TSLean.Stdlib.HashMap
import TSLean.Stdlib.HashSet
import TSLean.Runtime.BrandedTypes
import TSLean.Runtime.Validation
import TSLean.DurableObjects.Queue
import TSLean.DurableObjects.RateLimiter
import TSLean.DurableObjects.Auth
import TSLean.DurableObjects.SessionStore
import TSLean.DurableObjects.Model

open TSLean TSLean.Stdlib.HashMap TSLean.DO

/-! ## HashMap (AssocMap) roundtrip tests -/

private def testAssocMap : IO Unit := do
  -- empty has no keys
  let m : AssocMap String Nat := AssocMap.empty
  assert! m.get? "a" == none
  assert! m.size == 0

  -- insert then lookup
  let m1 := m.insert "x" 42
  assert! m1.get? "x" == some 42
  assert! m1.get? "y" == none
  assert! m1.size == 1

  -- insert same key overwrites
  let m2 := m1.insert "x" 99
  assert! m2.get? "x" == some 99
  assert! m2.size == 1

  -- insert different key
  let m3 := m2.insert "y" 7
  assert! m3.get? "x" == some 99
  assert! m3.get? "y" == some 7

  -- erase
  let m4 := m3.erase "x"
  assert! m4.get? "x" == none
  assert! m4.get? "y" == some 7

  -- singleton
  let s := AssocMap.singleton "k" 1
  assert! s.get? "k" == some 1
  assert! s.size == 1

  IO.println "  ✓ AssocMap roundtrips"

#eval testAssocMap

/-! ## HashSet tests -/

open TSLean.Stdlib.HashSet in
private def testHashSet : IO Unit := do
  let s : TSHashSet String := TSHashSet.empty
  assert! s.contains "a" == false
  assert! s.size == 0

  let s1 := s.insert "hello"
  assert! s1.contains "hello" == true
  assert! s1.contains "world" == false
  assert! s1.size == 1

  -- insert duplicate is idempotent
  let s2 := s1.insert "hello"
  assert! s2.size == 1

  let s3 := s2.insert "world"
  assert! s3.size == 2
  assert! s3.contains "hello" == true
  assert! s3.contains "world" == true

  -- erase
  let s4 := s3.erase "hello"
  assert! s4.contains "hello" == false
  assert! s4.contains "world" == true

  IO.println "  ✓ HashSet operations"

#eval testHashSet

/-! ## BrandedTypes tests -/

private def testBrandedTypes : IO Unit := do
  -- smart constructors reject empty strings
  assert! UserId.mk' "" == none
  assert! RoomId.mk' "" == none
  assert! SessionToken.mk' "" == none
  assert! MessageId.mk' "" == none

  -- smart constructors accept non-empty strings
  assert! (UserId.mk' "alice").isSome
  assert! (RoomId.mk' "room-1").isSome
  assert! (SessionToken.mk' "tok_abc123").isSome

  -- equality
  let u1 := UserId.mk "alice"
  let u2 := UserId.mk "alice"
  let u3 := UserId.mk "bob"
  assert! u1 == u2
  assert! !(u1 == u3)

  -- Coe to String
  assert! (u1 : String) == "alice"

  IO.println "  ✓ BrandedTypes"

#eval testBrandedTypes

/-! ## Validation tests -/

open TSLean.Validation in
private def testValidation : IO Unit := do
  -- validLength
  assert! validLength "hello" 1 10 == true
  assert! validLength "" 1 10 == false
  assert! validLength "toolong" 1 3 == false

  -- nonEmpty
  assert! nonEmpty "x" == true
  assert! nonEmpty "" == false

  -- isAlphanumeric
  assert! isAlphanumeric "abc123" == true
  assert! isAlphanumeric "hello world" == false
  assert! isAlphanumeric "" == true -- vacuously

  -- isValidIdentifier
  assert! isValidIdentifier "myVar" == true
  assert! isValidIdentifier "_private" == true
  assert! isValidIdentifier "123bad" == false
  assert! isValidIdentifier "" == false

  -- isEmailLike
  assert! isEmailLike "a@b.c" == true
  assert! isEmailLike "user@domain.com" == true
  assert! isEmailLike "noatsign" == false
  assert! isEmailLike "@missing.local" == false

  -- isHexColor
  assert! isHexColor "#ff00aa" == true
  assert! isHexColor "#abc" == true
  assert! isHexColor "#xyz" == false
  assert! isHexColor "ff00aa" == false

  -- validators
  assert! (validateUserId "alice").isSome
  assert! (validateUserId "").isNone
  assert! (validateSessionToken "short").isNone
  assert! (validateSessionToken "0123456789abcdef").isSome

  IO.println "  ✓ Validation"

#eval testValidation

/-! ## DurableQueue model tests -/

open TSLean.DO.Queue in
private def testQueue : IO Unit := do
  let q0 := DurableQueue.empty
  assert! q0.total == 0
  assert! q0.pending.length == 0

  -- enqueue
  let q1 := q0.enqueue "msg1" 100
  assert! q1.total == 1
  assert! q1.pending.length == 1
  assert! q1.nextId == 1

  let q2 := q1.enqueue "msg2" 101
  assert! q2.total == 2
  assert! q2.nextId == 2

  -- deliver (FIFO)
  let (msg, q3) := q2.deliver
  assert! msg.isSome
  assert! (msg.map (·.payload)) == some "msg1"
  assert! q3.pending.length == 1
  assert! q3.inflight.length == 1
  assert! q3.total == 2

  -- ack removes from inflight
  let q4 := q3.ack 0
  assert! q4.inflight.length == 0
  assert! q4.total == 1

  -- empty deliver returns none
  let (msg2, _) := DurableQueue.empty.deliver
  assert! msg2.isNone

  IO.println "  ✓ DurableQueue model"

#eval testQueue

/-! ## RateLimiter model tests -/

open TSLean.DO.RateLimiter in
private def testRateLimiter : IO Unit := do
  let rl := RateLimiter.empty 1000 3
  assert! rl.isAllowed 100 == true
  assert! rl.countInWindow 100 == 0

  -- record events
  let rl1 := rl.record 100
  let rl2 := rl1.record 200
  let rl3 := rl2.record 300
  assert! rl3.countInWindow 500 == 3

  -- at limit: not allowed
  assert! rl3.isAllowed 500 == false

  -- tryAllow returns (false, _) when at limit
  let (allowed, _) := rl3.tryAllow 500
  assert! allowed == false

  -- after window expires, allowed again
  assert! rl3.isAllowed 1200 == true

  IO.println "  ✓ RateLimiter model"

#eval testRateLimiter

/-! ## Auth model tests -/

private def testAuth : IO Unit := do
  let store := Auth.AuthStore.empty
  let tok := SessionToken.mk "session_abc"
  let uid := UserId.mk "alice"
  let entry : Auth.SessionEntry := {
    userId := uid, token := tok, expiresAt := 1000, createdAt := 0
  }

  -- login
  let store1 := store.login entry
  assert! store1.lookup tok == some entry

  -- authenticate before expiry
  assert! (store1.authenticate tok 500).isSome

  -- authenticate after expiry
  assert! (store1.authenticate tok 1500).isNone

  -- isValid
  assert! store1.isValid tok 500 == true
  assert! store1.isValid tok 1500 == false

  -- logout
  let store2 := store1.logout tok
  assert! store2.lookup tok == none
  assert! store2.isValid tok 500 == false

  IO.println "  ✓ Auth model"

#eval testAuth

/-! ## Storage model tests -/

private def testStorage : IO Unit := do
  let s := DO.Storage.clear
  assert! s.get "key" == none

  let s1 := s.put "key" (.svStr "value")
  assert! s1.get "key" == some (.svStr "value")
  assert! s1.contains "key" == true

  -- overwrite
  let s2 := s1.put "key" (.svNum 42.0)
  assert! s2.get "key" == some (.svNum 42.0)

  -- delete
  let s3 := s2.delete "key"
  assert! s3.get "key" == none
  assert! s3.contains "key" == false

  -- different keys are independent
  let s4 := s1.put "other" (.svBool true)
  assert! s4.get "key" == some (.svStr "value")
  assert! s4.get "other" == some (.svBool true)

  IO.println "  ✓ Storage model"

#eval testStorage

/-! ## SessionStore model tests -/

open TSLean.DO.SessionStore in
private def testSessionStore : IO Unit := do
  let store := SessionStore.empty
  let tok := SessionToken.mk "sess_xyz"
  let uid := UserId.mk "bob"
  let sess : Session := {
    userId := uid, token := tok, data := [],
    createdAt := 0, expiresAt := 500
  }

  let store1 := store.put sess
  assert! store1.get tok == some sess

  -- getFresh before expiry
  assert! (store1.getFresh tok 100).isSome

  -- getFresh after expiry
  assert! (store1.getFresh tok 600).isNone

  -- delete
  let store2 := store1.delete tok
  assert! store2.get tok == none

  IO.println "  ✓ SessionStore model"

#eval testSessionStore

/-! ## Test runner -/

#eval IO.println "TSLean test suite: all tests passed."
