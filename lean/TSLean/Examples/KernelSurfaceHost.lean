/-!
# The host boundary, as nineteen store-passing reference implementations

`TSLean/LeanToTypeScript/Export.lean` writes a `foreign` declaration for each of the nineteen
constants in the `TSLean.LeanToTypeScript.Host` namespace, carrying the host wire spelling, the
erased parameter list, the result type and this body as the reference the substrate has to agree
with. The agreement itself is the named premise `Preservation.HostAgrees`, never an axiom: nothing
here claims the substrate computes this, only what it would have to compute.

The calling convention is surface §4: the parameters are the payloads and then the store, and the
result is a pair of reply and store. The store is `List (String × String)` because that is a form
the surface carries with the operations these bodies need — the substrate's own payloads are
`ByteArray`, and `bytes` has no opcode row in v6, so a reference body that computed with one would
have no emitted form to be proved against.
-/

namespace TSLean.Examples.HostSupport

/-- The entries whose key matches, which is what a keyed read and a keyed delete both decide. -/
def matching (key : String) (store : List (String × String)) : List (String × String) :=
  store.filter fun entry => entry.fst == key

/-- The value stored at a key, and none when the store holds no entry for it. -/
def lookup (key : String) (store : List (String × String)) : Option String :=
  match (matching key store).head? with
  | some entry => some entry.snd
  | none => none

/-- The store without the entries at a key, which is what makes a write idempotent. -/
def without (key : String) (store : List (String × String)) : List (String × String) :=
  store.filter fun entry => !(entry.fst == key)

/-- Every key the store holds, in entry order. -/
def keys (store : List (String × String)) : List String :=
  store.map fun entry => entry.fst

/-- The letters after an offset. Structural recursion on the list, which is the discipline the
exporter records for it. -/
def afterLetters (offset : Nat) (source : List Char) : List Char :=
  match source with
  | [] => []
  | letter :: rest => if offset = 0 then letter :: rest else afterLetters (offset - 1) rest

/-- The first `span` letters of a list. -/
def firstLetters (span : Nat) (source : List Char) : List Char :=
  match source with
  | [] => []
  | letter :: rest => if span = 0 then [] else letter :: firstLetters (span - 1) rest

/-- Whether a write changed the store, decided by the entry count rather than by comparing
stores, because the emitted comparison of two lists would need an element equality the surface
does not carry at `pair`. -/
def changed (before after : List (String × String)) : Bool :=
  !(before.length == after.length)

end TSLean.Examples.HostSupport

namespace TSLean.LeanToTypeScript.Host

open TSLean.Examples.HostSupport

/-- `host.store.get`: the value at a key, with the store threaded unchanged. -/
def storeGet (key : String) (store : List (String × String)) :
    Option String × List (String × String) :=
  (lookup key store, store)

/-- `host.store.put`: one entry written at a key, replacing whatever the key held. -/
def storePut (key : String) (value : String) (store : List (String × String)) :
    Nat × List (String × String) :=
  let written := (key, value) :: without key store
  (written.length, written)

/-- `host.store.delete`: the entries at a key removed, and whether anything was. -/
def storeDelete (key : String) (store : List (String × String)) :
    Bool × List (String × String) :=
  let remaining := without key store
  (changed store remaining, remaining)

/-- `host.store.list`: every key the store holds. -/
def storeList (store : List (String × String)) :
    List String × List (String × String) :=
  (keys store, store)

/-- `host.store.txn`: a batch of writes applied ahead of the entries they shadow. -/
def storeTxn (writes : List (String × String)) (store : List (String × String)) :
    Nat × List (String × String) :=
  (writes.length, writes ++ store)

/-- `host.alarm.set`: the alarm entry written, and the time it was set for. -/
def alarmSet (scheduled : Nat) (store : List (String × String)) :
    Nat × List (String × String) :=
  (scheduled, ("alarm", "set") :: without "alarm" store)

/-- `host.alarm.get`: whether an alarm is set. -/
def alarmGet (store : List (String × String)) :
    Option String × List (String × String) :=
  (lookup "alarm" store, store)

/-- `host.alarm.delete`: the alarm entry removed, and whether one was set. -/
def alarmDelete (store : List (String × String)) : Bool × List (String × String) :=
  let remaining := without "alarm" store
  (changed store remaining, remaining)

/-- `host.content.put`: a body written at a key, answering the code-point count written. -/
def contentPut (key : String) (body : String) (store : List (String × String)) :
    Nat × List (String × String) :=
  (body.length, (key, body) :: without key store)

/-- `host.content.get`: the body at a key. -/
def contentGet (key : String) (store : List (String × String)) :
    Option String × List (String × String) :=
  (lookup key store, store)

/-- `host.content.head`: whether a key holds a body, without reading it. -/
def contentHead (key : String) (store : List (String × String)) :
    Bool × List (String × String) :=
  (!(matching key store).isEmpty, store)

/-- `host.content.range`: the code points of a body between an offset and a span. The range is
taken over the code-point list, because a String position is a UTF-8 byte offset and is outside
the surface for that reason. -/
def contentRange (key : String) (offset : Nat) (span : Nat) (store : List (String × String)) :
    Option String × List (String × String) :=
  (match lookup key store with
    | some body => some (String.ofList (firstLetters span (afterLetters offset body.toList)))
    | none => none,
   store)

/-- `host.queue.send`: a message appended, answering the depth after the send. -/
def queueSend (message : String) (store : List (String × String)) :
    Nat × List (String × String) :=
  let queued := ("queue", message) :: store
  (queued.length, queued)

/-- `host.queue.ack`: the entry at an identifier removed, and whether it was there to remove. -/
def queueAck (identifier : String) (store : List (String × String)) :
    Bool × List (String × String) :=
  let remaining := without identifier store
  (changed store remaining, remaining)

/-- `host.queue.retry`: the entry at an identifier marked for retry, answering the delay. -/
def queueRetry (identifier : String) (delay : Nat) (store : List (String × String)) :
    Nat × List (String × String) :=
  (delay, (identifier, "retry") :: without identifier store)

/-- `host.isolate.load`: a module recorded as loaded, and whether it was nameable. -/
def isolateLoad (moduleName : String) (store : List (String × String)) :
    Bool × List (String × String) :=
  (!moduleName.isEmpty, (moduleName, "loaded") :: without moduleName store)

/-- `host.isolate.call`: the argument echoed when the module was loaded, and none otherwise. -/
def isolateCall (moduleName : String) (argument : String) (store : List (String × String)) :
    Option String × List (String × String) :=
  (match lookup moduleName store with
    | some _ => some argument
    | none => none,
   store)

/-- `host.rpc.call`: the payload echoed to a target that has a stub, and none otherwise. -/
def rpcCall (target : String) (payload : String) (store : List (String × String)) :
    Option String × List (String × String) :=
  (match lookup target store with
    | some _ => some payload
    | none => none,
   store)

/-- `host.rpc.dispose`: a target's stub released, and whether one was held. -/
def rpcDispose (target : String) (store : List (String × String)) :
    Bool × List (String × String) :=
  let remaining := without target store
  (changed store remaining, remaining)

end TSLean.LeanToTypeScript.Host
