import TSLean.Lcnf.Tests.Extract.Harness
import TSLean.Examples.Roundtrip.Traffic
import TSLean.Examples.Roundtrip.Priority
import TSLean.Examples.Roundtrip.Invariant
import Std.Data.HashMap

/-!
# Golden closures for the mono-LCNF extractor (M1)

Each golden prints the closure (canonical code-declaration names, extern leaves with their
attribute data, constructor leaves, `implemented_by` pairs, `safe=false` declarations and
refusals). It then round-trips every raw and every canonical declaration through JSON and prints
each root's canonical digest. `#guard_msgs` pins the whole output, so any drift fails the build.
-/

open Lean Elab Command Compiler LCNF TSLean.Lcnf TSLean.Lcnf.Tests.Extract

/-! ## SHA-256 known-answer vectors (FIPS 180-2) -/

#guard Canon.sha256Str "" == "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
#guard Canon.sha256Str "abc" == "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
#guard Canon.sha256Str "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq" ==
  "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"

/-! ## The probe program: 5 code declarations, 5 `Nat` externs, 4 constructors -/

namespace GoldenProbe
structure Order where
  id : Nat
  qty : Nat
  price : Nat

def total (os : List Order) : Nat := os.foldl (fun acc o => acc + o.qty * o.price) 0

def firstBig (os : List Order) : Nat :=
  match os.find? (fun o => o.qty > 10) with
  | some o => o.id
  | none => 0

def countdown : Nat → List Nat
  | 0 => [0]
  | n + 1 => (n + 1) :: countdown n
end GoldenProbe

/--
info: roots: GoldenProbe.total, GoldenProbe.firstBig, GoldenProbe.countdown
code decls (5):
  GoldenProbe.total
  GoldenProbe.firstBig
  GoldenProbe.countdown
  List.foldl._lcnf_6c0d550bc0e622a9
  List.find?._lcnf_4069f95042e54cac
externs (5):
  Nat.decEq/2 [standard all lean_nat_dec_eq]
  Nat.sub/2 [standard all lean_nat_sub]
  Nat.add/2 [standard all lean_nat_add]
  Nat.mul/2 [standard all lean_nat_mul]
  Nat.decLt/2 [standard all lean_nat_dec_lt]
opaque externs (0):
ctors (4):
  List.nil (List #0, 1+0)
  List.cons (List #1, 1+2)
  Option.none (Option #0, 1+0)
  Option.some (Option #1, 1+1)
implemented_by (0):
safe=false (0):
over-applications (0):
erased lets (0):
partial ctors (0):
refusals (0):
round-trip: 5 raw and 5 canonical declarations
digest GoldenProbe.total: 638d6bc885a69c0818ca92ff08bff2a4f8c5afaf889cdb7b88c20a3f44efd76c
digest GoldenProbe.firstBig: 70eb6052b6c8f56686615c10b0fd4d56c5fcdc9260adbe1e6c08665520e802ab
digest GoldenProbe.countdown: efa7849f793a1530efce2096c815fdb2447794855fbb0fa8cdb023f5812ec25e
-/
#guard_msgs in
#eval golden #[``GoldenProbe.total, ``GoldenProbe.firstBig, ``GoldenProbe.countdown]

/-! ## `step` from p4c: effects as data -/

namespace GoldenStep
inductive Command where
  | fetch (id : Nat) (url : String)
  | storagePut (k v : String)

inductive Event where
  | start (now : Nat)
  | fetched (id : Nat) (status : Nat) (body : String)

structure St where
  pending : List Nat := []
  lastNow : Nat := 0

def step (st : St) : Event → St × List Command
  | .start now => ({ st with lastNow := now, pending := [1] }, [.fetch 1 "https://example.test"])
  | .fetched id status body =>
    ({ st with pending := st.pending.filter (· ≠ id) }, if status == 200 then [.storagePut "k" body] else [])
end GoldenStep

/--
info: roots: GoldenStep.step
code decls (4):
  GoldenStep.step
  List.filterTR.loop._lcnf_d252058044c93029
  List.reverse._lcnf_092e97308b17464f
  List.reverseAux._lcnf_0b89f70bab121710
externs (1):
  Nat.decEq/2 [standard all lean_nat_dec_eq]
opaque externs (0):
ctors (6):
  List.nil (List #0, 1+0)
  List.cons (List #1, 1+2)
  GoldenStep.St.mk (GoldenStep.St #0, 0+2)
  GoldenStep.Command.fetch (GoldenStep.Command #0, 0+2)
  Prod.mk (Prod #0, 2+2)
  GoldenStep.Command.storagePut (GoldenStep.Command #1, 0+2)
implemented_by (0):
safe=false (0):
over-applications (0):
erased lets (0):
partial ctors (0):
refusals (0):
round-trip: 4 raw and 4 canonical declarations
digest GoldenStep.step: 92565db6cb6b9350b6b59b1df4b3afe449f3fe0c05061eec31574a1899781675
-/
#guard_msgs in
#eval golden #[``GoldenStep.step]

/-! ## `HashMap`: `String.hash` is a pure opaque extern, handed to the primitive table (M3) -/

namespace GoldenHashMap
def hmInsert (m : Std.HashMap String Nat) (k : String) : Std.HashMap String Nat := m.insert k 1
def hmToList (m : Std.HashMap String Nat) : List (String × Nat) := m.toList
def hmNat (m : Std.HashMap Nat Nat) (k : Nat) : Option Nat := m.get? k
end GoldenHashMap

/--
info: roots: GoldenHashMap.hmInsert, GoldenHashMap.hmToList, GoldenHashMap.hmNat
code decls (13):
  GoldenHashMap.hmInsert
  GoldenHashMap.hmToList
  GoldenHashMap.hmNat
  Std.DHashMap.Internal.Raw₀.insert._lcnf_d60f51a592379062
  Array.foldrMUnsafe.fold._lcnf_70dcc3772ef0e84f
  Std.DHashMap.Internal.Raw₀.Const.get?._lcnf_a814700579574d56
  Std.DHashMap.Internal.AssocList.contains._lcnf_b8629ca429e948b5
  Std.DHashMap.Internal.Raw₀.expand._lcnf_bc108d99ff212fc5
  Std.DHashMap.Internal.AssocList.replace._lcnf_7809f32a2d0aa7c1
  Std.DHashMap.Internal.AssocList.foldrM._lcnf_bb525bf65f18633d
  Std.DHashMap.Internal.AssocList.get?._lcnf_d1deb3c595f50a3b
  Std.DHashMap.Internal.Raw₀.expand.go._lcnf_428ddbc8a0b5c947
  Std.DHashMap.Internal.AssocList.foldlM._lcnf_d6b14431a812f219
externs (21):
  Array.size/2 [standard all lean_array_get_size]
  Nat.decLt/2 [standard all lean_nat_dec_lt]
  USize.ofNat/1 [standard all lean_usize_of_nat]
  UInt64.shiftRight/2 [standard all lean_uint64_shift_right]
  UInt64.xor/2 [standard all lean_uint64_xor]
  UInt64.toUSize/1 [standard all lean_uint64_to_usize]
  USize.sub/2 [standard all lean_usize_sub]
  USize.land/2 [standard all lean_usize_land]
  Array.uget/4 [standard all lean_array_uget]
  Nat.add/2 [standard all lean_nat_add]
  Array.uset/5 [standard all lean_array_uset]
  Nat.mul/2 [standard all lean_nat_mul]
  Nat.div/2 [standard all lean_nat_div]
  Nat.decLe/2 [standard all lean_nat_dec_le]
  USize.decEq/2 [standard all lean_usize_dec_eq]
  UInt64.ofNat/1 [standard all lean_uint64_of_nat]
  String.decEq/2 [standard all lean_string_dec_eq]
  Array.replicate/3 [standard all lean_mk_array]
  Nat.decEq/2 [standard all lean_nat_dec_eq]
  Array.getInternal/4 [standard all lean_array_fget]
  Array.set/5 [standard all lean_array_fset]
opaque externs (1):
  String.hash/1 [standard all lean_string_hash] pure
ctors (9):
  List.nil (List #0, 1+0)
  Std.DHashMap.Internal.AssocList.cons (Std.DHashMap.Internal.AssocList #1, 2+3)
  Std.DHashMap.Raw.mk (Std.DHashMap.Raw #0, 2+2)
  Std.DHashMap.Internal.AssocList.nil (Std.DHashMap.Internal.AssocList #0, 2+0)
  Bool.false (Bool #0, 0+0)
  Prod.mk (Prod #0, 2+2)
  List.cons (List #1, 1+2)
  Option.none (Option #0, 1+0)
  Option.some (Option #1, 1+1)
implemented_by (1):
  Array.foldrM -> Array.foldrMUnsafe via Array.foldrMUnsafe.fold._lcnf_70dcc3772ef0e84f
safe=false (1):
  Array.foldrMUnsafe.fold._lcnf_70dcc3772ef0e84f
over-applications (0):
erased lets (0):
partial ctors (0):
refusals (1):
  lcnf.extract.requires-primitive-table-entry: String.hash is a pure opaque extern and requires a primitive-table entry
round-trip: 13 raw and 13 canonical declarations
digest GoldenHashMap.hmInsert: cb508e4d9ac8422a5af8bc8a2ba36b5fa34e6cc7ac48ea6cc53bdc92cc4087b7
digest GoldenHashMap.hmToList: 3b7351b29a32d4695daa38c138b55fd417e7a6dd0784e6d9756eab23919e977b
digest GoldenHashMap.hmNat: 1bc1ec0f3f44057a3ce4adb2d5b2166aaf5c0b7e1b8789703d115318f87ddde7
-/
#guard_msgs in
#eval golden #[``GoldenHashMap.hmInsert, ``GoldenHashMap.hmToList, ``GoldenHashMap.hmNat]

/-! ## Roundtrip corpus: Traffic, Priority (both with `cases` default alternatives), Invariant -/

/--
info: roots: TSLean.Examples.Roundtrip.Traffic.next, TSLean.Examples.Roundtrip.Traffic.mayCross
code decls (2):
  TSLean.Examples.Roundtrip.Traffic.next
  TSLean.Examples.Roundtrip.Traffic.mayCross
externs (0):
opaque externs (0):
ctors (5):
  TSLean.Examples.Roundtrip.Traffic.Light.green (TSLean.Examples.Roundtrip.Traffic.Light #2, 0+0)
  TSLean.Examples.Roundtrip.Traffic.Light.red (TSLean.Examples.Roundtrip.Traffic.Light #0, 0+0)
  TSLean.Examples.Roundtrip.Traffic.Light.amber (TSLean.Examples.Roundtrip.Traffic.Light #1, 0+0)
  Bool.true (Bool #1, 0+0)
  Bool.false (Bool #0, 0+0)
implemented_by (0):
safe=false (0):
over-applications (0):
erased lets (0):
partial ctors (0):
refusals (0):
round-trip: 2 raw and 2 canonical declarations
digest TSLean.Examples.Roundtrip.Traffic.next: 6c06fd16b48c01c6c0fb1fe83f68b1d2328c64783c2c26b1ab51caab2c357f9d
digest TSLean.Examples.Roundtrip.Traffic.mayCross: 529fef2716a21a3df02a6c8292b74aca53f0a59e6508946961bab0667532ecc3
-/
#guard_msgs in
#eval golden #[``TSLean.Examples.Roundtrip.Traffic.next, ``TSLean.Examples.Roundtrip.Traffic.mayCross]

/--
info: roots: TSLean.Examples.Roundtrip.Priority.before
code decls (1):
  TSLean.Examples.Roundtrip.Priority.before
externs (0):
opaque externs (0):
ctors (2):
  Bool.false (Bool #0, 0+0)
  Bool.true (Bool #1, 0+0)
implemented_by (0):
safe=false (0):
over-applications (0):
erased lets (0):
partial ctors (0):
refusals (0):
round-trip: 1 raw and 1 canonical declarations
digest TSLean.Examples.Roundtrip.Priority.before: 333ec1a36462f1317f0cdbaa4ba418623dbda16950c6b3a13d690fbc48db7468
-/
#guard_msgs in
#eval golden #[``TSLean.Examples.Roundtrip.Priority.before]

/--
info: roots: TSLean.Examples.Roundtrip.Invariant.build, TSLean.Examples.Roundtrip.Invariant.widenedFrom, TSLean.Examples.Roundtrip.Invariant.widthAfterWidening, TSLean.Examples.Roundtrip.Invariant.shutGateOpened, TSLean.Examples.Roundtrip.Invariant.emptyTallySize, TSLean.Examples.Roundtrip.Invariant.room
code decls (10):
  TSLean.Examples.Roundtrip.Invariant.build
  TSLean.Examples.Roundtrip.Invariant.widenedFrom
  TSLean.Examples.Roundtrip.Invariant.widthAfterWidening
  TSLean.Examples.Roundtrip.Invariant.shutGateOpened
  TSLean.Examples.Roundtrip.Invariant.emptyTallySize
  TSLean.Examples.Roundtrip.Invariant.room
  TSLean.Examples.Roundtrip.Invariant.widened
  TSLean.Examples.Roundtrip.Invariant.shutGate
  List.lengthTR._lcnf_206421b7ff1f32a5
  List.lengthTRAux._lcnf_a55d7f5c4ae331d9
externs (3):
  Nat.add/2 [standard all lean_nat_add]
  Nat.decLe/2 [standard all lean_nat_dec_le]
  Nat.sub/2 [standard all lean_nat_sub]
opaque externs (0):
ctors (6):
  Option.none (Option #0, 1+0)
  TSLean.Examples.Roundtrip.Invariant.Window.mk (TSLean.Examples.Roundtrip.Invariant.Window #0, 0+3)
  Option.some (Option #1, 1+1)
  Bool.false (Bool #0, 0+0)
  List.nil (List #0, 1+0)
  TSLean.Examples.Roundtrip.Invariant.Gate.mk (TSLean.Examples.Roundtrip.Invariant.Gate #0, 0+3)
implemented_by (0):
safe=false (0):
over-applications (0):
erased lets (0):
partial ctors (0):
refusals (0):
round-trip: 10 raw and 10 canonical declarations
digest TSLean.Examples.Roundtrip.Invariant.build: 0bbc4656e4d03debdc4020b67db6ef93f9234a66db29be856e00fca7a8c6830d
digest TSLean.Examples.Roundtrip.Invariant.widenedFrom: 8894302b9cd7eb51b429f4194649e6ded3f3b54c11b0ceecd304fa66bb0ed40e
digest TSLean.Examples.Roundtrip.Invariant.widthAfterWidening: 2c638bcb8c0e76b888a2fa597321c0712d6bc38666232f210d2a4249edba7db4
digest TSLean.Examples.Roundtrip.Invariant.shutGateOpened: 04268a68dbbcc2e3425ae2d733cb96db4cad7a72be8091e407a82e0afa4e3985
digest TSLean.Examples.Roundtrip.Invariant.emptyTallySize: d27bb2f89c134e3607e028735a6a0cc763986d79915db3616f35eedb14688769
digest TSLean.Examples.Roundtrip.Invariant.room: c484764efe27c02256db590b758478a3f40fd90f11a3296c32f08e180ed8a452
-/
#guard_msgs in
#eval golden #[``TSLean.Examples.Roundtrip.Invariant.build,
  ``TSLean.Examples.Roundtrip.Invariant.widenedFrom,
  ``TSLean.Examples.Roundtrip.Invariant.widthAfterWidening,
  ``TSLean.Examples.Roundtrip.Invariant.shutGateOpened,
  ``TSLean.Examples.Roundtrip.Invariant.emptyTallySize,
  ``TSLean.Examples.Roundtrip.Invariant.room]

/-! ## `implemented_by`: the stdlib pair behind `Array.map`, and a user pair -/

namespace GoldenImpl
def incAll (a : Array Nat) : Array Nat := a.map (· + 1)

def implSide (n : Nat) : Nat := n + 1000
@[implemented_by implSide] def refSide (n : Nat) : Nat := n
def useRef (n : Nat) : Nat := refSide n
end GoldenImpl

/--
info: roots: GoldenImpl.incAll
code decls (2):
  GoldenImpl.incAll
  Array.mapMUnsafe.map._lcnf_c52100d05bbeed36
externs (6):
  Array.usize/2 [standard all lean_array_size]
  USize.decLt/2 [standard all lean_usize_dec_lt]
  Array.uget/4 [standard all lean_array_uget]
  Array.uset/5 [standard all lean_array_uset]
  Nat.add/2 [standard all lean_nat_add]
  USize.add/2 [standard all lean_usize_add]
opaque externs (0):
ctors (0):
implemented_by (1):
  Array.mapM -> Array.mapMUnsafe via Array.mapMUnsafe.map._lcnf_c52100d05bbeed36
safe=false (1):
  Array.mapMUnsafe.map._lcnf_c52100d05bbeed36
over-applications (0):
erased lets (0):
partial ctors (0):
refusals (0):
round-trip: 2 raw and 2 canonical declarations
digest GoldenImpl.incAll: ae5f43428660d707d4fe13e3868cf2b05ed5e9edd109d40a791c2d2742e7b5b1
-/
#guard_msgs in
#eval golden #[``GoldenImpl.incAll]

/--
info: roots: GoldenImpl.useRef
code decls (2):
  GoldenImpl.useRef
  GoldenImpl.implSide
externs (1):
  Nat.add/2 [standard all lean_nat_add]
opaque externs (0):
ctors (0):
implemented_by (1):
  GoldenImpl.refSide -> GoldenImpl.implSide via GoldenImpl.implSide
safe=false (0):
over-applications (0):
erased lets (0):
partial ctors (0):
refusals (0):
round-trip: 2 raw and 2 canonical declarations
digest GoldenImpl.useRef: 76b260479f7168308e171d5898f576fa076f1360089850935476651c7cc93ea4
-/
#guard_msgs in
#eval golden #[``GoldenImpl.useRef]

/-! ## Refused: `IO` programs (world tokens and effectful opaque externs) -/

namespace GoldenIO
def nowMs : IO Nat := IO.monoMsNow
end GoldenIO

/--
info: roots: GoldenIO.nowMs
code decls (1):
  GoldenIO.nowMs
externs (0):
opaque externs (1):
  IO.monoMsNow/1 [standard all lean_io_mono_ms_now] effectful
ctors (1):
  EST.Out.ok (EST.Out #0, 3+2)
implemented_by (0):
safe=false (0):
over-applications (0):
erased lets (0):
partial ctors (0):
refusals (3):
  lcnf.extract.world-token: GoldenIO.nowMs mentions the world token lcVoid; effects are data at the root
  lcnf.extract.world-token: GoldenIO.nowMs mentions the world token EST.Out; effects are data at the root
  lcnf.extract.effectful-extern: IO.monoMsNow is an opaque extern over a world token; effects are data at the root
round-trip: 1 raw and 1 canonical declarations
digest GoldenIO.nowMs: f3b22e7ae066e58bd7a0f866ddfabb5840f45352c17e43ff63442316360f5c8b
-/
#guard_msgs in
#eval golden #[``GoldenIO.nowMs]

/-! ## Closures: `borrowed` metadata in mono types, and over-application of a constant

A let-bound partial application of an `@&` extern (`Nat.add`, `Nat.mul`) has a mono type that
carries `[mdata borrowed:1 Nat]`. The codec carries that metadata, so both declarations round-trip
at plain equality. `konst Nat.mul 0 x y` is `konst._redArg _x.1 x y` in mono: arity 1, three
arguments. It is admitted and listed under `over-applications`. -/

namespace GoldenClosures
def curry3 (a b c : Nat) : Nat := a * 100 + b * 10 + c

@[noinline] def konst {α : Type} (a : α) (_n : Nat) : α := a

@[noinline] def fns (k : Nat) : List (Nat → Nat → Nat → Nat) :=
  [konst Nat.add, konst (curry3 k), curry3, fun a b c => a + b + c + k]

structure Box where
  f : Nat → Nat → Nat

@[noinline] def boxes (k : Nat) : List Box :=
  [⟨Nat.add⟩, ⟨Nat.mul⟩, ⟨curry3 k⟩, ⟨fun a b => if a == 0 then 100 - b else a + b⟩]

def constOver (x y : Nat) : Nat := konst Nat.mul 0 x y
end GoldenClosures

/--
info: roots: GoldenClosures.fns
code decls (5):
  GoldenClosures.fns
  GoldenClosures.fns._lcnf_944b7ea2a70dadce
  GoldenClosures.konst
  GoldenClosures.curry3
  GoldenClosures.konst._lcnf_5a04ff138329a080
externs (2):
  Nat.add/2 [standard all lean_nat_add]
  Nat.mul/2 [standard all lean_nat_mul]
opaque externs (0):
ctors (2):
  List.nil (List #0, 1+0)
  List.cons (List #1, 1+2)
implemented_by (0):
safe=false (0):
over-applications (0):
erased lets (0):
partial ctors (0):
refusals (0):
round-trip: 5 raw and 5 canonical declarations
digest GoldenClosures.fns: 21da8f2877b44f39129d5e6711ee2bf7fc7189f28b12a2f20a80de8e9df8d830
-/
#guard_msgs in
#eval golden #[``GoldenClosures.fns]

/--
info: roots: GoldenClosures.boxes
code decls (3):
  GoldenClosures.boxes
  GoldenClosures.boxes._lcnf_bb5e8afb45fad2d3
  GoldenClosures.curry3
externs (4):
  Nat.add/2 [standard all lean_nat_add]
  Nat.mul/2 [standard all lean_nat_mul]
  Nat.decEq/2 [standard all lean_nat_dec_eq]
  Nat.sub/2 [standard all lean_nat_sub]
opaque externs (0):
ctors (2):
  List.nil (List #0, 1+0)
  List.cons (List #1, 1+2)
implemented_by (0):
safe=false (0):
over-applications (0):
erased lets (0):
partial ctors (0):
refusals (0):
round-trip: 3 raw and 3 canonical declarations
digest GoldenClosures.boxes: db3993169464c027903576ddcf15d7bd256458632543f4525edf7f9b8441c560
-/
#guard_msgs in
#eval golden #[``GoldenClosures.boxes]

/--
info: roots: GoldenClosures.constOver
code decls (2):
  GoldenClosures.constOver
  GoldenClosures.konst._lcnf_5a04ff138329a080
externs (1):
  Nat.mul/2 [standard all lean_nat_mul]
opaque externs (0):
ctors (0):
implemented_by (0):
safe=false (0):
over-applications (1):
  GoldenClosures.constOver: GoldenClosures.konst._lcnf_5a04ff138329a080 takes 1, applied to 3
erased lets (0):
partial ctors (0):
refusals (0):
round-trip: 2 raw and 2 canonical declarations
digest GoldenClosures.constOver: 5eedcfaae171b58990ae25af9c722bc4279ff9c00d8ef57b01d9aa94e538e8db
-/
#guard_msgs in
#eval golden #[``GoldenClosures.constOver]

/- Reached, not just present: the closures above really carry `mdata` in their mono types. If Lean
stops emitting it, this count changes and the goldens above no longer test the codec's mdata path. -/
/--
info: GoldenClosures.fns: 1 carried Exprs contain mdata, e.g. (some ([mdata borrowed:1 Nat]) -> ([mdata borrowed:1 Nat]) -> Nat)
GoldenClosures.boxes: 2 carried Exprs contain mdata, e.g. (some ([mdata borrowed:1 Nat]) -> ([mdata borrowed:1 Nat]) -> Nat)
GoldenClosures.constOver: 1 carried Exprs contain mdata, e.g. (some ([mdata borrowed:1 Nat]) -> ([mdata borrowed:1 Nat]) -> Nat)
-/
#guard_msgs in
#eval show CommandElabM Unit from liftCoreM do
  for root in #[``GoldenClosures.fns, ``GoldenClosures.boxes, ``GoldenClosures.constOver] do
    let c ← Extract.closure #[root]
    let es := c.decls.flatMap Serialize.declExprs
    let md := es.filter fun e => (e.find? (·.isMData)).isSome
    IO.println s!"{root}: {md.size} carried Exprs contain mdata, e.g. {md[0]?}"

/-! ## Erased lets and partial constructor applications, from real stdlib declarations

The census of imported mono found 124 erased lets and 20 partial constructor applications. Both
goldens below are declarations the census found. `boolToProp` is `let _x.1 : lcErased := ◾`.
`instNatCastInt` is `Int.ofNat` taken as a closure. -/

/--
info: roots: boolToProp
code decls (1):
  boolToProp
externs (0):
opaque externs (0):
ctors (0):
implemented_by (0):
safe=false (0):
over-applications (0):
erased lets (1):
  boolToProp: let _x.1
partial ctors (0):
refusals (0):
round-trip: 1 raw and 1 canonical declarations
digest boolToProp: 7c56ecf4e1bf20c310ebc32cc9a6482dd5329c1ebafa0879fc49d6cf16cecd9f
-/
#guard_msgs in
#eval golden #[``boolToProp]

/--
info: roots: instNatCastInt
code decls (1):
  instNatCastInt
externs (1):
  Int.ofNat/1 [standard all lean_nat_to_int]
opaque externs (0):
ctors (0):
implemented_by (0):
safe=false (0):
over-applications (0):
erased lets (0):
partial ctors (1):
  instNatCastInt: Int.ofNat takes 1, applied to 0
refusals (0):
round-trip: 1 raw and 1 canonical declarations
digest instNatCastInt: 5d818ae8e6eb84127ebb216bb298b9b1a146f6e055faf77e1659988106ff096a
-/
#guard_msgs in
#eval golden #[``instNatCastInt]

/-! ## Refusal controls: unsupported forms, planted as mono declarations

User code does not produce these forms, so each is planted: a hand-built declaration saved into
the mono extension, or a base-phase body (which has `fun` and `proj`) saved as mono. The planted
declaration also contains three admitted forms, which are listed: an over-application of a code
declaration (`Nat.add x x x`), an erased let and a partial constructor application. -/

namespace GoldenPlant
def fv (i : Nat) : FVarId := ⟨.num `_plant i⟩
def natTy : Expr := .const ``Nat []

/-- `x ↦ fun f y := return y; let a := Nat.add x x x; let b := ◾; let c := x; let d := List.cons ◾;
let e := List.nil ◾ x; return a` -/
def formsDecl : Decl .pure :=
  let lets : List (LetDecl .pure) := [
    { fvarId := fv 1, binderName := `a, type := natTy,
      value := .const ``Nat.add [] #[.fvar (fv 0), .fvar (fv 0), .fvar (fv 0)] },
    { fvarId := fv 2, binderName := `b, type := natTy, value := .erased },
    { fvarId := fv 3, binderName := `c, type := natTy, value := .fvar (fv 0) #[] },
    { fvarId := fv 4, binderName := `d, type := natTy, value := .const ``List.cons [.zero] #[.erased] },
    { fvarId := fv 7, binderName := `e, type := natTy,
      value := .const ``List.nil [.zero] #[.erased, .fvar (fv 0)] }]
  { name := `GoldenPlant.forms, levelParams := [], type := natTy,
    params := #[{ fvarId := fv 0, binderName := `x, type := natTy, borrow := false }],
    value := .code (.fun (.mk (fv 5) `f #[{ fvarId := fv 6, binderName := `y, type := natTy, borrow := false }]
        natTy (.return (fv 6))) (lets.foldr (fun d k => .let d k) (.return (fv 1)))),
    inlineAttr? := none }

/-- A mono value of `extern [opaque]` without an `@[extern]` attribute: what the exported olean
level shows for a hidden body. -/
def hiddenDecl : Decl .pure :=
  { name := `GoldenPlant.hidden, levelParams := [], type := natTy, params := #[],
    value := .extern { entries := [.opaque] }, inlineAttr? := none }
end GoldenPlant

/--
info: #[GoldenPlant.forms]: #[lcnf.extract.unsupported-form: GoldenPlant.forms contains `fun` (local function f), a form the pipeline does not lower, lcnf.extract.unsupported-form: GoldenPlant.forms contains `fvar-alias` (let c), a form the pipeline does not lower, lcnf.extract.unsupported-form: GoldenPlant.forms contains `ctor-over-application` (List.nil takes 1, applied to 2), a form the pipeline does not lower]
  admitted over-application in GoldenPlant.forms: Nat.add takes 2, applied to 3
  admitted erased let in GoldenPlant.forms: let b
  admitted partial ctor in GoldenPlant.forms: List.cons takes 3, applied to 1
#[GoldenPlant.hidden]: #[lcnf.extract.extern-opaque: GoldenPlant.hidden is `extern [opaque]`; its mono body is not available at this olean level]
#[GoldenPlant.baseFirstBig]: #[lcnf.extract.unsupported-form: GoldenPlant.baseFirstBig contains `proj` (GoldenProbe.Order.0), a form the pipeline does not lower]
#[Nat.rec]: #[lcnf.extract.no-mono-decl: Nat.rec (recursor) has no mono declaration and is not a constructor]
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  liftCoreM do
    GoldenPlant.formsDecl.saveMono
    GoldenPlant.hiddenDecl.saveMono
    let some base ← getDeclAt? ``GoldenProbe.firstBig .base | throwError "no base decl"
    { base with name := `GoldenPlant.baseFirstBig }.saveMono
  for roots in #[#[`GoldenPlant.forms], #[`GoldenPlant.hidden], #[`GoldenPlant.baseFirstBig],
                 #[``Nat.rec]] do
    let c ← liftCoreM (Extract.closure roots)
    IO.println s!"{roots}: {c.refusals.map (·.message)}"
    for o in c.overApplications do
      IO.println s!"  admitted over-application in {o.decl}: {o.callee} takes {o.arity}, applied to {o.args}"
    for e in c.erasedLets do IO.println s!"  admitted erased let in {e.decl}: let {e.binder}"
    for p in c.partialCtors do
      IO.println s!"  admitted partial ctor in {p.decl}: {p.ctor} takes {p.arity}, applied to {p.args}"
