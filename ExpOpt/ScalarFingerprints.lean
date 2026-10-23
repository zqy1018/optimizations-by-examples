import Std.Data.HashSet

/-!
# A key that costs no allocation: `Nat` below 2⁶³ instead of `UInt64`

Veil: PRs #96 and #108.

## Why it matters

Compiled Lean code is polymorphic by *erasure*: wherever a type parameter stands, the value is a
`lean_object *`. A `UInt64` stored there has to be boxed: `lean_box_uint64` allocates a 16-byte
object, 8 bytes of header and 8 of payload, to hold the number, and every read of the key
dereferences it. A `Nat` below 2⁶³ is a tagged scalar, `(n << 1) | 1`, which *is* a
`lean_object *`: storing it allocates nothing, comparing it dereferences nothing.

This matters wherever a 64-bit key is stored many times over in generic containers. A model
checker is the extreme case: it keeps no visited state, only the state's 64-bit hash, and keeps
that hash in a seen set, in a log, in a work queue, all generic in the key type, for millions of
states. Each copy is an allocation, a deallocation later, and a pointer to follow on every
comparison; on several threads the boxes are shared objects with atomic reference counts. A 63-bit
`Nat` key removes all of that, with two provisos: the value must stay below 2⁶³, because
`UInt64.toNat` of a larger value allocates a bignum; and the bit dropped to get there must be the
right one.
-/

/-! ## 1. Where the boxing happens

A work-queue item, simplified. `Item` is generic in the key type; `ItemMono` fixes it to `UInt64`.
Each definition's IR is in the infoview, under a `[Compiler.IR] [result]` node:

- `mkItemU` boxes first: `let x_3 : tobj := box x_1;` and then stores the box in the constructor.
  That `box` of a `u64` is `lean_box_uint64`, an allocation.
- `mkItemN` stores the `Nat` as it is: `ctor_0[Item.mk] x_1 x_2`. Its IR type is `tobj`, "tagged or
  object": a scalar when small.
- `mkItemMono` has no box either: `sset x_3[1, 0] : u64 := x_1` writes the number into the
  constructor's scalar area. Monomorphic structures keep `UInt64` fields unboxed.

The problem is not `UInt64`, it is `UInt64` seen through a type parameter. When the container has
to stay generic (Veil's checker does: with the state itself as the key, the search is complete),
the fix is a key type that is already a `lean_object *`. -/

structure Item (σₕ : Type) where
  fingerprint : σₕ
  depth : Nat

structure ItemMono where
  fingerprint : UInt64
  depth : Nat

set_option trace.compiler.ir.result true in
def mkItemU (h : UInt64) (d : Nat) : Item UInt64 := ⟨h, d⟩

set_option trace.compiler.ir.result true in
def mkItemN (h : Nat) (d : Nat) : Item Nat := ⟨h, d⟩

set_option trace.compiler.ir.result true in
def mkItemMono (h : UInt64) (d : Nat) : ItemMono := ⟨h, d⟩

/-! The same thing inside a real container. `Std.HashSet` keeps each bucket as a linked list of
keys; a lookup walks the list comparing keys. In the `UInt64` version, the comparison loop (the
specialization of `AssocList.contains` for `containsU`) does `let x_6 : u64 := unbox x_4;` for
every key it passes, a pointer dereference, and `insert` boxes the key before consing it onto the
bucket. In the `Nat` version there is neither `box` nor `unbox` anywhere: the key is compared as a
tagged scalar. -/

set_option trace.compiler.ir.result true in
def containsU (s : Std.HashSet UInt64) (x : UInt64) : Bool := s.contains x

set_option trace.compiler.ir.result true in
def containsN (s : Std.HashSet Nat) (x : Nat) : Bool := s.contains x

/-! ## 2. Below 2⁶³, and which bit to drop

`UInt64.toNat` is `lean_uint64_to_nat`: `lean_box(n)` if `n ≤ LEAN_MAX_SMALL_NAT`, a bignum
allocation otherwise. `LEAN_MAX_SMALL_NAT` is `SIZE_MAX >> 1`, so a 64-bit hash has to lose one
bit. The first version (PR #96) shifted the hash right by one, dropping the lowest bit. That merged
states (PR #108), and the reason is where a hash keeps its information. -/

#guard (0x7fffffffffffffff : Nat) == 2 ^ 63 - 1   -- `LEAN_MAX_SMALL_NAT` on a 64-bit platform

/-- An enumeration. Lean's derived hash of a constructor without fields is its index. -/
inductive Color | red | green | blue
  deriving Hashable, Repr, DecidableEq

#guard (hash Color.red, hash Color.green, hash Color.blue) == (0, 1, 2)

-- The hashes of the base types are the values themselves.
#guard (hash (5 : Nat), hash (5 : Fin 10), hash 'a') == (5, 5, 97)

/-- A state with a single field, hashed as that field: folding `mixHash` over the fields *starting
from the first field's hash* leaves a lone field unmixed, so its hash is `0`, `1` or `2` here.
(Lean's own `deriving Hashable` mixes from a seed, hence the hand-written instance; Veil's deriving
handler folds from the first field.) -/
structure OneField where
  x : Color

instance : Hashable OneField := ⟨fun s => hash s.x⟩

/-- Drop the lowest bit (PR #96). -/
def fingerprintShift (s : OneField) : Nat := (hash s >>> 1).toNat

/-- Drop the highest bit (PR #108). The mask is `LEAN_MAX_SMALL_NAT`. -/
def fingerprintMask (s : OneField) : Nat := (hash s &&& 0x7fffffffffffffff).toNat

-- Two different states, one fingerprint: a checker would see 2 states where there are 3.
#guard fingerprintShift ⟨.red⟩ == fingerprintShift ⟨.green⟩
-- Dropping the top bit keeps them apart.
#guard fingerprintMask ⟨.red⟩ != fingerprintMask ⟨.green⟩
#guard fingerprintMask ⟨.green⟩ != fingerprintMask ⟨.blue⟩
#guard fingerprintMask ⟨.red⟩ != fingerprintMask ⟨.blue⟩

/-- With two or more fields the hash goes through `mixHash`, a multiplicative mix, after which no
bit is better than another: dropping the top one or the bottom one collides with the same
probability. Multi-field states therefore never showed the bug. -/
structure TwoFields where
  x : Color
  y : Color

instance : Hashable TwoFields := ⟨fun s => mixHash (hash s.x) (hash s.y)⟩

#eval (hash (TwoFields.mk .red .red), hash (TwoFields.mk .red .green), hash (TwoFields.mk .green .red))

/-- The key to use, for any hashable value: its hash with the top bit cleared, as a scalar `Nat`. -/
def fingerprint {σ : Type} [Hashable σ] (s : σ) : Nat := (hash s &&& 0x7fffffffffffffff).toNat

/-! ## 3. Measure it

`lake exe scalar-fingerprints [n] [uint64|nat|bignat]` inserts `n` pseudo-random keys into a
`Std.HashSet` and then looks every one of them up, with the keys as `UInt64`, as `Nat` below 2⁶³,
or as `Nat` at or above 2⁶³ (what dropping no bit would give). The keys are the same 63 bits in all
three cases. With no mode given, it runs all three in turn.

With the default 4,000,000 keys (Apple M4 Pro), filling the `UInt64` set takes about 1.5× as long
as filling the `Nat` set (670 ms against 440 ms) and looking every key up 1.2× (95 ms against
80 ms); the bignum set takes 6× and 15× (2.8 s and 1.2 s). For the memory, run one mode at a time
under `/usr/bin/time -l` (macOS) and compare the maximum resident set size: 272 MB for `UInt64`,
233 MB for `Nat`, 404 MB for the bignums. The 39 MB between the first two is less than the 64 MB
that 4,000,000 boxes of 16 bytes occupy, because the peak is measured against pages the allocator
had already mapped for the old bucket arrays and could reuse. The generated C
(`.lake/build/ir/ExpOpt/ScalarFingerprints.c`) shows the boxing statically: `lean_box_uint64`
appears in the `insertIfNew` specialized for the `UInt64` set and in `mkItemU` (and in the
`_boxed` wrappers of functions that return a `UInt64`, which only the interpreter calls), and
nowhere in the `Nat` paths. -/

/-- splitmix64: 64 well-mixed bits from an index. -/
def splitmix64 (x : UInt64) : UInt64 :=
  let z := x + 0x9e3779b97f4a7c15
  let z := (z ^^^ (z >>> 30)) * 0xbf58476d1ce4e5b9
  let z := (z ^^^ (z >>> 27)) * 0x94d049bb133111eb
  z ^^^ (z >>> 31)

def keyU (i : Nat) : UInt64 := splitmix64 i.toUInt64 &&& 0x7fffffffffffffff
def keyN (i : Nat) : Nat := (keyU i).toNat                       -- a scalar
def keyBig (i : Nat) : Nat := (keyU i ||| 0x8000000000000000).toNat -- a bignum

/-- The loops run in `IO` so that they are sequenced with the clock reads. A pure `let` in an `IO`
block is not ordered with respect to the actions around it, and the compiler moved a pure `fill`
and `countHits` past both clock reads, to the `println` that used their results: both measured
0 ms. -/
@[specialize] def fill {κ : Type} [BEq κ] [Hashable κ] (n : Nat) (key : Nat → κ) :
    IO (Std.HashSet κ) := do
  let mut s : Std.HashSet κ := {}
  for i in [0:n] do
    s := s.insert (key i)
  return s

@[specialize] def countHits {κ : Type} [BEq κ] [Hashable κ] (s : Std.HashSet κ) (n : Nat)
    (key : Nat → κ) : IO Nat := do
  let mut hits := 0
  for i in [0:n] do
    if s.contains (key i) then hits := hits + 1
  return hits

@[specialize] def runMode {κ : Type} [BEq κ] [Hashable κ] (label : String) (n : Nat)
    (key : Nat → κ) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let s ← fill n key
  let t1 ← IO.monoNanosNow
  let hits ← countHits s n key
  let t2 ← IO.monoNanosNow
  IO.println s!"  {label}: fill {(t1 - t0) / 1000000} ms, lookups {(t2 - t1) / 1000000} ms, \
    {s.size} distinct keys, {hits} hits"

def main (args : List String) : IO Unit := do
  let n := (args[0]? >>= String.toNat?).getD 4000000
  let mode := args[1]?.getD "all"
  IO.println s!"{n} keys inserted into a Std.HashSet, then looked up"
  if mode == "all" || mode == "uint64" then runMode "UInt64         " n keyU
  if mode == "all" || mode == "nat"    then runMode "Nat below 2^63 " n keyN
  if mode == "all" || mode == "bignat" then runMode "Nat above 2^63 " n keyBig
