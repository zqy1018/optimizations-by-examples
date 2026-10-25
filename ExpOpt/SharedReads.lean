import Lean

/-!
# When sharing a state read prevents inlining

Veil: PR #81.

## Why it matters

Veil's model checker repeatedly executes actions that combine state and nondeterminism.
This example shows how sharing a state-read function can prevent inlining, leaving avoidable
allocations and checks in those actions.

The IR observations below were checked on Lean v4.32.0 and v4.35.0. Inlining decisions depend
on the compiler version and the surrounding code.
-/

/-! ## 1. The monad, the reads, and a program

`StateM σ α` takes a state, and returns a value and a new state. `Multi σ α` returns a list of such
pairs. `bindM m k` runs `m`, then runs the continuation `k` on each resulting value and state.
*Its empty and singleton fast paths avoid generic `flatMap` code.* In particular, the singleton
case makes a lifted deterministic step followed by `bind` reduce definitionally to its
continuation, allowing us to isolate the sharing and inlining issue below. The `Monad` instance
uses this bind and `pureM`, so programs can use `do` notation.

`Go.go` wraps a `StateM` computation's result in a singleton list. We use the standard `get` and
`modifyGet` operations for reads and updates.

`requireM` is a guard: when its condition is false, it returns no results. -/

abbrev Multi (σ α : Type) := σ → List (α × σ)

@[inline] def bindM (m : Multi σ α) (k : α → Multi σ β) : Multi σ β := fun s =>
  match m s with
  | [] => []                -- fast path for no results
  | [(a, s')] => k a s'     -- fast path for a single result
  | rs => rs.flatMap fun (a, s') => k a s'

@[inline] def pureM (a : α) : Multi σ α := fun s => [(a, s)]

instance : Monad (Multi σ) where
  pure := pureM
  bind := bindM

@[inline] def emptyM : Multi σ α := fun _ => []
@[inline] def requireM (c : Bool) : Multi σ Unit := if c then pureM () else emptyM

class Go (σ : Type) where
  go : StateM σ α → Multi σ α

instance : Go σ where
  go x := fun s => [x s]

/-! A read does not change the state. In `[(s, s)]`, the first `s` is the value read and the
second is the state passed to the next step. Substituting this singleton list into `bindM`
selects its one-result branch, so the whole operation reduces to `k s s`:

```
(Go.go get >>= k) s = k s s
```

This reduction is witnessed by the following definitional equality: -/

example (k : σ → Multi σ α) (s : σ) : (Go.go get >>= k) s = k s s := rfl

/-! Whether the compiler performs this optimization depends on its inlining decisions and the
surrounding code. The next example shows how sharing the read function can prevent it. -/

abbrev S := Nat × Nat

/-! The program reads the state, checks a guard, reads again, updates the state, and reads once
more before calling `k`. The middle read is deliberately unused. Even this redundant read can
affect compilation. -/

set_option trace.compiler.ir.result true in
def prog (k : Nat → Multi S Unit) : Multi S Unit := do
  let x ← Go.go get
  requireM (x.1 == 0)
  let _ ← Go.go get
  Go.go (modifyGet fun st => ((), (st.1 + 1, st.2)))
  let s ← Go.go get
  k s.1

/-! The generated IR, shown in the infoview or by `lake build`, contains a separate read function.
The caller takes its result apart and checks the list's tail:

```
def prog._lam_0 (x_1 : obj) : tobj :=             -- the read: build [(s, s)]
  inc x_1;
  let x_2 : obj := ctor_0[Prod.mk] x_1 x_1;
  let x_3 : tagged := ctor_0[List.nil];
  let x_4 : obj := ctor_1[List.cons] x_2 x_3;
  ret x_4
def prog (x_1 : obj) (x_2 : obj) : tobj :=
  let x_3 : tobj := prog._lam_0 x_2;              -- call it
  let x_4 : tobj := proj[0] x_3;                   -- head
  inc x_4;
  let x_5 : tobj := proj[1] x_3;                   -- tail
  inc x_5;
  case x_5 : tobj of                               -- exactly one result?
  List.nil → …                                     -- yes: go on, and read again the same way
  default → … List.flatMapTR.go._at_.prog.spec_1 … -- no: the generic path, never taken
```

The two remaining read sites *share* the same function, `prog._lam_0`: the call shown above is
followed by another when the guard succeeds. The last source-level read has already been
eliminated. There are two remaining checks of a list's tail and two branches into generic
`flatMap` code. The compiler has removed the outer empty-list check, but has not removed the
checks that distinguish one result from several.

This sharing leaves both calls uninlined in the final IR. Each call still constructs a
temporary pair and list cell, which the caller then unpacks and checks. These allocations,
calls, checks, and associated reference-count operations add runtime work. What's worse, the
generic `flatMap` branches are never taken for a read, but their specialized helper functions
remain in the generated code and increase its size. -/

/-! ## 2. How sharing affects inlining

Common-subexpression elimination (CSE) runs before the first simplification pass.
`set_option trace.Compiler.cse true` and `trace.Compiler.simp true` on `prog` show the steps.
Here `simp` is a compiler pass, not the tactic. After `cse`, one `let` stands for all three
occurrences of `Go.go get`. It is the function that is shared, roughly, after unfolding the
`Monad` instance:

```
let read := Go.go get
bindM read fun x => ... bindM read ...
```

Each use of `read` still receives its own state; no read result is cached across the update.
After the first `simp` pass, the shared expression is a local function with two calls remaining.
The local function `_f.2` below is later lifted to `prog._lam_0` in the final IR shown above:

```
fun _f.2 _y.3 : List ((Nat × Nat) × Nat × Nat) :=
  let _x.4 := @Prod.mk _ _ _y.3 _y.3;
  let _x.5 := @List.nil _;
  let _x.6 := @List.cons _ _x.4 _x.5;
  return _x.6;
…
let _x.43 := _f.2 a.1;
cases _x.43 : List (PUnit × Nat × Nat)
| List.nil => …
| List.cons head.45 tail.46 => …
```

The local-function inliner accepts a function marked `once` or `mustInline`, or one whose body
has size at most `compiler.small` (default 1). The usage information is approximate and is
recomputed between simplification iterations. Here the read function is used more than once,
is not marked `mustInline`, and has size 3: one `let` each for the pair, nil, and cons. It is not
inlined at the remaining calls. These rules are in `Lean.Compiler.LCNF.Simp.SimpM`.

`twoReads` and `threeReads` below illustrate how sharing the read function affects inlining.
With `trace.Compiler.simp.step`, the first internal simplification iteration of `twoReads` leaves
just one call to the shared read function.
A later iteration can inline it, and all read-related allocations and checks disappear.
For `threeReads`, two calls remain and prevent this further inlining. This is a consequence of
the simplification sequence for these terms, not a fixed limit of two reads. -/

set_option trace.compiler.ir.result true in
def twoReads (k : Nat → Multi S Unit) : Multi S Unit := do
  let _ ← Go.go get
  let s ← Go.go get
  k s.1

set_option trace.compiler.ir.result true in
def threeReads (k : Nat → Multi S Unit) : Multi S Unit := do
  let _ ← Go.go get
  let _ ← Go.go get
  let s ← Go.go get
  k s.1

/-! As a control, increase `compiler.small` to 3 for a copy of `prog`. The shared read function
now qualifies for inlining, and its temporary data and the associated checks disappear. Its
final IR is the same as `progLowered` below, apart from the definition name.

This illustrates a tradeoff: sharing reduces repeated expressions, but can prevent inlining
that would also simplify their consumers. Inlining the read also removes the caller's list
checks and generic branches. A size estimate for the read alone does not account for those savings. -/

set_option compiler.small 3 in
set_option trace.compiler.ir.result true in
def progSmall (k : Nat → Multi S Unit) : Multi S Unit := do
  let x ← Go.go get
  requireM (x.1 == 0)
  let _ ← Go.go get
  Go.go (modifyGet fun st => ((), (st.1 + 1, st.2)))
  let s ← Go.go get
  k s.1

/-! However, raising `compiler.small` also affects other inlining decisions within its scope.
We therefore use a rewrite that targets the state read together with its `bind`, as described
in the next section. -/

/-! ## 3. Rewrite the read and its bind together

We can implement `Go.go get >>= k` directly as `fun s => k s s`, using the definitional
equality established above. We package this computation in a helper named `getThen`: -/

@[always_inline, inline] def getThen (k : σ → Multi σ α) : Multi σ α := fun s => k s s

/-! Replacing `Go.go get >>= k` with `getThen k` removes the list-producing operation before
compilation. Each rewritten use of `getThen` receives its own continuation. The
`@[always_inline]` attribute exposes a direct call to that continuation at the use site.

The same idea applies to any deterministic step `f` lifted by the concrete `Go` instance above:
pass the value and state from `f s` directly to `k`. It need not be a read. This equation also
holds by definitional equality: -/

example (f : StateM σ α) (k : α → Multi σ β) :
    (Go.go f >>= k) = (fun s => let (a, s') := f s; k a s') := rfl

/-! `modifyGetThen` implements this for an update. -/

@[always_inline, inline] def modifyGetThen (f : σ → β × σ) (k : β → Multi σ α) : Multi σ α :=
  fun s => match f s with | (b, s') => k b s'

/-! We express the transformations above as rewrite lemmas. `go_get_bind` and `go_modifyGet_bind`
replace a read or update followed by `>>=` with the corresponding wrapper. `getThen_const`
removes a read whose value is unused: `fun _ => k` ignores the value read, while `k` still
receives the current state.

*All three lemmas have `rfl` proofs, so `dsimp` can apply them while preserving definitional equality.*
The bind lemmas match `>>=` directly, as generated by `do` notation. Veil applies such
rewrites to extracted actions before compilation; `lower%` below provides a small term
elaborator for this example. -/

theorem go_get_bind (k : σ → Multi σ α) : (Go.go get >>= k) = getThen k := rfl

theorem go_modifyGet_bind (f : σ → β × σ) (k : β → Multi σ α) :
    (Go.go (modifyGet f) >>= k) = modifyGetThen f k := rfl

theorem getThen_const (k : Multi σ α) : getThen (fun _ => k) = k := rfl

open Lean Elab Term Meta in
/-- Elaborate `t`, then apply the given `rfl` lemmas using `dsimp`. Stop when the expression no
longer changes, or after eight rounds. Return the rewritten term for compilation. -/
elab "lower% " "[" lemmas:ident,* "] " t:term : term <= expectedType => do
  let e ← elabTermEnsuringType t expectedType
  synthesizeSyntheticMVarsNoPostponing  -- a pending instance (of a numeral, say) blocks a rewrite
  let mut e ← instantiateMVars e
  let mut thms : SimpTheorems := {}
  for l in lemmas.getElems do
    thms ← thms.addConst (← realizeGlobalConstNoOverload l)
  let ctx ← Simp.mkContext (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)
  for _ in [0:8] do
    let (r, _) ← dsimp e ctx
    if r == e then break
    e := r
  return e

/-! Only `go_get_bind` is needed to optimize this program. The compiler handles the update and
the unused read once the list-producing reads have been replaced. `progReadLowered` has the
same final IR as the version with all three rewrites below. -/

set_option trace.compiler.ir.result true in
def progReadLowered (k : Nat → Multi S Unit) : Multi S Unit :=
  lower% [go_get_bind] do
    let x ← Go.go get
    requireM (x.1 == 0)
    let _ ← Go.go get
    Go.go (modifyGet fun st => ((), (st.1 + 1, st.2)))
    let s ← Go.go get
    k s.1

/-! Applying all three rewrites also makes the update explicit and removes the unused read
before compilation. `#print progLowered` shows the resulting term:

```
getThen fun x => do
  requireM (x.fst == 0)
  modifyGetThen (fun st => ((), st.fst + 1, st.snd)) fun _ => getThen fun s => k s.fst
```

The final IR projects the state, checks the guard, updates the first component, and calls `k`.
It reuses the state pair when it has a unique reference, and allocates a new pair otherwise.
There are no temporary singleton lists from reads or the update, and no calls to the shared
read function. The continuation `k` may still allocate its own result list. -/

set_option trace.compiler.ir.result true in
def progLowered (k : Nat → Multi S Unit) : Multi S Unit :=
  lower% [go_get_bind, go_modifyGet_bind, getThen_const] do
    let x ← Go.go get
    requireM (x.1 == 0)
    let _ ← Go.go get
    Go.go (modifyGet fun st => ((), (st.1 + 1, st.2)))
    let s ← Go.go get
    k s.1

set_option pp.funBinderTypes false in
#print progLowered

/-! ## 4. Check that the programs are equal

Changing the compiler option does not change the term. The rewrites preserve definitional
equality, as checked by `rfl` below. These proofs establish equality of the programs; the IR
traces separately show whether the intended optimization occurred. -/

example : progSmall = prog := rfl
example : progReadLowered = prog := rfl
example : progLowered = prog := rfl

/-! ## 5. Measure it

`lake exe shared-reads [iters]` runs both programs `iters` times on states that pass the guard
half of the time, with a continuation that returns one result. The default is 10,000,000 runs.
A sample run on arm64 macOS with Lean v4.32.0 took 394 ms for `prog` and 154 ms for `progLowered`. -/

@[noinline] def runProg (iters : Nat) : IO Nat := do
  let k : Nat → Multi S Unit := fun n s => [((), (n, s.2 + 1))]
  let mut acc := 0
  for i in [0:iters] do
    acc := acc + (prog k (i % 2, i)).length
  return acc

@[noinline] def runLowered (iters : Nat) : IO Nat := do
  let k : Nat → Multi S Unit := fun n s => [((), (n, s.2 + 1))]
  let mut acc := 0
  for i in [0:iters] do
    acc := acc + (progLowered k (i % 2, i)).length
  return acc

def main (args : List String) : IO Unit := do
  let iters := (args[0]? >>= String.toNat?).getD 10000000
  IO.println s!"read, guard, read, write, read, continue: {iters} runs of each version"
  let t0 ← IO.monoNanosNow
  let a ← runProg iters
  let t1 ← IO.monoNanosNow
  let b ← runLowered iters
  let t2 ← IO.monoNanosNow
  let report (label : String) (ns : Nat) :=
    IO.println s!"  {label}: {ns / 1000000} ms, {ns / iters} ns per run"
  report "reads as shared function calls " (t1 - t0)
  report "reads lowered to getThen       " (t2 - t1)
  IO.println s!"  same results: {a == b} ({a} results in total)"

/-! ## 6. What this example shows

Sharing can reduce repeated expressions while preventing later simplification. Here CSE shares
the read function, which changes the inlining decision. The cost includes both the read's
temporary data and the checks in the caller that inlining would have removed.

For this state-and-list representation, a deterministic step followed by `bind` can pass its
value and state directly to the continuation. Rewriting the two operations together before
compilation removes the intermediate singleton list while preserving definitional equality.
`getThen` is the state-read case of this more general transformation. -/
