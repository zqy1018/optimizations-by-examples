/-!
# Bounded quantifiers, decided by a loop of their own

Veil: PR #87.

## Why it matters

A bounded quantifier such as `∀ i : Fin n, P i` is decided by a `Decidable` instance, and an
instance is an ordinary function: compiled once, for an arbitrary `P`. Each call site hands over
its predicate as a closure, and the loop inside the instance calls the closure back once per
candidate. When `P i` itself is cheap, an array read and a comparison, the callback is most of the
work: an indirect call, reference-count traffic on the captured variables, boxing of the result.
Code that decides many such quantifiers in a hot loop, as a model checker does for the invariants
and guards of every state it explores, pays this on every candidate of every quantifier.

## The lesson

The obvious tools do not help. The compiler does not inline instances in the phase where it
specializes, and it never specializes instances at all, so `@[inline]` or `@[specialize]` on the
instance leave its loop blind to the predicate. `@[macro_inline]` works, because it expands the
instance before compilation proper begins: the call site then sees a `@[specialize]` loop applied
to its predicate, and gets a copy of the loop with the predicate compiled in.
-/

/-! ## 1. The naive version, and what it compiles to

Is every element of an array below a bound? As a quantifier over `Fin`, with the instance Lean
finds on its own, `Nat.decidableForallFin` from core. Its IR is in the infoview, under a
`[Compiler.IR] [result]` node, or in the `lake build` output. The two lines that matter:

    let x_3 : obj := pap allBelowCore._lam_0._boxed x_1 x_2;   -- a closure: the predicate
    let x_5 : u8 := Nat.decidableForallFin._redArg x_4 x_3;    -- core's instance, precompiled

The predicate `fun i => xs[i] < bound` became `allBelowCore._lam_0`, which the `pap` wraps in a
closure together with `xs` and `bound`. Core's instance reduces to `Nat.decidableBallLT`, which a
`@[csimp]` lemma replaces at run time by `Nat.decidableBallLTTR`, whose loop was compiled once, in
`Init.Data.Nat.Lemmas`, for an arbitrary `f`. So for every `i` the loop calls our closure through
`lean_apply_1`: an indirect call that bumps the reference counts of the captured `xs` and `bound`,
enters the `_boxed` wrapper, and boxes the `Bool` on the way back. -/

set_option trace.compiler.ir.result true in
def allBelowCore (xs : Array Nat) (bound : Nat) : Bool :=
  decide (∀ i : Fin xs.size, xs[i] < bound)

/-! ## 2. The loop we want, and two attributes that do not get us there

`allLT n f` checks `f 0, f 1, …` and stops at the first `false`. It is the loop core uses, with
one difference that matters: `go` is `@[specialize]`, so the compiler is allowed to make a copy of
it for each `f` it is called with. -/

namespace Loop

/-- `true` iff `f i h` holds for every `i < n`, checking `i = 0, 1, …` and stopping at the first
`false`. -/
@[inline] def allLT (n : Nat) (f : (i : Nat) → i < n → Bool) : Bool :=
  go 0 n (Nat.zero_add n)
where
  @[specialize] go (i : Nat) : (k : Nat) → i + k = n → Bool
    | 0, _ => true
    | k + 1, h => f i (by omega) && go (i + 1) k (by omega)

private theorem allLT_go_eq_true {n : Nat} {f : (i : Nat) → i < n → Bool} :
    ∀ k i (h : i + k = n), allLT.go n f i k h = true ↔ ∀ j (hj : j < n), i ≤ j → f j hj = true := by
  intro k; induction k <;> (intro i h; simp only [allLT.go]; grind)

theorem allLT_eq_true {n : Nat} {f : (i : Nat) → i < n → Bool} :
    allLT n f = true ↔ ∀ i (h : i < n), f i h = true := by
  simp only [allLT, allLT_go_eq_true, Nat.zero_le, forall_const]

/-- The proof that `allLT` decides the quantifier, shared by the instances below. -/
theorem forall_fin_iff_allLT {n : Nat} (P : Fin n → Prop) [DecidablePred P] :
    allLT n (fun i h => decide (P ⟨i, h⟩)) = true ↔ ∀ i, P i := by
  simp only [allLT_eq_true, decide_eq_true_eq]
  exact ⟨fun h i => h i.1 i.2, fun h i hi => h ⟨i, hi⟩⟩

end Loop

/-! ### Attempt A: `@[inline]` on the instance

The IR of `allBelow` below still builds the predicate closure, then a second closure around it,
and calls the *generic* `Loop.allLT.go._redArg`: `allLT` was inlined (it is a plain definition),
but by then it was too late for `go` to be specialized.

    let x_3 : obj := pap allBelowCore._lam_0._boxed x_1 x_2;   -- the same lambda as before, reused
    let x_5 : obj := pap WithInlineInstance.decForallFin._redArg._lam_0._boxed x_3;
    let x_7 : u8 := Loop.allLT.go._redArg x_5 x_6 x_4;

The reason is in the compiler's inliner (`Lean/Compiler/LCNF/Simp/InlineCandidate.lean`): "We
don't inline instances tagged with `[inline]/[always_inline]/[inline_if_reduce]` at the base
phase." The base phase is where specialization happens; by the time the instance is inlined, in
the mono phase, the specializer has run. `@[always_inline]` behaves the same. -/

namespace WithInlineInstance

@[inline] scoped instance (priority := high) decForallFin {n : Nat} (P : Fin n → Prop)
    [DecidablePred P] : Decidable (∀ i, P i) :=
  decidable_of_iff _ (Loop.forall_fin_iff_allLT P)

set_option trace.compiler.ir.result true in
def allBelow (xs : Array Nat) (bound : Nat) : Bool :=
  decide (∀ i : Fin xs.size, xs[i] < bound)

end WithInlineInstance

/-! ### Attempt B: `@[specialize]` on the instance

Now the instance is called as a function, with the closure, and nothing is specialized:

    let x_3 : obj := pap allBelowCore._lam_0._boxed x_1 x_2;
    let x_5 : u8 := WithSpecializeInstance.decForallFin._redArg x_4 x_3;

The specializer (`Lean/Compiler/LCNF/Specialize.lean`, `specializeApp?`) returns early for every
declaration whose reducibility status is `implicitReducible`, which is the status every `instance`
gets (`Lean.getReducibilityStatus` shows it). -/

namespace WithSpecializeInstance

@[specialize] scoped instance (priority := high) decForallFin {n : Nat} (P : Fin n → Prop)
    [DecidablePred P] : Decidable (∀ i, P i) :=
  decidable_of_iff _ (Loop.forall_fin_iff_allLT P)

set_option trace.compiler.ir.result true in
def allBelow (xs : Array Nat) (bound : Nat) : Bool :=
  decide (∀ i : Fin xs.size, xs[i] < bound)

end WithSpecializeInstance

/-! ## 3. The fix: `@[macro_inline]` on the instance

`@[macro_inline]` is not an inlining hint for the optimizer; it is a substitution performed when
the definition is first translated for the compiler (`Lean/Compiler/LCNF/ToDecl.lean`,
`macroInline`), before any compiler pass. Core uses it for `Decidable (p ∧ q)` and `(p → q)`, so
that `if p ∧ q then …` short-circuits. After the expansion, the compiler sees
`Loop.allLT n (fun i h => decide (xs[i] < bound))` right in `allBelow`, and the specializer gives
`go` a copy for this predicate: `Loop.allLT.go._at_.allBelow.spec_0` below reads the array and
compares, with no closure in sight.

Two things to know about `@[macro_inline]`: it is a macro, so an argument that the body uses twice
is evaluated twice (our body uses `n`, `P` and the instance once each); and it is only allowed on
non-recursive definitions, which is why the loop is a separate `@[specialize]` function.

The priority is `high` so that this instance beats core's for the same type. -/

@[macro_inline] instance (priority := high) decidableForallFin {n : Nat} (P : Fin n → Prop)
    [DecidablePred P] : Decidable (∀ i, P i) :=
  decidable_of_iff _ (Loop.forall_fin_iff_allLT P)

set_option trace.compiler.ir.result true in
def allBelow (xs : Array Nat) (bound : Nat) : Bool :=
  decide (∀ i : Fin xs.size, xs[i] < bound)

/-! ## 4. Nothing changed but the code

Two instances of `Decidable p` are equal (there is only one proof of `p`, and only one of `¬p`), so
the two functions agree: -/

theorem allBelow_eq_allBelowCore (xs : Array Nat) (bound : Nat) :
    allBelow xs bound = allBelowCore xs bound := by
  unfold allBelow allBelowCore
  congr   -- `Decidable (∀ i, …)` is a `Subsingleton`

/-- The new instance still evaluates inside the kernel, so `by decide` keeps working. -/
example : ∀ i : Fin 3, #[1, 2, 3][i] < 4 := by decide

/-! ## 5. Measure it

`lake exe quantifier-loops [n] [iters]` decides the quantifier `iters` times over an array of `n`
elements, with each version; the bound changes with the iteration so that nothing can be hoisted
out of the loop. With the defaults (64 elements, 1,000,000 calls each) the core instance takes
490–620 ns per call and the specialized loop 55–70 ns, a factor of 8–9 (Apple M4 Pro). What the
specialized loop does not pay is the per-element callback: the closure call, the reference-count
traffic, the boxing. -/

def benchCore (xs : Array Nat) (iters : Nat) : IO Nat := do
  let mut acc := 0
  for i in [0:iters] do
    if allBelowCore xs (xs.size + i % 2) then acc := acc + 1
  return acc

def benchSpec (xs : Array Nat) (iters : Nat) : IO Nat := do
  let mut acc := 0
  for i in [0:iters] do
    if allBelow xs (xs.size + i % 2) then acc := acc + 1
  return acc

def main (args : List String) : IO Unit := do
  let n := (args[0]? >>= String.toNat?).getD 64
  let iters := (args[1]? >>= String.toNat?).getD 1000000
  let xs := Array.range n
  IO.println s!"∀ i : Fin {n}, xs[i] < bound, decided {iters} times with each instance"
  let t0 ← IO.monoNanosNow
  let a ← benchCore xs iters
  let t1 ← IO.monoNanosNow
  let b ← benchSpec xs iters
  let t2 ← IO.monoNanosNow
  let report (label : String) (ns : Nat) :=
    IO.println s!"  {label}: {ns / 1000000} ms, {ns / iters} ns per call"
  report "core instance (predicate as a closure)   " (t1 - t0)
  report "macro_inline instance, specialized loop  " (t2 - t1)
  IO.println s!"  same answers: {a == b} ({a} of {iters} calls were true)"
