/-!
# An optimization with a shelf life

Veil: PR #87. A workaround measured on Lean v4.32 and v4.34, revisited on v4.35.

## Why it mattered

Invariants and guards of a specification are full of bounded quantifiers, `∀ i : Fin n, P i`, and
a model checker decides them on every state it explores, through the `Decidable` instances Lean
synthesizes. Instance search happens during elaboration; at run time, the selected instance
executes the check. The proposition and its proofs are erased, but the decision procedure supplied
by `DecidablePred P` still has to run. Below, "predicate closure" means this executable check.

On older toolchains, calling the predicate for each element dominated the array check below;
specialization put the check directly into the loop.

## Why revisit it

On Lean v4.35, the same source expression already produces a specialized core loop.
-/

/-! ## 1. The naive version, and what it compiled to on v4.32

Is every element of an array below a bound? As a quantifier over `Fin`, with the instance Lean
finds on its own, `Nat.decidableForallFin` from core. On v4.32 its IR (infoview, under a
`[Compiler.IR] [result]` node, or in the `lake build` output) has two lines that matter. Here `pap`
constructs a closure containing the check and its captured arguments:

    let x_3 : obj := pap allBelowCore._lam_0._boxed x_1 x_2;   -- a closure: the predicate
    let x_5 : u8 := Nat.decidableForallFin._redArg x_4 x_3;    -- core's instance, precompiled

The predicate `fun i => xs[i] < bound` became `allBelowCore._lam_0`, wrapped in a closure with `xs`
and `bound`. Core's instance reduces to `Nat.decidableBallLT`, which a `@[csimp]` lemma replaces
during compilation by `Nat.decidableBallLTTR`, whose loop was compiled in `Init.Data.Nat.Lemmas`
for an arbitrary `f`; for each visited `i` it calls our closure through `lean_apply_1`. The closure
is allocated once per quantifier call; the indirect call and its ownership bookkeeping recur per
element. The `Bool` result is boxed as a tagged immediate, without a heap allocation. Small `Nat`
captures such as this benchmark's bound also have no reference count, whereas the array does. -/

set_option trace.compiler.ir.result true in
def allBelowCore (xs : Array Nat) (bound : Nat) : Bool :=
  decide (∀ i : Fin xs.size, xs[i] < bound)

/-! ## 2. The loop we want, and the attribute that did not get us there

`allLT n f` checks `f 0, f 1, …` and stops at the first `false`; `go` is `@[specialize]`, so the
compiler may copy it for a visible predicate. Core's `Nat.allLTTR.loop` already had this attribute;
the missing opportunity was exposing the predicate to it. This version keeps the current index
and remaining count explicitly, while core computes the index from its remaining count.

With `@[inline]` on an instance built from this loop, the IR of
`allBelow` on v4.32 still built the predicate closure, a second closure around it, and called the
*generic* `Loop.allLT.go._redArg`: `allLT` was inlined, being a plain definition, but too late for
`go` to be specialized. The compiler's inliner says why
(`Lean/Compiler/LCNF/Simp/InlineCandidate.lean`): "We don't inline instances tagged with
`[inline]/[always_inline]/[inline_if_reduce]` at the base phase", and the base phase is where
specialization happens. In this compiler, `@[specialize]` on the instance did no better:
`Lean/Compiler/LCNF/Specialize.lean` skips declarations with `implicitReducible` status, which the
`instance` command assigns by default. These are compiler policies, not semantic properties of
type classes. -/

namespace Loop

/-- `true` iff `f i h` holds for every `i < n`, checking `i = 0, 1, …` and stopping at the first
`false`. -/
@[inline] def allLT (n : Nat) (f : (i : Nat) → i < n → Bool) : Bool :=
  go 0 n (Nat.zero_add n)
where
  @[specialize] go (i : Nat) : (k : Nat) → i + k = n → Bool
    | 0, _ => true
    | k + 1, h => f i (by omega) && go (i + 1) k (by omega)

-- The next three lemmas establish correctness; they can be skipped when following the optimization.
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

namespace WithInlineInstance

@[inline] scoped instance (priority := high) decForallFin {n : Nat} (P : Fin n → Prop)
    [DecidablePred P] : Decidable (∀ i, P i) :=
  decidable_of_iff _ (Loop.forall_fin_iff_allLT P)

set_option trace.compiler.ir.result true in
def allBelow (xs : Array Nat) (bound : Nat) : Bool :=
  decide (∀ i : Fin xs.size, xs[i] < bound)

end WithInlineInstance

/-! ## 3. The fix: `@[macro_inline]` on the instance

`@[macro_inline]` is not an inlining hint for the optimizer; it is a substitution performed when
the definition is first translated for the compiler (`Lean/Compiler/LCNF/ToDecl.lean`), before any
pass. Core uses it for `Decidable (p ∧ q)`, so that `if p ∧ q then …` short-circuits. After the
expansion the compiler sees `Loop.allLT n (fun i h => decide (xs[i] < bound))` right in
`allBelow`, and the specializer gives `go` a copy for this predicate:
`Loop.allLT.go._at_.allBelow.spec_0` reads the array and compares, with no predicate closure.
The values of `xs` and `bound` can still vary at run time; it is the code of the check that must be
visible. Substituting argument expressions can duplicate work if the body uses them more than
once. `@[macro_inline]` is only allowed on non-recursive definitions, which is why the loop is a
separate function. -/

@[macro_inline] instance (priority := high) decidableForallFin {n : Nat} (P : Fin n → Prop)
    [DecidablePred P] : Decidable (∀ i, P i) :=
  decidable_of_iff _ (Loop.forall_fin_iff_allLT P)

set_option trace.compiler.ir.result true in
def allBelow (xs : Array Nat) (bound : Nat) : Bool :=
  decide (∀ i : Fin xs.size, xs[i] < bound)

/-! ## 4. Nothing changed but the code

Two instances of `Decidable p` are equal, so the two functions agree, and the new instance still
evaluates in the kernel. This establishes their semantic agreement; their relative execution
cost is a separate measurement. The `by decide` example checks kernel evaluation still works,
without making a claim about its speed. -/

theorem allBelow_eq_allBelowCore (xs : Array Nat) (bound : Nat) :
    allBelow xs bound = allBelowCore xs bound := by
  unfold allBelow allBelowCore
  congr   -- `Decidable (∀ i, …)` is a `Subsingleton`

example : ∀ i : Fin 3, #[1, 2, 3][i] < 4 := by decide

/-! ## 5. Measure it

`lake exe quantifier-loops [n] [iters]` decides the quantifier `iters` times over an array of `n`
elements with each implementation. The bound alternates between `n` and `n + 1`, making the call
depend on the iteration. Every element of `Array.range n` satisfies both bounds, so this measures
full scans with a cheap predicate, not early failures or expensive checks.

One local comparison on Apple M4 Pro, with 64 elements and 1,000,000 calls per implementation,
gave these ranges over three runs per toolchain (Release compilation, `-O3 -DNDEBUG`):

| Lean | Core instance, ns/call | Custom instance, ns/call |
| --- | ---: | ---: |
| v4.32.0 | 496–512 | 56–59 |
| v4.34.0 | 498–515 | 57–58 |
| v4.35.0 | 64–84 | 56–57 |

The large gap has disappeared on v4.35, although a smaller difference remains. These measurements
do not isolate the cause of that remaining difference or predict whole-model-checker speedups. -/

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
  IO.println s!"Lean {Lean.versionString}"
  IO.println s!"∀ i : Fin {n}, xs[i] < bound, decided {iters} times with each instance"
  let t0 ← IO.monoNanosNow
  let a ← benchCore xs iters
  let t1 ← IO.monoNanosNow
  let b ← benchSpec xs iters
  let t2 ← IO.monoNanosNow
  let report (label : String) (ns : Nat) :=
    IO.println s!"  {label}: {ns / 1000000} ms, {ns / iters} ns per call"
  report "core instance               " (t1 - t0)
  report "custom macro_inline instance" (t2 - t1)
  IO.println s!"  same answers: {a == b} ({a} of {iters} calls were true)"

/-! ## 6. Revisit the diagnosis, then the workaround

Lean v4.35 changed `Decidable` from a `class inductive` to a structure containing a `Bool` and a
proof that it reflects the proposition (Lean PR #8309, also described in the
[v4.35 release notes](https://lean-lang.org/doc/reference/latest/releases/v4.35.0/)). Reading
`decide` is now a field projection. The compiler can expand this class dictionary access before
specialization (`Lean/Compiler/LCNF/Simp/InlineProj.lean`), exposing the check to the loop.

Recompile the unchanged `allBelowCore` on v4.35: instead of the closure and generic call in
section 1, it calls a specialized `Nat.allLTTR.loop._at_.allBelowCore.spec_0`. Inside that loop
are the operations we wanted all along (with generated variable names shortened):

    let value : tobj := Array.getInternalBorrowed ◾ xs i ◾;
    let result : u8 := Nat.decLt value bound;

The loop now performs the check directly. Even `WithInlineInstance.allBelow`, the failed attempt
on the older toolchains, now gets a specialized loop. Inspect the loop body and its calls:
`_redArg` alone is not a sign of missed specialization, since specialized functions can have that
suffix too.

For this example on the tested v4.35 toolchain, the custom instance is no longer needed to compile
the check directly into the loop. Whether to retire it depends on the remaining benefit and the
cost of maintaining it. In Veil, the instances in `Veil/Util/DecidableQuantifiers.lean` and the
`Enumeration`-based instances in `Veil/Frontend/DSL/State/Types.lean` are candidates for that
review; this example only checks a universal quantifier over `Fin`. Other quantifiers and
enumeration paths need their own generated-code checks and representative measurements.

The workaround addressed a specific limitation of the compiler we were using. When upgrading
Lean, revisit both the measurement and the generated code. Keep enough evidence to recognize
when a workaround can be retired.
-/
