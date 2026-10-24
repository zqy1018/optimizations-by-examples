# Reflection on Optimizations

One small Lean 4 program per optimization of Veil's model checker. Each file shows
the problem on a toy, the fix, and what it buys, with no Veil involved. Toolchain `v4.32.0`, as Veil.

`lake build` compiles everything and prints the IR excerpts the files discuss; in VS Code, the
infoview shows a definition's IR under a `[Compiler.IR] [result]` node. Most files are also executables that time both versions.

| File | How | Effect |
|---|---|---|
| [ScalarFingerprints.lean](ExpOpt/ScalarFingerprints.lean) | Store a hash as a `Nat` below 2⁶³, a tagged scalar, instead of a `UInt64`, which polymorphic containers box into a 16-byte object. Drop the top bit, not the bottom one. | 1.5× faster inserts, 1.2× faster lookups, 40 MB less for 4M keys (`lake exe scalar-fingerprints`) |
| [QuantifierLoops.lean](ExpOpt/QuantifierLoops.lean) | Decide `∀ i : Fin n, P i` with an `@[macro_inline]` instance over a `@[specialize]` loop, because core's instance called `P` through a closure and no attribute on a `Decidable` instance helped: `Decidable` was a `class inductive`. From Lean v4.35 it is a structure and the compiler specializes the core instance itself. | 8–9× faster per quantifier on v4.32 (`lake exe quantifier-loops`); obsolete from v4.35 |
