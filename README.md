# Math in Lean

A workspace for machine-checked mathematical results and clearly labeled open questions. Formalization of a known result is not a claim of a new mathematical discovery.

## Erdős–Straus (Erdős #242)

**Status: open.** For every integer n > 2, can 4/n be written as 1/x + 1/y + 1/z with positive integers x < y < z? We use the distinct-denominator version in [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/242.lean).

- [Lean development](Math/ErdosStraus.lean): four classical congruence families, positive scaling, coverage of all odd primes outside 1 mod 24, and an equivalence reducing the full statement to the primes in 1 mod 24.
- [Proof audit and regression examples](Audit/ErdosStraus.lean): the seven theorem declarations are checked with only standard Lean axioms.
- [Research log](Research/ErdosStraus.md): witness formulas, remaining cases, and next experiment.

**Not proved:** the remaining prime case. This baseline does not supersede sharper reductions in the literature.

## Reproduce

With [elan](https://lean-lang.org/install/) installed, run the following from the repository root. The toolchain and dependency revisions are pinned.

```sh
lake exe cache get Mathlib.Data.Nat.Prime.Basic Mathlib.Tactic.FieldSimp Mathlib.Tactic.Ring
lake build
lake env lean Audit/ErdosStraus.lean
```

The audit prints each theorem's dependencies. The recorded set is `propext`, `Classical.choice`, and `Quot.sound`; there are no admitted results. The open statement is a definition of a proposition, not an axiom.
