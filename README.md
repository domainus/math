# Math in Lean

A workspace for machine-checked mathematical results and clearly labeled open questions. Formalization of a known result is not a claim of a new mathematical discovery.

## Erdős–Straus (Erdős #242)

**Status: open.** For every integer n > 2, can 4/n be written as 1/x + 1/y + 1/z with positive integers x < y < z? We use the distinct-denominator version in [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/242.lean).

- [Lean development](Math/ErdosStraus.lean): nine classical congruence families and three fixed-parameter Type II families, positive scaling, and a reduction to primes with remainder 1, 121, 169, 289, 361, or 529 modulo 840, restricted further to primes with no divisor of p + 1 congruent to 3 modulo 4. The shifted-divisor and Salez (14b) tests narrow the remaining primes further. For a surviving prime, a certificate only needs three positive denominators; Lean proves that they cannot repeat.
- [Proof audit and regression examples](Audit/ErdosStraus.lean): the twenty-six public theorem declarations are checked with only standard Lean axioms.
- [Research log](Research/ErdosStraus.md): witness formulas, remaining cases, and next experiment.

**Not proved:** the conjecture for the remaining prime classes. The reduction modulo 840 is classical and does not supersede sharper results in the literature.

## Reproduce

With [elan](https://lean-lang.org/install/) installed, run the following from the repository root. The toolchain and dependency revisions are pinned.

```sh
lake exe cache get Mathlib.Algebra.Order.Field.Rat Mathlib.Data.Nat.Prime.Basic Mathlib.Tactic.FieldSimp Mathlib.Tactic.Ring
lake build
lake env lean Audit/ErdosStraus.lean
```

The audit prints each theorem's dependencies. The recorded set is `propext`, `Classical.choice`, and `Quot.sound`; there are no admitted results. The open statement is a definition of a proposition, not an axiom.
