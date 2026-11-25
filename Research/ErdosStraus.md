# Erdős–Straus research log

## 2026-11-25 · checked baseline

For an input n in the indicated family, the Lean proofs construct the following increasing witnesses:

| Family | Conditions | Denominators |
|---|---|---|
| n = 2k | k ≥ 2 | k, k + 1, k(k + 1) |
| n = 4k + 3 | a = k + 1, b = na | a, b + 1, b(b + 1) |
| n = 3k + 2 | k ≥ 1, a = k + 1 | a, n, na |
| n = 8k + 5 | a = k + 1 | 2a, na, 2na |

Multiplying the input and all three witnesses by the same positive integer preserves the identity and strict order. Thus every odd input n > 2 can be handled via any prime divisor with a valid expansion. An odd prime > 3 outside 1 mod 24 is in at least one of the checked odd families, and 3 is handled directly. Conversely, the full conjecture includes all primes in 1 mod 24. This is a reduction, not a solution.

Lean 4.19.0 and the pinned mathlib dependencies: clean `lake build`, followed by `lake env lean Audit/ErdosStraus.lean`. All seven results use only the standard Lean axioms printed by the audit. The code is an independent formalization of elementary, known methods.

## 2026-11-25 · classical sieve modulo 840

The following five families specialize Elsholtz–Tao, Proposition 1.9 and §10.
Each row lists the denominators in strictly increasing order.

| Family | Conditions | Denominators |
|---|---|---|
| n = 20k + 13 | c = k + 1, b = 3k + 2 | 5c, 5bc, 5bn |
| n = 20k + 17 | c = k + 1, b = 7k + 6 | 5c, 5bc, 5bn |
| n = 7k + 3 | k ≥ 1, b = 2k + 1 | b, 2n, 2bn |
| n = 7k + 5 | k ≥ 2, b = k + 1 | 2b, 2n, bn |
| n = 7k + 6 | k ≥ 1, b = k + 1 | 2b, 2n, 2bn |

A prime congruent to 1 modulo 24 is at least 25, so the lower bounds in
the last three rows do not exclude any eligible primes. Such a prime is
coprime to 5 and 7. Among the 24 residues modulo 840 meeting these
conditions, the five new families cover 18. The Lean kernel checks the
finite sieve table over all 840 residues using `decide`; combining it with
the prime reduction leaves exactly **1, 121, 169, 289, 361, 529** as the
candidate residues for this sieve.

This is a formalization of known mathematics, not a proof of the open
conjecture or a claim that primes in these classes lack expansions.

## Experiment selected after the modulo-840 sieve

Test divisor-based witness criteria on primes in the six residual classes.
Start by comparing positive solutions from Proposition 2.6 with the
strict-denominator target and checking how to handle ties. Track sample
coverage separately from universal theorems. Elsholtz–Tao, Proposition 1.6
and the discussion before Proposition 1.9, explain why a finite list of
polynomial formulas on congruence classes cannot finish the conjecture.

### Sources

- [Erdős Problems #242](https://www.erdosproblems.com/242).
- [Formal Conjectures: Erdős #242](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/242.lean), for the precise distinct-denominator statement.
- Serge E. Salez, [The Erdős–Straus conjecture: New modular equations and checking up to N = 10^17](https://arxiv.org/abs/1406.6307), for the modular sieve context and the distinction between finite verification and a universal proof.
- Christian Elsholtz and Terence Tao, [Counting the number of solutions to the Erdős–Straus equation on unit fractions](https://arxiv.org/abs/1107.1010), especially Propositions 1.6 and 1.9 and §10.

- K. Obláth, “Sur l’équation diophantienne 4/n = 1/x₁ + 1/x₂ + 1/x₃,” Mathesis 59 (1950), 308–316.
## 2026-11-25 · variable-divisor filter inside the six classes

The reusable Type II lemma takes positive integers with `a < b < c n`
and checks the relation `4 a b c d = c n + a + b`. It gives strictly
increasing denominators `abd, acdn, bcdn` by writing the three fractions
over the common denominator `abcd n`. This is the forward algebra of
Elsholtz–Tao's Type II parameterization; it does not assert that every
expansion admits these ordering conditions.

In the classical criterion attributed to Obláth, take a divisor
`q ≡ 3 mod 4` of `n + 1`, with `n ≡ 1 mod 4`. Set
`d = (q + 1)/4` and `b = (n + 1)/q`. Lean checks `1 < b < n`,
so `db, dn, dbn` are distinct and ordered. The divisor need not be prime.
For example, 20521 has remainder 361 modulo 840, but the divisor 31 of
20522 gives the expansion with denominators 5296, 164168, and 108679216.

The conjecture now reduces to primes in the same six classes for which
**no** divisor of `p + 1` is 3 modulo 4. This is not a resolution of
the remaining case. Next, test how much the filter actually covers on an
explicitly bounded sample, and investigate a different witness criterion
on the cases it misses.
