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

## Next experiment

Compare the statement and witness ordering of selected modular identities in the literature. Kernel-check one identity on a residual subclass of primes and verify the exact range it covers before claiming any advance over this baseline. In particular, do not assume a published identity using positive denominators also guarantees strict order.

### Sources

- [Erdős Problems #242](https://www.erdosproblems.com/242).
- [Formal Conjectures: Erdős #242](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/242.lean), for the precise distinct-denominator statement.
- Serge E. Salez, [The Erdős–Straus conjecture: New modular equations and checking up to N = 10^17](https://arxiv.org/abs/1406.6307), for the modular sieve context and the distinction between finite verification and a universal proof.
