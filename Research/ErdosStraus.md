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

## 2026-11-25 · positive certificates suffice on the remaining primes

A certificate with positive denominators normally need not be sorted or
distinct. On a prime `p ≡ 1 mod 4`, however, a repeated denominator
`a` would give `4/p = 2/a + 1/b` with `a,b > 0`. Both fractions are
positive, so `2a > p` and `4b > p`. Clearing fractions gives
`(2a − p)(4b − p) = p²`. The positive factor `4b − p` is 3 modulo 4,
but the only positive divisors of `p²` are `1, p, p²`, all 1 modulo 4.
Thus a repeated denominator is impossible, and the three witnesses can
be sorted. Each residual class modulo 840 is 1 modulo 4, so this gives an
equivalent reduction that accepts positive certificates directly.

This bridge does not cover another prime by itself. It removes the need
to prove strict order separately when importing positive witness formulas
or computational certificates for these residual primes.

## 2026-11-26 · three fixed-parameter Type II families

Set `a = d = 1` in the existing Type II identity and take
`c = 3, 5, 6` in turn. For `q = 4c − 1`, put
`n = qk + q − 4` and `b = ck + c − 1`. These choices give
`4bc = cn + 1 + b` with `1 < b < cn`, hence ordered denominators
`b, cn, bcn`. The corresponding sufficient conditions are
`n ≡ 7 mod 11`, `n ≡ 15 mod 19`, and `n ≡ 19 mod 23`. Lean
checks these families and the equivalence obtained by excluding them
after the modulo-840 and Obláth filters. This is a specialization of the
known Type II parametrization, not a novelty claim.

For instance, the prime 1129 is 289 modulo 840 and has
`1129 + 1 = 2 · 5 · 113`, with no divisor congruent to 3 modulo 4.
The modulo-11 rule gives the denominators 308, 3387, and 1043196.

**Bounded computation, not a Lean theorem.** A prime sieve through
1,000,000 yields 2,370 primes in the six residual classes. Of these, 876
pass the Obláth test, computed by scanning divisor pairs of `p + 1`
and cross-checking by prime factorization. Among the remaining 1,494,
319 satisfy at least one of the three new congruences, leaving 1,175
outside this particular sieve. The counts do not describe primes
without expansions and are not a proof beyond the stated bound.

## 2026-11-26 · variable shifted divisor and Salez certificates

The fixed Type II rules are special cases of a variable-divisor rule.
If a divisor `q ≥ 11` of `n + 4` is 3 modulo 4, let
`c = (q + 1)/4`, `k = (n + 4)/q`, and `b = ck − 1`. Then
`qb = cn + 1` and `4bc = cn + 1 + b`, with Lean checking the
strict inequalities required for the ordered Type II witness. The
first regression example here beyond the fixed rules is 3049, with
`q = 43` and denominators 780, 33539, and 26160420.

There is also an ordered witness for the `B = 1` case of
[Salez's (14b)](https://arxiv.org/abs/1406.6307), Proposition 3.
Given `3 ≤ f ≤ n`, positive `d,t`, and the identities
`4x = n + f`, `x = de`, and `e + 1 = ft`, take
`y = ndt` and `z = ey`. Since `nt ≥ ft = e + 1` and `e ≥ 2`,
the denominators satisfy `0 < x < y < z`. The last two fractions sum
to `f/(nx)`; adding `1/x` gives `4/n`. At 1009, values
`f = 3, x = 253, d = 23, e = 11, t = 4` give denominators
253, 92828, and 1021108. Lean now verifies that the conjecture is
equivalent to the remaining cases that lack both kinds of certificate
(and already passed through the modulo-840 and Obláth filters).

**Bounded computation, not a Lean theorem.** Of the 1,494 primes
remaining below 1,000,000 after Obláth, 863 do not match the
shifted-divisor rule. Trying Salez successively at `f = 3, 7, 11`
leaves 524, 349, and 217 respectively. For each fixed `f`, the search
checks divisor pairs of `x = (p + f)/4` for `e + 1` divisible by
`f`; every selected witness was checked with exact rational
arithmetic. This does not exhaust Salez certificates, much less all
possible expansions. The counts are not counterexamples.

## 2026-11-26 · variable Type II parameters

For the `d = 1` case of the Type II identity, choose positive `a`,
`q ≥ 2` with `q + 1 = 4ac`, and write `n + 4a² = qk`.
When `2a < ck`, put `b = ck − a`. Multiplying `b + a = ck`
by `q` gives `qb = cn + a` after cancellation. The hypotheses
imply `a < b`, and `2b ≤ qb = cn + a` then gives `b < cn`.
This checks the preconditions for the ordered denominators
`ab, acn, bcn` and gives another filter in the formal reduction.
This is an algebraic specialization of the existing Type II identity.

Lean checks two examples: `(n,a,c,q,k) = (2521,4,3,47,55)`
and `(66529,8,3,95,703)`, with denominators
`(644,30252,1217643)` and `(16808,1596696,419332287)`, respectively.
The latter uses a composite divisor `q = 95`.

**Bounded computation, separate from Lean.** In the previous sample,
extend the Salez search to `f = 15,19,…,327` with `f ≤ p`.
This finds witnesses for 215 of the last 217 enumerated primes;
2521 and 66529 are the two remaining cases. The witnesses from all
stages were checked with exact rational arithmetic. This is a small
test of the certificate pipeline, not a new computational record
or a universal proof. Lean checks the general theorems and the
two examples above, not the completeness of the sample enumeration.

## 2026-11-26 · exact factorization with the first denominator fixed

Fix positive integers `n, x` with `n < 4x`. Put `A = 4x − n`
and `B = nx`, without reducing the fraction. For positive `y, z`,
Lean proves the expansion is equivalent to
`(Ay − B)(Az − B) = B²` in the integers. The hypothesis `A > 0`
excludes the degenerate case where the factor equation is automatic.
To use the identity in a search, pick a positive divisor `u` of
`B²`, set `v = B²/u`, and check that `(u+B)/A` and `(v+B)/A`
are integers with `x < (u+B)/A < (v+B)/A`. Any expansion
yields positive factors, since each reciprocal in the remainder
is strictly less than their sum `A/B`.

The audit now checks four more ordered Type II examples from the
larger computational run: 3,842,281; 5,410,441; 25,569,769; and
86,083,321. Their explicit denominators are also checked independently
against the factor equation in Lean. This does not certify the entire
search range in Lean or settle the conjecture.

## 2026-11-26 · bounds for the first denominator

For an ordered solution, positivity gives `1/x < 4/n`, and the two
later fractions are strictly smaller than `1/x`, so `4/n < 3/x`.
Lean converts both inequalities to exact integer bounds
`n < 4x < 3n` and combines them with the factorization. This gives
a finite search: try only the first denominators in this interval,
and for each one try the divisors of `(nx)^2`.

For `n = 8803369`, Lean checks the ordered triple
`(2200869, 181085300330, 3293760527702370)` using the bounded
factorization theorem. Here `A = 107` and the factors are
`1065207649` and `352413001402225929`. The example certifies this
triple, not the result of searching all smaller choices of `x`.
## 2026-11-26 · one congruence for the reduced remainder

Reduce `(4x − n)/(nx)` to `a/b` with `a, b > 0` and
`gcd(a,b)=1`. An ordered expansion starting at `x` exists
if and only if some positive divisor `u` of `b²` satisfies
`u < b`, `a ∣ u+b`, and `ax < u+b`. The last inequality
enforces that the reconstructed second denominator exceeds `x`.

If `uv=b²`, then `b(v+b)=v(u+b)`. Since `a` and `b` are
coprime, divisibility of `u+b` by `a` implies divisibility of
`v+b` by `a`. Thus only the smaller divisor requires a
congruence test. Reducing the remainder also replaces the search
on `(nx)²` by one on `b²`. This is an exact search criterion,
not a guarantee that a divisor exists or a solution to the conjecture.

The audit exercises cancellation with `n=6`, `x=2`, and the
remainder `2/12=1/6`, and a nontrivial congruence with `n=13`,
`x=4`, and the remainder `3/52`.
