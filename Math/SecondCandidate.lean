import Math.ReducedRemainder

namespace ErdosStraus

private theorem seven_divisor_pair {q t : ℤ} (hq : 1 < q) (ht : 0 < t)
    (hr : q % 7 = 3 ∨ q % 7 = 5 ∨ q % 7 = 6) :
    ∃ u : ℤ, 0 < u ∧ u < 2*q*t ∧ u ∣ (2*q*t)^2 ∧ 7 ∣ u + 2*q*t := by
  have haux (c d : ℤ) (hc : 0 < c) (hlt : c < 2*q)
      (hcd : c*d = 4*q^2) (hs : (7 : ℤ) ∣ c + 2*q) :
      ∃ u : ℤ, 0 < u ∧ u < 2*q*t ∧ u ∣ (2*q*t)^2 ∧ 7 ∣ u + 2*q*t := by
    obtain ⟨k, hk⟩ := hs
    refine ⟨c*t, mul_pos hc ht, mul_lt_mul_of_pos_right hlt ht,
      ⟨d*t, ?_⟩, ⟨k*t, ?_⟩⟩
    · linear_combination -t^2 * hcd
    · linear_combination t * hk
  rcases hr with h | h | h
  · apply haux 1 (4*q^2) (by decide) (by omega) (by ring)
    exact ⟨2*(q / 7)+1, by omega⟩
  · apply haux 4 (q^2) (by decide) (by omega) (by ring)
    exact ⟨2*(q / 7)+2, by omega⟩
  · apply haux 2 (2*q^2) (by decide) (by omega) (by ring)
    exact ⟨2*(q / 7)+2, by omega⟩

/-- If the reduced remainder after the first denominator has numerator seven,
an even denominator divisible by a positive factor with residue 3, 5, or 6
modulo seven gives a strict expansion. The three cases use distinct divisor pairs. -/
theorem fixed_first_seven_of_factor {n x : ℕ} {q t : ℤ}
    (hn : 7 < n) (hx : 0 < x) (hfirst : n + 7 = 4*x)
    (hq : 1 < q) (ht : 0 < t)
    (hprod : (n : ℤ)*(x : ℤ) = 2*q*t)
    (hcop : IsCoprime (7 : ℤ) ((n : ℤ)*(x : ℤ)))
    (hr : q % 7 = 3 ∨ q % 7 = 5 ∨ q % 7 = 6) :
    ∃ y z : ℕ, x < y ∧ y < z ∧
      4 / (n : ℚ) = 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ) := by
  have hn' : (7 : ℤ) < (n : ℤ) := by exact_mod_cast hn
  have hx' : (0 : ℤ) < (x : ℤ) := by exact_mod_cast hx
  have hsize := mul_lt_mul_of_pos_right hn' hx'
  have hpos : (0 : ℤ) < n := by omega
  have hfirst' : (n : ℤ) + 7 = 4*(x : ℤ) := by exact_mod_cast hfirst
  obtain ⟨u, hu, hub, hd, hseven⟩ := seven_divisor_pair hq ht hr
  rw [← hprod] at hub hd hseven
  apply (fixed_first_iff_reduced_one_divisor (k := 1)
    (by omega) hx (by decide) (mul_pos hpos hx') (by decide) hcop
    (by omega) (by ring)).mpr
  exact ⟨u, hu, hub, hd, hseven, by linarith⟩

private def GoodSeven (a : ℕ) : Prop := a % 7 = 1 ∨ a % 7 = 2 ∨ a % 7 = 4

private theorem goodSeven_mul {a b : ℕ} (ha : GoodSeven a) (hb : GoodSeven b) :
    GoodSeven (a*b) := by
  unfold GoodSeven at *
  rw [Nat.mul_mod]
  rcases ha with h | h | h <;> rcases hb with h' | h' | h' <;>
    rw [h,h'] <;> decide

private theorem goodSeven_of_prime_factors (m : ℕ) (hm : 0 < m)
    (h : ∀ q : ℕ, q.Prime → q ∣ m → GoodSeven q) : GoodSeven m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases h1 : m = 1
    · subst m; unfold GoodSeven; decide
    obtain ⟨q, hq, ⟨k, hk⟩⟩ := Nat.exists_prime_and_dvd h1
    have hkpos : 0 < k := Nat.pos_of_ne_zero (fun hz => by
      rw [hz, mul_zero] at hk
      omega)
    have hkm : k < m := by
      rw [hk]
      have hh := Nat.mul_lt_mul_of_pos_right hq.one_lt hkpos
      simpa using hh
    rw [hk]
    exact goodSeven_mul (h q hq ⟨k, hk⟩) (ih k hkm hkpos (fun r hr hrd =>
      h r hr (hrd.trans ⟨q, by simpa [mul_comm] using hk⟩)))

/-- For a prime in a nonzero square class modulo seven, with a positive even
first denominator `x` satisfying `4*x = p+7`, the first denominator works
exactly when `x` has a prime factor with residue 3, 5, or 6 modulo seven. -/
theorem second_candidate_iff_prime_factor {p x : ℕ} (hp : p.Prime) (hp7 : 7 < p)
    (hpx : p + 7 = 4*x) (hx2 : 2 ∣ x)
    (hpr : p % 7 = 1 ∨ p % 7 = 2 ∨ p % 7 = 4) :
    (∃ y z : ℕ, x < y ∧ y < z ∧
      4 / (p : ℚ) = 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ)) ↔
      ∃ q : ℕ, q.Prime ∧ q ∣ x ∧ (q % 7 = 3 ∨ q % 7 = 5 ∨ q % 7 = 6) := by
  have hx : 0 < x := by omega
  have hxr : GoodSeven x := by
    unfold GoodSeven
    omega
  have hb : GoodSeven (p*x) := goodSeven_mul hpr hxr
  have hi : (p*x : ℕ) % 7 = 1 ∨ (p*x : ℕ) % 7 = 2 ∨ (p*x : ℕ) % 7 = 4 := hb
  have hi' : ((p : ℤ)*(x : ℤ)) % 7 = 1 ∨
      ((p : ℤ)*(x : ℤ)) % 7 = 2 ∨ ((p : ℤ)*(x : ℤ)) % 7 = 4 := by exact_mod_cast hi
  let b : ℤ := (p : ℤ)*(x : ℤ)
  have hcop : IsCoprime (7 : ℤ) b := by
    change b % 7 = 1 ∨ b % 7 = 2 ∨ b % 7 = 4 at hi'
    rcases hi' with h | h | h
    · exact ⟨-(b/7), 1, by omega⟩
    · exact ⟨-1-4*(b/7), 4, by omega⟩
    · exact ⟨-1-2*(b/7), 2, by omega⟩
  constructor
  · intro hexp
    have hpos : 0 < b := by dsimp [b]; positivity
    have hpx' : (p : ℤ) + 7 = 4*(x : ℤ) := by exact_mod_cast hpx
    obtain ⟨u, hu, _, hdiv, hmod, _⟩ := (fixed_first_iff_reduced_one_divisor (k := 1)
      (by omega) hx (by decide) hpos (by decide) hcop (by omega) (by dsimp [b]; ring)).mp hexp
    have huN : (u.toNat : ℤ) = u := Int.toNat_of_nonneg hu.le
    have hun : 0 < u.toNat := by omega
    have hdivN : u.toNat ∣ (p*x)^2 := by exact_mod_cast (show (u.toNat : ℤ) ∣ ((p : ℤ)*(x : ℤ))^2 by simpa only [huN] using hdiv)
    have hsum : 7 ∣ u.toNat + p*x := by
      exact_mod_cast (show (7 : ℤ) ∣ (u.toNat : ℤ) + (p : ℤ)*(x : ℤ) by simpa only [huN] using hmod)
    by_contra! hnone
    have huGood : GoodSeven u.toNat := goodSeven_of_prime_factors _ hun (by
      intro q hq hqd
      have hqb : q ∣ p*x := hq.dvd_of_dvd_pow (hqd.trans hdivN)
      rcases hq.dvd_mul.mp hqb with hqp | hqx
      · have : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp hqp
        simpa [this] using hpr
      · have hnot := hnone q hq hqx
        have hqne : q % 7 ≠ 0 := by
          intro hzero
          have h7q : 7 ∣ q := Nat.dvd_of_mod_eq_zero hzero
          have h7b : 7 ∣ p*x := h7q.trans hqb
          have hz := Nat.mod_eq_zero_of_dvd h7b
          omega
        unfold GoodSeven
        omega)
    have hsum0 := Nat.mod_eq_zero_of_dvd hsum
    rw [Nat.add_mod] at hsum0
    unfold GoodSeven at huGood
    omega
  · rintro ⟨q, hq, hqd, hqr⟩
    have hne : (2 : ℕ) ≠ q := by omega
    have h2q := (Nat.coprime_primes Nat.prime_two hq).mpr hne
    obtain ⟨k, hk⟩ := h2q.mul_dvd_of_dvd_of_dvd hx2 hqd
    have hkpos : 0 < k := by
      by_contra! hh
      have : k = 0 := by omega
      simp [this] at hk
      omega
    have hprodN : p*x = 2*q*(p*k) := by rw [hk]; ring
    have hprod : (p : ℤ)*(x : ℤ) = 2*(q : ℤ)*(p*k : ℕ) := by exact_mod_cast hprodN
    have hqr' : (q : ℤ) % 7 = 3 ∨ (q : ℤ) % 7 = 5 ∨ (q : ℤ) % 7 = 6 := by exact_mod_cast hqr
    exact fixed_first_seven_of_factor hp7 hx hpx (by exact_mod_cast hq.one_lt)
      (by exact_mod_cast Nat.mul_pos hp.pos hkpos) hprod hcop hqr'

/-- Exact second-candidate factor test on the six residual classes modulo 840. -/
theorem residual840_second_candidate_iff {p : ℕ} (hp : p.Prime)
    (hr : Residual840 (p % 840)) :
    let x := (p + 7) / 4
    (∃ y z : ℕ, x < y ∧ y < z ∧
      4 / (p : ℚ) = 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ)) ↔
      ∃ q : ℕ, q.Prime ∧ q ∣ x ∧ (q % 7 = 3 ∨ q % 7 = 5 ∨ q % 7 = 6) := by
  dsimp only
  have hp2 := hp.two_le
  obtain h | h | h | h | h | h := hr
  all_goals
    apply second_candidate_iff_prime_factor hp <;> omega

end ErdosStraus
