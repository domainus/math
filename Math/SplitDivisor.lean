import Math.ReducedRemainder
import Mathlib.Data.Int.GCD

namespace ErdosStraus

/-- For a reduced remainder with `a*x < b`, the ordered two-term completion
can be tested by splitting a divisor of `b` into two coprime positive factors.
This avoids a search over divisors of `b²`. -/
theorem reduced_remainder_iff_coprime_split {a b x : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hx : 0 < x)
    (hab : IsCoprime a b) (hsize : a*x < b) :
    (∃ y z : ℤ, x < y ∧ y < z ∧ a*y*z = b*(y+z)) ↔
      ∃ r s : ℤ, 0 < r ∧ r < s ∧ IsCoprime r s ∧ r*s ∣ b ∧ a ∣ r+s := by
  rw [reduced_remainder_iff_one_divisor ha hb hx hab]
  constructor
  · rintro ⟨u, hu, hub, ⟨v, hv⟩, hsum, _⟩
    let g : ℤ := (Int.gcd u b : ℤ)
    have hg : 0 < g := by
      dsimp [g]
      exact_mod_cast Int.gcd_pos_of_ne_zero_left b hu.ne'
    obtain ⟨r, hr⟩ : g ∣ u := Int.gcd_dvd_left
    obtain ⟨s, hs⟩ : g ∣ b := Int.gcd_dvd_right
    have hrpos : 0 < r := by
      rw [hr] at hu
      exact pos_of_mul_pos_right hu hg.le
    have hrs : r < s := by
      rw [hr, hs] at hub
      exact lt_of_mul_lt_mul_left hub hg.le
    have hcop : IsCoprime r s := by
      let ca := Int.gcdA u b
      let cb := Int.gcdB u b
      have hh : g = u*ca + b*cb := Int.gcd_eq_gcd_ab u b
      have hh' : g = g*r*ca + g*s*cb := by
        calc
          g = u*ca + b*cb := hh
          _ = g*r*ca + g*s*cb := congrArg₂ (· + ·)
            (congrArg (· * ca) hr) (congrArg (· * cb) hs)
      refine ⟨ca, cb, ?_⟩
      apply mul_left_cancel₀ hg.ne'
      linear_combination -hh'
    have hrg : r ∣ g := by
      apply (hcop.mul_right hcop).dvd_of_dvd_mul_right
      refine ⟨v, ?_⟩
      apply mul_left_cancel₀ hg.ne'
      rw [hr, hs] at hv
      linear_combination hv
    obtain ⟨t, ht⟩ := hrg
    refine ⟨r, s, hrpos, hrs, hcop, ⟨t, ?_⟩, ?_⟩
    · rw [hs, ht]; ring
    · apply (hab.of_isCoprime_of_dvd_right ⟨s, hs⟩).dvd_of_dvd_mul_left
      rw [hr, hs, ← mul_add] at hsum
      exact hsum
  · rintro ⟨r, s, hr, hrs, _, ⟨t, ht⟩, ⟨k, hk⟩⟩
    have hs := hr.trans hrs
    have hrt : 0 < r*s := mul_pos hr hs
    have htpos : 0 < t := by
      rw [ht] at hb
      exact pos_of_mul_pos_right hb hrt.le
    let u := r*r*t
    have hu : 0 < u := mul_pos (mul_pos hr hr) htpos
    have hub : u < b := by
      rw [ht]
      exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hrs hr) htpos
    refine ⟨u, hu, hub, ⟨s*s*t, ?_⟩, ⟨r*t*k, ?_⟩, ?_⟩
    · rw [ht]; dsimp [u]; ring
    · rw [ht]; dsimp [u]; linear_combination r*t*hk
    · linarith

/-- The coprime split applies to the original Erdős–Straus equation when the
positive remainder is reduced to `a/b` and its order bound is automatic. -/
theorem fixed_first_iff_reduced_coprime_split {n x : ℕ} {a b k : ℤ}
    (hn : 0 < n) (hx : 0 < x)
    (ha : 0 < a) (hb : 0 < b) (hk : 0 < k) (hab : IsCoprime a b)
    (hnum : 4*(x : ℤ) - (n : ℤ) = k*a)
    (hden : (n : ℤ)*(x : ℤ) = k*b)
    (hsize : a*(x : ℤ) < b) :
    (∃ y z : ℕ, x < y ∧ y < z ∧
      4 / (n : ℚ) = 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ)) ↔
      ∃ r s : ℤ, 0 < r ∧ r < s ∧ IsCoprime r s ∧ r*s ∣ b ∧ a ∣ r+s := by
  have hx' : (0 : ℤ) < x := by exact_mod_cast hx
  exact (fixed_first_iff_reduced_one_divisor hn hx ha hb hk hab hnum hden).trans
    ((reduced_remainder_iff_one_divisor ha hb hx' hab).symm.trans
      (reduced_remainder_iff_coprime_split ha hb hx' hab hsize))

end ErdosStraus
