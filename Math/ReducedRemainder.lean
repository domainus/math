import Math.ErdosStraus
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

namespace ErdosStraus

/-- For a positive reduced remainder `a / b`, only the smaller divisor
needs a congruence check. Strict bounds recover ordered positive denominators. -/
theorem reduced_remainder_iff_one_divisor {a b x : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hx : 0 < x) (hab : IsCoprime a b) :
    (∃ y z : ℤ, x < y ∧ y < z ∧ a * y * z = b * (y + z)) ↔
      ∃ u : ℤ, 0 < u ∧ u < b ∧ u ∣ b ^ 2 ∧ a ∣ u + b ∧ a * x < u + b := by
  constructor
  · rintro ⟨y, z, hxy, hyz, he⟩
    let u := a * y - b
    let v := a * z - b
    have hprod : u * v = b ^ 2 := by dsimp [u, v]; linear_combination a * he
    have hpy : 0 < y := hx.trans hxy
    have hpz : 0 < z := hpy.trans hyz
    have hu : 0 < u := by
      have hz : u * z = b * y := by dsimp [u]; linear_combination he
      by_contra! h
      have hn := mul_nonpos_of_nonpos_of_nonneg h hpz.le
      rw [hz] at hn
      exact (not_le_of_gt (mul_pos hb hpy)) hn
    have huv : u < v := by
      dsimp [u, v]
      exact sub_lt_sub_right (mul_lt_mul_of_pos_left hyz ha) _
    have hub : u < b := by
      by_contra! h
      have h1 := mul_lt_mul_of_pos_left huv hu
      have h2 := mul_le_mul h h hb.le hu.le
      nlinarith
    have hsum : u + b = a * y := by dsimp [u]; ring
    refine ⟨u, hu, hub, ⟨v, hprod.symm⟩, ?_, ?_⟩
    · rw [hsum]; exact dvd_mul_right _ _
    · rw [hsum]; exact mul_lt_mul_of_pos_left hxy ha
  · rintro ⟨u, hu, hub, ⟨v, hv⟩, ⟨y, hy⟩, hxy⟩
    have huv : u < v := by
      by_contra! h
      have h1 := mul_le_mul_of_nonneg_left h hu.le
      have h2 := (mul_lt_mul_of_pos_left hub hu).trans (mul_lt_mul_of_pos_right hub hb)
      nlinarith
    have hc : b * (v + b) = v * (u + b) := by linear_combination hv
    have hd : a ∣ b * (v + b) := by
      rw [hc, hy]
      exact ⟨v * y, by ring⟩
    obtain ⟨z, hz⟩ : a ∣ v + b := hab.dvd_of_dvd_mul_left hd
    have hxy' : x < y := lt_of_mul_lt_mul_left (by simpa only [hy] using hxy) ha.le
    have hyz : y < z := by
      apply lt_of_mul_lt_mul_left _ ha.le
      rw [← hy, ← hz]
      exact add_lt_add_right huv _
    refine ⟨y, z, hxy', hyz, ?_⟩
    have hu' : u = a * y - b := by linarith
    have hv' : v = a * z - b := by linarith
    rw [hu', hv'] at hv
    have he : a * (a * y * z - b * (y + z)) = 0 := by linear_combination -hv
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left ha.ne')

/-- The one-divisor search for an Erdős–Straus expansion beginning at `x`.
The equations for `k` express cancellation of the common factor from
`(4x - n)/(nx)`. For a reduced fraction, no congruence test on the larger
divisor is needed. -/
theorem fixed_first_iff_reduced_one_divisor {n x : ℕ} {a b k : ℤ}
    (hn : 0 < n) (hx : 0 < x)
    (ha : 0 < a) (hb : 0 < b) (hk : 0 < k) (hab : IsCoprime a b)
    (hnum : 4 * (x : ℤ) - (n : ℤ) = k * a)
    (hden : (n : ℤ) * (x : ℤ) = k * b) :
    (∃ y z : ℕ, x < y ∧ y < z ∧
      4 / (n : ℚ) = 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ)) ↔
      ∃ u : ℤ, 0 < u ∧ u < b ∧ u ∣ b ^ 2 ∧ a ∣ u + b ∧ a * (x : ℤ) < u + b := by
  have hx' : (0 : ℤ) < x := by exact_mod_cast hx
  have hsize : n < 4 * x := by
    have hp := mul_pos hk ha
    rw [← hnum] at hp
    omega
  have hbridge {y z : ℕ} (hy : 0 < y) (hz : 0 < z) :
      (4 / (n : ℚ) = 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ)) ↔
        a * (y : ℤ) * (z : ℤ) = b * ((y : ℤ) + (z : ℤ)) := by
    rw [fixed_first_iff_factorization hn hx hy hz hsize]
    dsimp only
    rw [hnum, hden]
    have hid :
        (k * a * (y : ℤ) - k * b) * (k * a * (z : ℤ) - k * b) - (k * b)^2 =
          (k ^ 2 * a) * (a * (y : ℤ) * (z : ℤ) - b * ((y : ℤ) + (z : ℤ))) := by ring
    have hne : k ^ 2 * a ≠ 0 := mul_ne_zero (pow_ne_zero 2 hk.ne') ha.ne'
    rw [← sub_eq_zero, hid, mul_eq_zero, or_iff_right hne, sub_eq_zero]
  rw [← reduced_remainder_iff_one_divisor ha hb hx' hab]
  constructor
  · rintro ⟨y, z, hxy, hyz, he⟩
    exact ⟨y, z, by exact_mod_cast hxy, by exact_mod_cast hyz,
      (hbridge (hx.trans hxy) (hx.trans (hxy.trans hyz))).mp he⟩
  · rintro ⟨y, z, hxy, hyz, he⟩
    have hy : 0 ≤ y := (hx'.trans hxy).le
    have hz : 0 ≤ z := hy.trans hyz.le
    refine ⟨y.toNat, z.toNat, ?_, ?_, ?_⟩
    · exact_mod_cast (show (x : ℤ) < (y.toNat : ℤ) by simpa [Int.toNat_of_nonneg hy] using hxy)
    · exact_mod_cast (show (y.toNat : ℤ) < (z.toNat : ℤ) by
        simpa [Int.toNat_of_nonneg hy, Int.toNat_of_nonneg hz] using hyz)
    · apply (hbridge (by omega) (by omega)).mpr
      simpa [Int.toNat_of_nonneg hy, Int.toNat_of_nonneg hz] using he

end ErdosStraus
