import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Erdős–Straus: elementary congruence cases
The open target uses strictly increasing positive denominators. The theorems
below formalize classical cases, not a solution of the conjecture. -/

namespace ErdosStraus

/-- The denominator `n` admits a decomposition with three distinct unit fractions. -/
def HasExpansion (n : ℕ) : Prop :=
  ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧
    (4 / (n : ℚ)) = 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ)

/-- Erdős Problem 242. This is a definition, not a proof or an axiom. -/
def Conjecture : Prop := ∀ n : ℕ, 2 < n → HasExpansion n

theorem even_case (k : ℕ) (hk : 2 ≤ k) : HasExpansion (2 * k) := by
  have h₁ : 0 < k := by omega
  have h₂ : k + 1 < k * (k + 1) := by
    have h := Nat.mul_le_mul_right (k + 1) hk
    omega
  refine ⟨k, k + 1, k * (k + 1), by omega, by omega, h₂, ?_⟩
  push_cast
  have hq : (0 : ℚ) < k := by exact_mod_cast h₁
  have hq' : (0 : ℚ) < (k : ℚ) + 1 := add_pos hq zero_lt_one
  field_simp [ne_of_gt hq, ne_of_gt hq']; ring

theorem three_mod_four (k : ℕ) : HasExpansion (4 * k + 3) := by
  let n := 4 * k + 3
  let a := k + 1
  let b := n * a
  have ha : 1 ≤ a := by dsimp [a]; omega
  have hn : 3 ≤ n := by dsimp [n]; omega
  have hab : a < b + 1 := by
    have h := Nat.mul_le_mul_right a hn
    dsimp [b]
    omega
  have hb : 2 ≤ b := by
    have h := Nat.mul_le_mul_right a hn
    dsimp [b]
    omega
  have hbc : b + 1 < b * (b + 1) := by
    have h := Nat.mul_le_mul_right (b + 1) hb
    omega
  refine ⟨a, b + 1, b * (b + 1), ha, hab, hbc, ?_⟩
  change (4 / (n : ℚ)) = 1 / (a : ℚ) + 1 / (↑(b + 1) : ℚ) + 1 / (↑(b * (b + 1)) : ℚ)
  have hnq : (0 : ℚ) < (n : ℚ) := by exact_mod_cast (show 0 < n by omega)
  have haq : (0 : ℚ) < (a : ℚ) := by exact_mod_cast (show 0 < a by omega)
  have hbq : (0 : ℚ) < (b : ℚ) := by exact_mod_cast (show 0 < b by omega)
  have hbp : (0 : ℚ) < (b : ℚ) + 1 := add_pos hbq zero_lt_one
  push_cast
  field_simp [ne_of_gt hnq, ne_of_gt haq, ne_of_gt hbq, ne_of_gt hbp]
  simp only [n, a, b, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  ring

theorem two_mod_three (k : ℕ) (hk : 1 ≤ k) : HasExpansion (3 * k + 2) := by
  let n := 3 * k + 2
  let a := k + 1
  have han : a < n := by dsimp [a, n]; omega
  have hna : n < n * a := by
    have h := Nat.mul_le_mul_left n (show 2 ≤ a by dsimp [a]; omega)
    omega
  refine ⟨a, n, n * a, by dsimp [a]; omega, han, hna, ?_⟩
  change (4 / (n : ℚ)) = 1 / (a : ℚ) + 1 / (n : ℚ) + 1 / (↑(n * a) : ℚ)
  have hnq : (0 : ℚ) < (n : ℚ) := by exact_mod_cast (show 0 < n by omega)
  have haq : (0 : ℚ) < (a : ℚ) := by exact_mod_cast (show 0 < a by dsimp [a]; omega)
  push_cast
  field_simp [ne_of_gt hnq, ne_of_gt haq]
  simp only [n, a, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  ring

theorem five_mod_eight (k : ℕ) : HasExpansion (8 * k + 5) := by
  let n := 8 * k + 5
  let a := k + 1
  have ha : 0 < a := by dsimp [a]; omega
  have hn : 5 ≤ n := by dsimp [n]; omega
  have hab : 2 * a < n * a := by
    have h := Nat.mul_le_mul_right a hn
    omega
  have hbc : n * a < 2 * (n * a) := by
    have h := Nat.mul_le_mul_right a hn
    omega
  refine ⟨2 * a, n * a, 2 * (n * a), by omega, hab, hbc, ?_⟩
  change (4 / (n : ℚ)) = 1 / (↑(2 * a) : ℚ) + 1 / (↑(n * a) : ℚ) +
    1 / (↑(2 * (n * a)) : ℚ)
  have hnq : (0 : ℚ) < (n : ℚ) := by exact_mod_cast (show 0 < n by omega)
  have haq : (0 : ℚ) < (a : ℚ) := by exact_mod_cast ha
  push_cast
  field_simp [ne_of_gt hnq, ne_of_gt haq]
  simp only [n, a, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  ring

theorem scale {n : ℕ} (h : HasExpansion n) (m : ℕ) (hm : 0 < m) :
    HasExpansion (n * m) := by
  obtain ⟨x, y, z, hx, hxy, hyz, h⟩ := h
  refine ⟨x * m, y * m, z * m, ?_, ?_, ?_, ?_⟩
  · have hxm := Nat.mul_pos (show 0 < x by omega) hm
    omega
  · exact Nat.mul_lt_mul_of_pos_right hxy hm
  · exact Nat.mul_lt_mul_of_pos_right hyz hm
  · push_cast
    simp only [div_mul_eq_div_div, ← add_div, h]

theorem prime_outside_residual {p : ℕ} (hp : p.Prime) (h₂ : 2 < p)
    (hres : p % 24 ≠ 1) : HasExpansion p := by
  by_cases h₃ : p = 3
  · subst p
    exact three_mod_four 0
  have hpodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · omega
  have hp3 : p % 3 ≠ 0 := by
    intro h
    have hd : 3 ∣ p := Nat.dvd_of_mod_eq_zero h
    rcases (Nat.dvd_prime hp).mp hd with he | he <;> omega
  by_cases h4 : p % 4 = 3
  · convert three_mod_four (p / 4) using 1; omega
  by_cases hm3 : p % 3 = 2
  · convert two_mod_three (p / 3) (by omega) using 1; omega
  have h8 : p % 8 = 5 := by omega
  convert five_mod_eight (p / 8) using 1; omega

/-- It suffices to treat the prime denominators congruent to one modulo 24. -/
theorem conjecture_iff_residual_primes :
    Conjecture ↔ ∀ p : ℕ, p.Prime → p % 24 = 1 → HasExpansion p := by
  constructor
  · intro h p hp hmod
    have h₂ := hp.two_le
    exact h p (by omega)
  · intro h n hn
    by_cases hev : n % 2 = 0
    · convert even_case (n / 2) (by omega) using 1; omega
    obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
    have hp2 : 2 < p := by
      have hpmin := hp.two_le
      by_contra! he
      have heq : p = 2 := by omega
      rw [heq] at hd
      exact hev (Nat.mod_eq_zero_of_dvd hd)
    have hexp : HasExpansion p := by
      by_cases hr : p % 24 = 1
      · exact h p hp hr
      · exact prime_outside_residual hp hp2 hr
    obtain ⟨m, hm⟩ := hd
    rw [hm]
    apply scale hexp
    by_contra! hz
    simp [show m = 0 by omega] at hm
    omega

end ErdosStraus
