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

/-! ## The classical sieve modulo 840

The witnesses below specialize the Type I and Type II constructions in
Elsholtz–Tao, Proposition 1.9 and §10 (arXiv:1107.1010).
-/

/-- Type I with a = 1, d = 5, f = 7. -/
theorem thirteen_mod_twenty (k : ℕ) : HasExpansion (20 * k + 13) := by
  let n := 20 * k + 13
  let b := 3 * k + 2
  let c := k + 1
  refine ⟨5 * c, 5 * b * c, 5 * b * n, by dsimp [c]; omega, ?_, ?_, ?_⟩
  · have h := Nat.mul_lt_mul_of_pos_right (show 1 < b by dsimp [b]; omega)
      (show 0 < 5 * c by dsimp [c]; omega)
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h
  · exact Nat.mul_lt_mul_of_pos_left (show c < n by dsimp [c, n]; omega)
      (show 0 < 5 * b by dsimp [b]; omega)
  · change 4 / (n : ℚ) = 1 / (↑(5 * c) : ℚ) + 1 / (↑(5 * b * c) : ℚ) +
      1 / (↑(5 * b * n) : ℚ)
    have hnq : (0 : ℚ) < n := by exact_mod_cast (show 0 < n by dsimp [n]; omega)
    have hbq : (0 : ℚ) < b := by exact_mod_cast (show 0 < b by dsimp [b]; omega)
    have hcq : (0 : ℚ) < c := by exact_mod_cast (show 0 < c by dsimp [c]; omega)
    push_cast
    field_simp [ne_of_gt hnq, ne_of_gt hbq, ne_of_gt hcq, show (5 : ℚ) ≠ 0 by decide]
    have h5 : (5 : ℚ) ≠ 0 := by decide
    have h5b := mul_ne_zero h5 (ne_of_gt hbq)
    rw [eq_div_iff (mul_ne_zero
      (mul_ne_zero (mul_ne_zero h5 (ne_of_gt hcq)) (mul_ne_zero h5b (ne_of_gt hcq)))
      (mul_ne_zero h5b (ne_of_gt hnq)))]
    simp only [n, b, c, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    ring

/-- Type I with a = 1, d = 5, f = 3. -/
theorem seventeen_mod_twenty (k : ℕ) : HasExpansion (20 * k + 17) := by
  let n := 20 * k + 17
  let b := 7 * k + 6
  let c := k + 1
  refine ⟨5 * c, 5 * b * c, 5 * b * n, by dsimp [c]; omega, ?_, ?_, ?_⟩
  · have h := Nat.mul_lt_mul_of_pos_right (show 1 < b by dsimp [b]; omega)
      (show 0 < 5 * c by dsimp [c]; omega)
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h
  · exact Nat.mul_lt_mul_of_pos_left (show c < n by dsimp [c, n]; omega)
      (show 0 < 5 * b by dsimp [b]; omega)
  · change 4 / (n : ℚ) = 1 / (↑(5 * c) : ℚ) + 1 / (↑(5 * b * c) : ℚ) +
      1 / (↑(5 * b * n) : ℚ)
    have hnq : (0 : ℚ) < n := by exact_mod_cast (show 0 < n by dsimp [n]; omega)
    have hbq : (0 : ℚ) < b := by exact_mod_cast (show 0 < b by dsimp [b]; omega)
    have hcq : (0 : ℚ) < c := by exact_mod_cast (show 0 < c by dsimp [c]; omega)
    push_cast
    field_simp [ne_of_gt hnq, ne_of_gt hbq, ne_of_gt hcq, show (5 : ℚ) ≠ 0 by decide]
    have h5 : (5 : ℚ) ≠ 0 := by decide
    have h5b := mul_ne_zero h5 (ne_of_gt hbq)
    rw [eq_div_iff (mul_ne_zero
      (mul_ne_zero (mul_ne_zero h5 (ne_of_gt hcq)) (mul_ne_zero h5b (ne_of_gt hcq)))
      (mul_ne_zero h5b (ne_of_gt hnq)))]
    simp only [n, b, c, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    ring

/-- Type II with a = d = 1 and f = 7. -/
theorem three_mod_seven (k : ℕ) (hk : 1 ≤ k) : HasExpansion (7 * k + 3) := by
  let n := 7 * k + 3
  let b := 2 * k + 1
  refine ⟨b, 2 * n, b * (2 * n), by dsimp [b]; omega, by dsimp [n, b]; omega, ?_, ?_⟩
  · have h := Nat.mul_lt_mul_of_pos_right (show 1 < b by dsimp [b]; omega)
      (show 0 < 2 * n by dsimp [n]; omega)
    simpa using h
  · change 4 / (n : ℚ) = 1 / (b : ℚ) + 1 / (↑(2 * n) : ℚ) + 1 / (↑(b * (2 * n)) : ℚ)
    have hnq : (0 : ℚ) < n := by exact_mod_cast (show 0 < n by dsimp [n]; omega)
    have hbq : (0 : ℚ) < b := by exact_mod_cast (show 0 < b by dsimp [b]; omega)
    push_cast
    field_simp [ne_of_gt hnq, ne_of_gt hbq, show (2 : ℚ) ≠ 0 by decide]
    simp only [n, b, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    ring

/-- Type II with a = 2, d = 1 and f = 7. -/
theorem five_mod_seven (k : ℕ) (hk : 2 ≤ k) : HasExpansion (7 * k + 5) := by
  let n := 7 * k + 5
  let b := k + 1
  refine ⟨2 * b, 2 * n, b * n, by dsimp [b]; omega, by dsimp [n, b]; omega, ?_, ?_⟩
  · exact Nat.mul_lt_mul_of_pos_right (show 2 < b by dsimp [b]; omega)
      (show 0 < n by dsimp [n]; omega)
  · change 4 / (n : ℚ) = 1 / (↑(2 * b) : ℚ) + 1 / (↑(2 * n) : ℚ) + 1 / (↑(b * n) : ℚ)
    have hnq : (0 : ℚ) < n := by exact_mod_cast (show 0 < n by dsimp [n]; omega)
    have hbq : (0 : ℚ) < b := by exact_mod_cast (show 0 < b by dsimp [b]; omega)
    push_cast
    field_simp [ne_of_gt hnq, ne_of_gt hbq, show (2 : ℚ) ≠ 0 by decide]
    simp only [n, b, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    ring

/-- Type II with a = 1, d = 2 and f = 7. -/
theorem six_mod_seven (k : ℕ) (hk : 1 ≤ k) : HasExpansion (7 * k + 6) := by
  let n := 7 * k + 6
  let b := k + 1
  refine ⟨2 * b, 2 * n, b * (2 * n), by dsimp [b]; omega, by dsimp [n, b]; omega, ?_, ?_⟩
  · have h := Nat.mul_lt_mul_of_pos_right (show 1 < b by dsimp [b]; omega)
      (show 0 < 2 * n by dsimp [n]; omega)
    simpa using h
  · change 4 / (n : ℚ) = 1 / (↑(2 * b) : ℚ) + 1 / (↑(2 * n) : ℚ) +
      1 / (↑(b * (2 * n)) : ℚ)
    have hnq : (0 : ℚ) < n := by exact_mod_cast (show 0 < n by dsimp [n]; omega)
    have hbq : (0 : ℚ) < b := by exact_mod_cast (show 0 < b by dsimp [b]; omega)
    push_cast
    field_simp [ne_of_gt hnq, ne_of_gt hbq, show (2 : ℚ) ≠ 0 by decide]
    simp only [n, b, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    ring

/-- The six square residues among integers coprime to 840. -/
def Residual840 (r : ℕ) : Prop :=
  r = 1 ∨ r = 121 ∨ r = 169 ∨ r = 289 ∨ r = 361 ∨ r = 529

instance (r : ℕ) : Decidable (Residual840 r) := inferInstanceAs
  (Decidable (r = 1 ∨ r = 121 ∨ r = 169 ∨ r = 289 ∨ r = 361 ∨ r = 529))

private def Sieve840Hyp (r : ℕ) : Prop :=
  r % 24 = 1 ∧ r % 5 ≠ 0 ∧ r % 7 ≠ 0 ∧
    r % 20 ≠ 13 ∧ r % 20 ≠ 17 ∧ r % 7 ≠ 3 ∧ r % 7 ≠ 5 ∧ r % 7 ≠ 6

instance (r : ℕ) : Decidable (Sieve840Hyp r) := by
  unfold Sieve840Hyp
  infer_instance

set_option maxRecDepth 4096 in
private theorem residue840_table (r : Fin 840) :
    Sieve840Hyp r.val ↔ Residual840 r.val := by
  let test := fun n : ℕ => decide (Sieve840Hyp n ↔ Residual840 n)
  have ht : (List.range 840).all test = true := by decide
  exact of_decide_eq_true (List.all_eq_true.mp ht r.val (List.mem_range.mpr r.isLt))

/-- Only primes in the six classical residue classes modulo 840 still need solving. -/
theorem conjecture_iff_residual840 :
    Conjecture ↔ ∀ p : ℕ, p.Prime → Residual840 (p % 840) → HasExpansion p := by
  constructor
  · intro h p hp hr
    have hh := hp.two_le
    have h2 : p ≠ 2 := by
      intro h2
      subst p
      exact (by decide : ¬ Residual840 (2 % 840)) hr
    exact h p (by omega)
  · intro h
    apply conjecture_iff_residual_primes.mpr
    intro p hp h24
    have hh := hp.two_le
    have h25 : 25 ≤ p := by omega
    by_cases h13 : p % 20 = 13
    · convert thirteen_mod_twenty (p / 20) using 1; omega
    by_cases h17 : p % 20 = 17
    · convert seventeen_mod_twenty (p / 20) using 1; omega
    by_cases h3 : p % 7 = 3
    · convert three_mod_seven (p / 7) (by omega) using 1; omega
    by_cases h5 : p % 7 = 5
    · convert five_mod_seven (p / 7) (by omega) using 1; omega
    by_cases h6 : p % 7 = 6
    · convert six_mod_seven (p / 7) (by omega) using 1; omega
    have h5nz : p % 5 ≠ 0 := by
      intro hm
      rcases (Nat.dvd_prime hp).mp (Nat.dvd_of_mod_eq_zero hm) with hh | hh <;> omega
    have h7nz : p % 7 ≠ 0 := by
      intro hm
      rcases (Nat.dvd_prime hp).mp (Nat.dvd_of_mod_eq_zero hm) with hh | hh <;> omega
    let r : Fin 840 := ⟨p % 840, Nat.mod_lt _ (by decide)⟩
    have hmod24 : r.val % 24 = p % 24 := Nat.mod_mod_of_dvd _ (by decide)
    have hmod5 : r.val % 5 = p % 5 := Nat.mod_mod_of_dvd _ (by decide)
    have hmod7 : r.val % 7 = p % 7 := Nat.mod_mod_of_dvd _ (by decide)
    have hmod20 : r.val % 20 = p % 20 := Nat.mod_mod_of_dvd _ (by decide)
    apply h p hp
    exact (residue840_table r).mp ⟨hmod24.trans h24, hmod5 ▸ h5nz, hmod7 ▸ h7nz,
      hmod20 ▸ h13, hmod20 ▸ h17, hmod7 ▸ h3, hmod7 ▸ h5, hmod7 ▸ h6⟩

end ErdosStraus
