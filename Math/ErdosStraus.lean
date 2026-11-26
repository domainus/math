import Mathlib.Algebra.Order.Field.Rat
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

/-! ## Variable-divisor witnesses -/

/-- A Type II identity with ordering conditions sufficient for distinct denominators. -/
theorem typeII_of_identity {n a b c d : ℕ}
    (ha : 0 < a) (hd : 0 < d) (hab : a < b) (hbc : b < c * n)
    (h : 4 * a * b * c * d = c * n + a + b) : HasExpansion n := by
  have hb : 0 < b := by omega
  have hcn : 0 < c * n := by omega
  have hc : 0 < c := by
    by_contra! hz
    simp [show c = 0 by omega] at hcn
  have hn : 0 < n := by
    by_contra! hz
    simp [show n = 0 by omega] at hcn
  have had := Nat.mul_pos ha hd
  have hdcn := Nat.mul_pos hd hcn
  refine ⟨a * b * d, a * c * d * n, b * c * d * n, ?_, ?_, ?_, ?_⟩
  · exact Nat.mul_pos (Nat.mul_pos ha hb) hd
  · simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      Nat.mul_lt_mul_of_pos_left hbc had
  · simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      Nat.mul_lt_mul_of_pos_right hab hdcn
  · have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ha)
    have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
    have hc' : (c : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hc)
    have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
    have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    have hq : 4 * (a : ℚ) * b * c * d = (c : ℚ) * n + a + b := by exact_mod_cast h
    let D : ℚ := (a : ℚ) * b * c * d * n
    have hD : D ≠ 0 := mul_ne_zero
      (mul_ne_zero (mul_ne_zero (mul_ne_zero ha' hb') hc') hd') hn'
    push_cast
    have ex : 1 / ((a : ℚ) * b * d) = ((c : ℚ) * n) / D := by
      apply (div_eq_div_iff (mul_ne_zero (mul_ne_zero ha' hb') hd') hD).2
      dsimp [D]
      ring
    have ey : 1 / ((a : ℚ) * c * d * n) = (b : ℚ) / D := by
      apply (div_eq_div_iff (mul_ne_zero (mul_ne_zero (mul_ne_zero ha' hc') hd') hn') hD).2
      dsimp [D]
      ring
    have ez : 1 / ((b : ℚ) * c * d * n) = (a : ℚ) / D := by
      apply (div_eq_div_iff (mul_ne_zero (mul_ne_zero (mul_ne_zero hb' hc') hd') hn') hD).2
      dsimp [D]
      ring
    rw [ex, ey, ez, ← add_div, ← add_div]
    rw [show (c : ℚ) * n + b + a = 4 * (a : ℚ) * b * c * d by
      rw [hq, add_right_comm]]
    apply (div_eq_div_iff hn' hD).2
    dsimp [D]
    ring

/-- Obláth's divisor criterion on the residual class modulo 4. The divisor need not be prime. -/
theorem oblath_of_dvd_add_one {n q : ℕ} (hn4 : n % 4 = 1)
    (hq4 : q % 4 = 3) (hq : q ∣ n + 1) : HasExpansion n := by
  obtain ⟨b, hb⟩ := hq
  let d := (q + 1) / 4
  have hd : 0 < d := by dsimp [d]; omega
  have hqeq : 4 * d = q + 1 := by dsimp [d]; omega
  have hb0 : b ≠ 0 := by
    intro h
    simp [h] at hb
  have hb1 : b ≠ 1 := by
    intro h
    rw [h, Nat.mul_one] at hb
    omega
  have h3b : 3 * b ≤ q * b := Nat.mul_le_mul_right b (by omega)
  have hbn : b < n := by omega
  apply typeII_of_identity (n := n) (a := 1) (b := b) (c := 1) (d := d) (by decide) hd
  · omega
  · simpa using hbn
  · calc
      4 * 1 * b * 1 * d = (4 * d) * b := by ring
      _ = (q + 1) * b := by rw [hqeq]
      _ = 1 * n + 1 + b := by rw [Nat.add_mul, ← hb]; simp

/-- Refine the six-class reduction by discarding primes covered by Obláth's criterion. -/
theorem conjecture_iff_residual840_without_oblath :
    Conjecture ↔ ∀ p : ℕ, p.Prime → Residual840 (p % 840) →
      (∀ q : ℕ, q ∣ p + 1 → q % 4 ≠ 3) → HasExpansion p := by
  constructor
  · intro h p hp hr _
    exact conjecture_iff_residual840.mp h p hp hr
  · intro h
    apply conjecture_iff_residual840.mpr
    intro p hp hr
    by_cases hf : ∃ q : ℕ, q ∣ p + 1 ∧ q % 4 = 3
    · obtain ⟨q, hd, hq⟩ := hf
      have hm : (p % 840) % 4 = p % 4 := Nat.mod_mod_of_dvd _ (by decide)
      have hr4 (r : ℕ) (hr' : Residual840 r) : r % 4 = 1 := by
        rcases hr' with h1 | h2 | h3 | h4 | h5 | h6 <;> subst r <;> decide
      exact oblath_of_dvd_add_one (hm.symm.trans (hr4 _ hr)) hq hd
    · exact h p hp hr (fun q hd hq => hf ⟨q, hd, hq⟩)

/-- Positive certificates without an ordering or distinctness requirement. -/
def HasPositiveExpansion (n : ℕ) : Prop :=
  ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
    (4 / (n : ℚ)) = 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ)

private theorem no_repeated_of_prime_mod_four {p a b : ℕ} (hp : p.Prime)
    (hp4 : p % 4 = 1) (ha : 0 < a) (hb : 0 < b)
    (h : (4 / (p : ℚ)) = 2 / (a : ℚ) + 1 / (b : ℚ)) : False := by
  have hP : (0 : ℚ) < p := by exact_mod_cast hp.pos
  have hA : (0 : ℚ) < a := by exact_mod_cast ha
  have hB : (0 : ℚ) < b := by exact_mod_cast hb
  have hxq : (p : ℚ) < 2 * a := by
    have hh : (2 : ℚ) / a < 4 / p := by
      rw [h]
      exact lt_add_of_pos_right _ (one_div_pos.mpr hB)
    have hh' := (div_lt_div_iff₀ hA hP).1 hh
    calc
      (p : ℚ) = (2 * p) / 2 := by ring
      _ < (4 * a) / 2 := div_lt_div_of_pos_right hh' (by decide)
      _ = 2 * a := by ring
  have hyq : (p : ℚ) < 4 * b := by
    have hh : (1 : ℚ) / b < 4 / p := by
      rw [h]
      exact lt_add_of_pos_left _ (div_pos (by decide) hA)
    simpa only [one_mul] using (div_lt_div_iff₀ hB hP).1 hh
  have hx : p ≤ 2 * a := by exact_mod_cast hxq.le
  have hy : p ≤ 4 * b := by exact_mod_cast hyq.le
  have hc : 4 * (a : ℚ) * b = (2 * b + a) * p := by
    field_simp [hP.ne', hA.ne', hB.ne'] at h
    first | exact h | simpa [mul_comm, mul_left_comm, mul_assoc, add_mul] using h
  have hf : (2 * (a : ℚ) - p) * (4 * (b : ℚ) - p) = (p : ℚ) ^ 2 := by
    calc
      _ = 2 * (4 * (a : ℚ) * b) - 2 * ((2 * b + a) * p) + (p : ℚ) ^ 2 := by ring
      _ = _ := by rw [hc, sub_self, zero_add]
  have hf' : (2 * a - p) * (4 * b - p) = p ^ 2 := by
    exact_mod_cast (show (↑((2 * a - p) * (4 * b - p)) : ℚ) = (p : ℚ) ^ 2 by
      push_cast [Nat.cast_sub hx, Nat.cast_sub hy]
      exact hf)
  have hd : 4 * b - p ∣ p ^ 2 := ⟨2 * a - p, by rw [← hf', Nat.mul_comm]⟩
  have hmod : (4 * b - p) % 4 = 3 := by omega
  obtain ⟨k, hk, he⟩ := (Nat.dvd_prime_pow hp).mp hd
  have hcase : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hcase with rfl | rfl | rfl
  · simp [he] at hmod
  · simp [he, hp4] at hmod
  · have hsq : p ^ 2 % 4 = 1 := by rw [pow_two, Nat.mul_mod, hp4]
    simp [he, hsq] at hmod

/-- On primes congruent to one modulo four, positive certificates automatically
have distinct denominators and can be sorted. -/
theorem hasExpansion_iff_positive_of_prime_mod_four {p : ℕ}
    (hp : p.Prime) (hp4 : p % 4 = 1) : HasExpansion p ↔ HasPositiveExpansion p := by
  constructor
  · rintro ⟨a, b, c, ha, hab, hbc, h⟩
    exact ⟨a, b, c, by omega, by omega, by omega, h⟩
  · rintro ⟨a, b, c, ha, hb, hc, h⟩
    have hab : a ≠ b := by
      rintro rfl
      apply no_repeated_of_prime_mod_four hp hp4 ha hc
      rwa [show (2 : ℚ) / a = 1 / (a : ℚ) + 1 / (a : ℚ) by ring]
    have hac : a ≠ c := by
      rintro rfl
      apply no_repeated_of_prime_mod_four hp hp4 ha hb
      rwa [show (2 : ℚ) / a = 1 / (a : ℚ) + 1 / (a : ℚ) by ring, add_right_comm]
    have hbc : b ≠ c := by
      rintro rfl
      apply no_repeated_of_prime_mod_four hp hp4 hb ha
      rw [show (2 : ℚ) / b = 1 / (b : ℚ) + 1 / (b : ℚ) by ring]
      simpa only [add_assoc, add_left_comm, add_comm] using h
    rcases lt_or_gt_of_ne hab with h₁ | h₁ <;>
      rcases lt_or_gt_of_ne hac with h₂ | h₂ <;>
      rcases lt_or_gt_of_ne hbc with h₃ | h₃
    · exact ⟨a, b, c, ha, h₁, h₃, h⟩
    · exact ⟨a, c, b, ha, h₂, h₃, by simpa only [add_assoc, add_left_comm, add_comm] using h⟩
    · omega
    · exact ⟨c, a, b, hc, h₂, h₁, by simpa only [add_assoc, add_left_comm, add_comm] using h⟩
    · exact ⟨b, a, c, hb, h₁, h₂, by simpa only [add_assoc, add_left_comm, add_comm] using h⟩
    · omega
    · exact ⟨b, c, a, hb, h₃, h₂, by simpa only [add_assoc, add_left_comm, add_comm] using h⟩
    · exact ⟨c, b, a, hc, h₃, h₁, by simpa only [add_assoc, add_left_comm, add_comm] using h⟩

/-- The remaining primes may be certified by any positive triple, without
pre-sorting the denominators or checking them separately for ties. -/
theorem conjecture_iff_residual840_positive :
    Conjecture ↔ ∀ p : ℕ, p.Prime → Residual840 (p % 840) →
      (∀ q : ℕ, q ∣ p + 1 → q % 4 ≠ 3) → HasPositiveExpansion p := by
  have hm (p : ℕ) (hr : Residual840 (p % 840)) : p % 4 = 1 := by
    rw [← Nat.mod_mod_of_dvd p (show 4 ∣ 840 by decide)]
    generalize p % 840 = r at hr ⊢
    rcases hr with h | h | h | h | h | h <;> subst r <;> decide
  rw [conjecture_iff_residual840_without_oblath]
  constructor
  · intro h p hp hr hd
    exact (hasExpansion_iff_positive_of_prime_mod_four hp (hm p hr)).mp (h p hp hr hd)
  · intro h p hp hr hd
    exact (hasExpansion_iff_positive_of_prime_mod_four hp (hm p hr)).mpr (h p hp hr hd)

/-- A fixed-parameter Type II family, with c = 3 and d = 1. -/
theorem seven_mod_eleven {n : ℕ}
    (hn : n % 11 = 7) : HasExpansion n := by
  let b := 3 * (n / 11) + 2
  apply typeII_of_identity (n := n) (a := 1) (b := b) (c := 3) (d := 1)
    (by decide) (by decide)
  · dsimp [b]; omega
  · dsimp [b]; omega
  · dsimp [b]; omega

/-- A fixed-parameter Type II family, with c = 5 and d = 1. -/
theorem fifteen_mod_nineteen {n : ℕ}
    (hn : n % 19 = 15) : HasExpansion n := by
  let b := 5 * (n / 19) + 4
  apply typeII_of_identity (n := n) (a := 1) (b := b) (c := 5) (d := 1)
    (by decide) (by decide)
  · dsimp [b]; omega
  · dsimp [b]; omega
  · dsimp [b]; omega

/-- A fixed-parameter Type II family, with c = 6 and d = 1. -/
theorem nineteen_mod_twenty_three {n : ℕ}
    (hn : n % 23 = 19) : HasExpansion n := by
  let b := 6 * (n / 23) + 5
  apply typeII_of_identity (n := n) (a := 1) (b := b) (c := 6) (d := 1)
    (by decide) (by decide)
  · dsimp [b]; omega
  · dsimp [b]; omega
  · dsimp [b]; omega

/-- Remove three more congruence families after the Obláth filter. -/
theorem conjecture_iff_residual840_after_fixed_typeII :
    Conjecture ↔ ∀ p : ℕ, p.Prime → Residual840 (p % 840) →
      (∀ q : ℕ, q ∣ p + 1 → q % 4 ≠ 3) →
      p % 11 ≠ 7 → p % 19 ≠ 15 → p % 23 ≠ 19 → HasPositiveExpansion p := by
  rw [conjecture_iff_residual840_positive]
  constructor
  · intro h p hp hr hd _ _ _
    exact h p hp hr hd
  · intro h p hp hr hd
    have hp4 : p % 4 = 1 := by
      rw [← Nat.mod_mod_of_dvd p (show 4 ∣ 840 by decide)]
      generalize p % 840 = r at hr ⊢
      rcases hr with hh | hh | hh | hh | hh | hh <;> subst r <;> decide
    have lift := (hasExpansion_iff_positive_of_prime_mod_four hp hp4).mp
    by_cases h11 : p % 11 = 7
    · exact lift (seven_mod_eleven h11)
    by_cases h19 : p % 19 = 15
    · exact lift (fifteen_mod_nineteen h19)
    by_cases h23 : p % 23 = 19
    · exact lift (nineteen_mod_twenty_three h23)
    exact h p hp hr hd h11 h19 h23

/-- The ordered witness associated to Salez's (14b), with the parameter B = 1.
The hypotheses are given in multiplication-only form. -/
theorem salez14b_of_identity {n f x d e t : ℕ}
    (hf : 3 ≤ f) (hfn : f ≤ n) (hd : 0 < d) (ht : 0 < t)
    (hfour : 4 * x = n + f) (hx : x = d * e) (he : e + 1 = f * t) :
    HasExpansion n := by
  have hn : 0 < n := by omega
  have hft : f ≤ f * t := by
    simpa using Nat.mul_le_mul_left f (show 1 ≤ t by omega)
  have he2 : 2 ≤ e := by omega
  have hnt : f * t ≤ n * t := Nat.mul_le_mul_right t hfn
  have hen : e < n * t := by omega
  let y := n * d * t
  have hxy : x < y := by
    rw [hx, show y = d * (n * t) by dsimp [y]; ring]
    exact Nat.mul_lt_mul_of_pos_left hen hd
  have hxp : 0 < x := by rw [hx]; exact Nat.mul_pos hd (by omega)
  have hyp : 0 < y := lt_trans hxp hxy
  have hyz : y < e * y := by
    simpa using Nat.mul_lt_mul_of_pos_right (show 1 < e by omega) hyp
  refine ⟨x, y, e * y, hxp, hxy, hyz, ?_⟩
  have hN : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hX : (x : ℚ) ≠ 0 := by exact_mod_cast hxp.ne'
  have hY : (y : ℚ) ≠ 0 := by exact_mod_cast hyp.ne'
  have hE : (e : ℚ) ≠ 0 := by exact_mod_cast (show e ≠ 0 by omega)
  have hfour' : 4 * (x : ℚ) = (n : ℚ) + f := by exact_mod_cast hfour
  have hx' : (x : ℚ) = (d : ℚ) * e := by exact_mod_cast hx
  have hy' : (y : ℚ) = (n : ℚ) * d * t := by dsimp [y]; push_cast; rfl
  have he' : (e : ℚ) + 1 = (f : ℚ) * t := by exact_mod_cast he
  have ht' : (1 : ℚ) / y + 1 / ((e : ℚ) * y) = (f : ℚ) / ((n : ℚ) * x) := by
    calc
      _ = ((e : ℚ) + 1) / ((e : ℚ) * y) := by
        field_simp [hE, hY]
      _ = _ := by
        apply (div_eq_div_iff (mul_ne_zero hE hY) (mul_ne_zero hN hX)).2
        rw [he',hx',hy']
        ring
  push_cast
  rw [add_assoc, ht']
  calc
    (4 : ℚ) / n = ((n : ℚ) + f) / ((n : ℚ) * x) := by
      apply (div_eq_div_iff hN (mul_ne_zero hN hX)).2
      rw [← hfour']
      ring
    _ = _ := by field_simp [hN, hX]

/-- Variable-divisor form of the Type II criterion with a = d = 1. -/
theorem typeII_of_dvd_add_four {n q : ℕ} (hq11 : 11 ≤ q)
    (hq4 : q % 4 = 3) (hdiv : q ∣ n + 4) : HasExpansion n := by
  obtain ⟨k, hk⟩ := hdiv
  have hk1 : 1 ≤ k := by
    by_contra! h
    have : k = 0 := by omega
    simp [this] at hk
  let c := (q + 1) / 4
  let b := c * k - 1
  have hc : 3 ≤ c := by dsimp [c]; omega
  have hc4 : 4 * c = q + 1 := by dsimp [c]; omega
  have hck : c ≤ c * k := by simpa using Nat.mul_le_mul_left c hk1
  have hb : 1 < b := by dsimp [b]; omega
  have hbck : b + 1 = c * k := by dsimp [b]; omega
  have h : q * b + q = c * n + q + 1 := by
    calc
      q * b + q = q * (b + 1) := by ring
      _ = q * (c * k) := by rw [hbck]
      _ = c * (q * k) := by ring
      _ = c * (n + 4) := by rw [← hk]
      _ = c * n + 4 * c := by ring
      _ = _ := by rw [hc4, ← Nat.add_assoc]
  have hb2 : 2 * b ≤ q * b := Nat.mul_le_mul_right b (by omega)
  have hbn : b < c * n := by omega
  apply typeII_of_identity (n := n) (a := 1) (b := b) (c := c) (d := 1)
    (by decide) (by decide) hb hbn
  calc
    4 * 1 * b * c * 1 = (4 * c) * b := by ring
    _ = (q + 1) * b := by rw [hc4]
    _ = q * b + b := by ring
    _ = _ := by omega

/-- Reduce the remaining cases by allowing every divisor in the shifted Type II test. -/
theorem conjecture_iff_residual840_after_shifted_divisor :
    Conjecture ↔ ∀ p : ℕ, p.Prime → Residual840 (p % 840) →
      (∀ q : ℕ, q ∣ p + 1 → q % 4 ≠ 3) →
      (∀ q : ℕ, 11 ≤ q → q ∣ p + 4 → q % 4 ≠ 3) → HasExpansion p := by
  rw [conjecture_iff_residual840_without_oblath]
  constructor
  · intro h p hp hr ho _
    exact h p hp hr ho
  · intro h p hp hr ho
    by_cases hf : ∃ q : ℕ, 11 ≤ q ∧ q ∣ p + 4 ∧ q % 4 = 3
    · obtain ⟨q, hq, hd, ht⟩ := hf
      exact typeII_of_dvd_add_four hq ht hd
    · exact h p hp hr ho (fun q hq hd ht => hf ⟨q, hq, hd, ht⟩)

/-- The hypotheses for the ordered B = 1 certificate in Salez's (14b). -/
def HasSalez14bCertificate (n : ℕ) : Prop :=
  ∃ f x d e t : ℕ, 3 ≤ f ∧ f ≤ n ∧ 0 < d ∧ 0 < t ∧
    4 * x = n + f ∧ x = d * e ∧ e + 1 = f * t

/-- The shifted-divisor and Salez certificates may be applied as successive filters. -/
theorem conjecture_iff_residual840_after_salez14b :
    Conjecture ↔ ∀ p : ℕ, p.Prime → Residual840 (p % 840) →
      (∀ q : ℕ, q ∣ p + 1 → q % 4 ≠ 3) →
      (∀ q : ℕ, 11 ≤ q → q ∣ p + 4 → q % 4 ≠ 3) →
      ¬ HasSalez14bCertificate p → HasExpansion p := by
  rw [conjecture_iff_residual840_after_shifted_divisor]
  constructor
  · intro h p hp hr ho hs _
    exact h p hp hr ho hs
  · intro h p hp hr ho hs
    by_cases hc : HasSalez14bCertificate p
    · obtain ⟨f, x, d, e, t, hf, hfn, hd, ht, hfour, hx, he⟩ := hc
      exact salez14b_of_identity hf hfn hd ht hfour hx he
    · exact h p hp hr ho hs hc

/-- The Type II witness with d = 1, allowing a variable first parameter.
The bound on c*k is exactly what is needed for a < c*k − a. -/
theorem typeII_of_shifted_multiple {n a c q k : ℕ}
    (ha : 0 < a) (hq : 2 ≤ q) (hqac : q + 1 = 4 * a * c)
    (hk : n + 4 * a ^ 2 = q * k) (hsize : 2 * a < c * k) :
    HasExpansion n := by
  let b := c * k - a
  have hab : a < b := by dsimp [b]; omega
  have hba : b + a = c * k := by dsimp [b]; omega
  have he : q * b + q * a = c * n + (q * a + a) := by
    calc
      q * b + q * a = q * (b + a) := by ring
      _ = q * (c * k) := by rw [hba]
      _ = c * (q * k) := by ring
      _ = c * (n + 4 * a ^ 2) := by rw [← hk]
      _ = c * n + (4 * a * c) * a := by ring
      _ = c * n + (q * a + a) := by rw [← hqac]; ring
  have hqb : q * b = c * n + a := by omega
  have hb2 : 2 * b ≤ q * b := Nat.mul_le_mul_right b hq
  have hbn : b < c * n := by omega
  apply typeII_of_identity (n := n) (a := a) (b := b) (c := c) (d := 1)
    ha (by decide) hab hbn
  calc
    4 * a * b * c * 1 = (4 * a * c) * b := by ring
    _ = (q + 1) * b := by rw [← hqac]
    _ = q * b + b := by ring
    _ = (c * n + a) + b := by rw [hqb]

/-- A search predicate for the variable-parameter Type II witness. -/
def HasShiftedTypeIICertificate (n : ℕ) : Prop :=
  ∃ a c q k : ℕ, 0 < a ∧ 2 ≤ q ∧ q + 1 = 4 * a * c ∧
    n + 4 * a ^ 2 = q * k ∧ 2 * a < c * k

/-- The variable-parameter Type II search can further reduce the residual primes. -/
theorem conjecture_iff_residual840_after_variable_typeII :
    Conjecture ↔ ∀ p : ℕ, p.Prime → Residual840 (p % 840) →
      (∀ q : ℕ, q ∣ p + 1 → q % 4 ≠ 3) →
      (∀ q : ℕ, 11 ≤ q → q ∣ p + 4 → q % 4 ≠ 3) →
      ¬ HasSalez14bCertificate p → ¬ HasShiftedTypeIICertificate p → HasExpansion p := by
  rw [conjecture_iff_residual840_after_salez14b]
  constructor
  · intro h p hp hr ho hs hsa _
    exact h p hp hr ho hs hsa
  · intro h p hp hr ho hs hsa
    by_cases hc : HasShiftedTypeIICertificate p
    · obtain ⟨a, c, q, k, ha, hq, hqac, hk, hsize⟩ := hc
      exact typeII_of_shifted_multiple ha hq hqac hk hsize
    · exact h p hp hr ho hs hsa hc

/-- Once the first denominator is fixed, the remaining equation is equivalent
to a factorization of `(n * x)^2`. Integer subtraction avoids truncation. -/
theorem fixed_first_iff_factorization {n x y z : ℕ}
    (hn : 0 < n) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hsize : n < 4 * x) :
    (4 / (n : ℚ) = 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ)) ↔
      let a : ℤ := 4 * (x : ℤ) - (n : ℤ)
      let b : ℤ := (n : ℤ) * (x : ℤ)
      (a * (y : ℤ) - b) * (a * (z : ℤ) - b) = b ^ 2 := by
  have hnq : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
  have hxq : (0 : ℚ) < (x : ℚ) := by exact_mod_cast hx
  have hyq : (0 : ℚ) < (y : ℚ) := by exact_mod_cast hy
  have hzq : (0 : ℚ) < (z : ℚ) := by exact_mod_cast hz
  let a : ℚ := 4 * (x : ℚ) - (n : ℚ)
  let b : ℚ := (n : ℚ) * (x : ℚ)
  have hcast :
      ((4 * (x : ℤ) - (n : ℤ)) * (y : ℤ) - (n : ℤ) * (x : ℤ)) *
        ((4 * (x : ℤ) - (n : ℤ)) * (z : ℤ) - (n : ℤ) * (x : ℤ)) =
        ((n : ℤ) * (x : ℤ)) ^ 2 ↔
      (a * (y : ℚ) - b) * (a * (z : ℚ) - b) = b ^ 2 := by
    dsimp [a, b]
    norm_cast
  dsimp only
  rw [hcast]
  have hineq : (n : ℚ) < 4 * (x : ℚ) := by exact_mod_cast hsize
  have ha : a ≠ 0 := ne_of_gt (sub_pos.mpr hineq)
  have hfactor :
      (a * (y : ℚ) - b) * (a * (z : ℚ) - b) - b ^ 2 =
        a * (a * (y : ℚ) * (z : ℚ) - b * ((y : ℚ) + (z : ℚ))) := by ring
  have hequiv :
      ((a * (y : ℚ) - b) * (a * (z : ℚ) - b) = b ^ 2) ↔
      a * (y : ℚ) * (z : ℚ) = b * ((y : ℚ) + (z : ℚ)) := by
    rw [← sub_eq_zero, hfactor, mul_eq_zero, or_iff_right ha, sub_eq_zero]
  rw [hequiv]
  dsimp [a, b]
  constructor <;> intro h
  · field_simp [ne_of_gt hnq, ne_of_gt hxq, ne_of_gt hyq, ne_of_gt hzq] at h
    rw [sub_mul, sub_mul, sub_eq_iff_eq_add]
    convert h using 1 <;> ring
  · field_simp [ne_of_gt hnq, ne_of_gt hxq, ne_of_gt hyq, ne_of_gt hzq]
    rw [sub_mul, sub_mul, sub_eq_iff_eq_add] at h
    convert h using 1 <;> ring

/-- Every ordered solution has its first denominator strictly between
`n / 4` and `3n / 4` (expressed without truncated division). -/
theorem first_denominator_bounds {n x y z : ℕ}
    (hn : 0 < n) (hx : 0 < x) (hxy : x < y) (hyz : y < z)
    (h : 4 / (n : ℚ) = 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ)) :
    n < 4 * x ∧ 4 * x < 3 * n := by
  have hnq : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
  have hxq : (0 : ℚ) < (x : ℚ) := by exact_mod_cast hx
  have hxyq : (x : ℚ) < (y : ℚ) := by exact_mod_cast hxy
  have hxzq : (x : ℚ) < (z : ℚ) := by exact_mod_cast (hxy.trans hyz)
  have hyq := hxq.trans hxyq
  have hzq := hxq.trans hxzq
  have hl : 1 / (x : ℚ) < 4 / (n : ℚ) := by
    rw [h]
    exact (lt_add_of_pos_right _ (div_pos zero_lt_one hyq)).trans
      (lt_add_of_pos_right _ (div_pos zero_lt_one hzq))
  have hu : 4 / (n : ℚ) < 3 / (x : ℚ) := by
    rw [h]
    calc
      _ < 1 / (x : ℚ) + 1 / (x : ℚ) + 1 / (x : ℚ) :=
        add_lt_add (add_lt_add_left (div_lt_div_of_pos_left zero_lt_one hxq hxyq) _)
          (div_lt_div_of_pos_left zero_lt_one hxq hxzq)
      _ = _ := by ring
  have hl' := (div_lt_div_iff₀ hxq hnq).mp hl
  have hu' := (div_lt_div_iff₀ hnq hxq).mp hu
  exact ⟨by exact_mod_cast (show (n : ℚ) < 4 * (x : ℚ) by simpa using hl'),
    by exact_mod_cast hu'⟩

/-- The whole strict expansion problem reduces to integer factor equations
for first denominators in the explicit bounded interval. -/
theorem hasExpansion_iff_bounded_factorization {n : ℕ} (hn : 0 < n) :
    HasExpansion n ↔ ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧
      n < 4 * x ∧ 4 * x < 3 * n ∧
      let a : ℤ := 4 * (x : ℤ) - (n : ℤ)
      let b : ℤ := (n : ℤ) * (x : ℤ)
      (a * (y : ℤ) - b) * (a * (z : ℤ) - b) = b ^ 2 := by
  constructor
  · rintro ⟨x, y, z, hx, hxy, hyz, h⟩
    have ⟨hlo, hhi⟩ := first_denominator_bounds hn (by omega) hxy hyz h
    exact ⟨x, y, z, hx, hxy, hyz, hlo, hhi,
      (fixed_first_iff_factorization hn (by omega) (by omega) (by omega) hlo).mp h⟩
  · rintro ⟨x, y, z, hx, hxy, hyz, hlo, _, h⟩
    exact ⟨x, y, z, hx, hxy, hyz,
      (fixed_first_iff_factorization hn (by omega) (by omega) (by omega) hlo).mpr h⟩

end ErdosStraus
