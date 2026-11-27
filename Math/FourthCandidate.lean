import Math.SplitDivisor

namespace ErdosStraus

private def GoodFifteen (a : ℕ) : Prop :=
  a % 15 = 1 ∨ a % 15 = 2 ∨ a % 15 = 4 ∨ a % 15 = 8

private theorem goodFifteen_mul {a b : ℕ}
    (ha : GoodFifteen a) (hb : GoodFifteen b) : GoodFifteen (a*b) := by
  unfold GoodFifteen at *
  rw [Nat.mul_mod]
  rcases ha with h | h | h | h <;> rcases hb with k | k | k | k <;>
    rw [h,k] <;> decide

private theorem goodFifteen_of_factors (n : ℕ) (hn : 0 < n)
    (h : ∀ q : ℕ, q.Prime → q ∣ n → GoodFifteen q) : GoodFifteen n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h1 : n = 1
    · subst n; unfold GoodFifteen; decide
    obtain ⟨q, hq, ⟨k, hk⟩⟩ := Nat.exists_prime_and_dvd h1
    have hkpos : 0 < k := Nat.pos_of_ne_zero (fun hz => by
      rw [hz, mul_zero] at hk
      omega)
    have hkn : k < n := by
      rw [hk]
      simpa using Nat.mul_lt_mul_of_pos_right hq.one_lt hkpos
    rw [hk]
    exact goodFifteen_mul (h q hq ⟨k, hk⟩) (ih k hkn hkpos (fun r hr hrd =>
      h r hr (hrd.trans ⟨q, by simpa [mul_comm] using hk⟩)))

/-- An exact criterion for an ordered expansion at `4*x = p+15` when
`x` is even and `p` is a prime in residue class 1 or 4 modulo 15. -/
theorem fixed_first_fifteen_iff_prime_factor {p x : ℕ} (hp : p.Prime)
    (hp15 : 15 < p) (hpx : p+15 = 4*x) (hx2 : 2 ∣ x)
    (hpr : p % 15 = 1 ∨ p % 15 = 4) :
    (∃ y z : ℕ, x < y ∧ y < z ∧
      4 / (p : ℚ) = 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ)) ↔
      ∃ q : ℕ, q.Prime ∧ q ∣ x ∧
        (q % 15 = 7 ∨ q % 15 = 11 ∨ q % 15 = 13 ∨ q % 15 = 14) := by
  have hx : 0 < x := by omega
  have hbmod : (p*x) % 15 = 4 := by
    rw [Nat.mul_mod]
    rcases hpr with h | h
    · have hxr : x % 15 = 4 := by omega
      rw [h,hxr]
    · have hxr : x % 15 = 1 := by omega
      rw [h,hxr]
  let b : ℤ := (p : ℤ)*(x : ℤ)
  have hbmod' : b % 15 = 4 := by
    dsimp [b]
    exact_mod_cast hbmod
  have hcop : IsCoprime (15 : ℤ) b := ⟨-1-4*(b/15), 4, by omega⟩
  have hsize : 15*(x : ℤ) < b := by
    dsimp [b]
    exact mul_lt_mul_of_pos_right (by exact_mod_cast hp15) (by exact_mod_cast hx)
  have hpos : 0 < b := by dsimp [b]; positivity
  have hpx' : (p : ℤ)+15 = 4*(x : ℤ) := by exact_mod_cast hpx
  rw [fixed_first_iff_reduced_coprime_split (k := 1)
    hp.pos hx (by decide) hpos (by decide) hcop (by omega) (by dsimp [b]; ring) hsize]
  classical
  constructor
  · rintro ⟨r,s,hr,hrs,_,hdiv,hsum⟩
    have hs := hr.trans hrs
    have hrN : (r.toNat : ℤ) = r := Int.toNat_of_nonneg hr.le
    have hsN : (s.toNat : ℤ) = s := Int.toNat_of_nonneg hs.le
    have hdivN : r.toNat*s.toNat ∣ p*x := by
      exact_mod_cast (show (r.toNat : ℤ)*(s.toNat : ℤ) ∣ (p : ℤ)*(x : ℤ) by
        simpa only [hrN,hsN] using hdiv)
    have hsumN : 15 ∣ r.toNat+s.toNat := by
      exact_mod_cast (show (15 : ℤ) ∣ (r.toNat : ℤ)+(s.toNat : ℤ) by
        simpa only [hrN,hsN] using hsum)
    by_contra hnone
    have hg (m : ℕ) (hm : 0 < m) (hmb : m ∣ p*x) : GoodFifteen m :=
      goodFifteen_of_factors m hm (by
        intro q hq hqm
        have hqb := hqm.trans hmb
        rcases hq.dvd_mul.mp hqb with hqp | hqx
        · have hqeq := (Nat.prime_dvd_prime_iff_eq hq hp).mp hqp
          unfold GoodFifteen
          omega
        · have hnot : ¬ (q % 15 = 7 ∨ q % 15 = 11 ∨ q % 15 = 13 ∨ q % 15 = 14) :=
            fun hh => hnone ⟨q,hq,hqx,hh⟩
          obtain ⟨t, ht⟩ := hqb
          have hmt := hbmod
          rw [ht,Nat.mul_mod] at hmt
          have hqr : q%15 < 15 := Nat.mod_lt _ (by decide)
          have htr : t%15 < 15 := Nat.mod_lt _ (by decide)
          unfold GoodFifteen
          have hv : q%15 = 0 ∨ q%15 = 1 ∨ q%15 = 2 ∨ q%15 = 3 ∨ q%15 = 4 ∨ q%15 = 5 ∨ q%15 = 6 ∨ q%15 = 7 ∨ q%15 = 8 ∨ q%15 = 9 ∨ q%15 = 10 ∨ q%15 = 11 ∨ q%15 = 12 ∨ q%15 = 13 ∨ q%15 = 14 := by omega
          rcases hv with hv | hv | hv | hv | hv | hv | hv | hv | hv | hv | hv | hv | hv | hv | hv <;>
            simp [hv] at hmt hnot ⊢ <;> omega)
    have hrg := hg r.toNat (by omega) ((dvd_mul_right _ _).trans hdivN)
    have hsg := hg s.toNat (by omega) ((dvd_mul_left _ _).trans hdivN)
    have hz := Nat.mod_eq_zero_of_dvd hsumN
    rw [Nat.add_mod] at hz
    unfold GoodFifteen at hrg hsg
    omega
  · rintro ⟨q,hq,hqd,hqr⟩
    have hqB : q ∣ p*x := hqd.trans (dvd_mul_left _ _)
    have hqge : 2 < q := by have := hq.two_le; omega
    have h2qx := ((Nat.coprime_primes Nat.prime_two hq).mpr (by omega : (2 : ℕ) ≠ q)).mul_dvd_of_dvd_of_dvd hx2 hqd
    have h2qB : 2*q ∣ p*x := h2qx.trans (dvd_mul_left _ _)
    have h2qB' : (2 : ℤ)*(q : ℤ) ∣ b := by dsimp [b]; exact_mod_cast h2qB
    have hqB' : (q : ℤ) ∣ b := by dsimp [b]; exact_mod_cast hqB
    have hdiv1 (s : ℤ) (hs : 1 < s) (hd : s ∣ b) (hc : (15 : ℤ) ∣ 1+s) :
        ∃ r s : ℤ, 0 < r ∧ r < s ∧ IsCoprime r s ∧ r*s ∣ b ∧ 15 ∣ r+s :=
      ⟨1,s,by decide,hs,⟨1,0,by ring⟩,by simpa only [one_mul] using hd,hc⟩
    have hqge' : (2 : ℤ) < q := by exact_mod_cast hqge
    rcases hqr with h | h | h | h
    · refine hdiv1 (2*q) (by omega) h2qB' ⟨2*((q : ℤ)/15)+1,?_⟩
      have hi : (q : ℤ)%15 = 7 := by exact_mod_cast h
      omega
    · obtain ⟨t,ht⟩ := hqB
      have hz := hbmod
      rw [ht,Nat.mul_mod,h] at hz
      have hz' : t % 15 = 14 := by omega
      have htB : t ∣ p*x := ⟨q,by simpa [mul_comm] using ht⟩
      have hi : (t : ℤ)%15 = 14 := by exact_mod_cast hz'
      refine hdiv1 t (by omega) (by dsimp [b]; exact_mod_cast htB) ⟨(t : ℤ)/15+1, by omega⟩
    · have hi : (q : ℤ)%15 = 13 := by exact_mod_cast h
      have hodd : ¬ (2 : ℕ) ∣ q := ((Nat.coprime_primes Nat.prime_two hq).mpr (by omega : (2 : ℕ) ≠ q)) |> Nat.prime_two.coprime_iff_not_dvd.mp
      have hi2N : q % 2 = 1 := by
        have ht : q%2 ≠ 0 := fun h0 => hodd (Nat.dvd_of_mod_eq_zero h0)
        omega
      have hi2 : (q : ℤ)%2 = 1 := by exact_mod_cast hi2N
      exact ⟨2,q,by decide,hqge',⟨-((q : ℤ)/2),1,by omega⟩,h2qB',⟨(q : ℤ)/15+1,by omega⟩⟩
    · have hi : (q : ℤ)%15 = 14 := by exact_mod_cast h
      exact hdiv1 q (by omega) hqB' ⟨(q : ℤ)/15+1,by omega⟩

/-- Fourth-candidate specialization to the six residual classes modulo 840. -/
theorem residual840_fourth_candidate_iff {p : ℕ} (hp : p.Prime)
    (hr : Residual840 (p % 840)) :
    let x := (p+15)/4
    (∃ y z : ℕ, x < y ∧ y < z ∧
      4 / (p : ℚ) = 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ)) ↔
      ∃ q : ℕ, q.Prime ∧ q ∣ x ∧
        (q % 15 = 7 ∨ q % 15 = 11 ∨ q % 15 = 13 ∨ q % 15 = 14) := by
  dsimp only
  have hp2 := hp.two_le
  obtain h | h | h | h | h | h := hr
  all_goals
    apply fixed_first_fifteen_iff_prime_factor hp <;> omega

end ErdosStraus
