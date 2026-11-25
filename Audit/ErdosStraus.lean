import Math.ErdosStraus

open ErdosStraus

#print axioms even_case
#print axioms three_mod_four
#print axioms two_mod_three
#print axioms five_mod_eight
#print axioms scale
#print axioms prime_outside_residual
#print axioms conjecture_iff_residual_primes

example : HasExpansion 4 := even_case 2 (by decide)
example : HasExpansion 7 := three_mod_four 1
example : HasExpansion 11 := two_mod_three 3 (by decide)
example : HasExpansion 13 := five_mod_eight 1
example : HasExpansion 33 := scale (three_mod_four 0) 11 (by decide)

#print axioms thirteen_mod_twenty
#print axioms seventeen_mod_twenty
#print axioms three_mod_seven
#print axioms five_mod_seven
#print axioms six_mod_seven
#print axioms conjecture_iff_residual840

example : HasExpansion 193 := thirteen_mod_twenty 9
example : HasExpansion 337 := seventeen_mod_twenty 16
example : HasExpansion 241 := three_mod_seven 34 (by decide)
example : HasExpansion 1321 := five_mod_seven 188 (by decide)
example : HasExpansion 601 := six_mod_seven 85 (by decide)
example : Residual840 (1009 % 840) := by decide
example : ¬ Residual840 (193 % 840) := by decide

#print axioms typeII_of_identity
#print axioms oblath_of_dvd_add_one
#print axioms conjecture_iff_residual840_without_oblath

-- Remainder 361 mod 840: the second-stage filter applies where the first sieve does not.
example : Residual840 (20521 % 840) := by decide
example : HasExpansion 20521 :=
  oblath_of_dvd_add_one (q := 31) (by decide) (by decide) (by decide)
example : (4 / (20521 : ℚ)) = 1 / 5296 + 1 / 164168 + 1 / 108679216 := by norm_num

#print axioms hasExpansion_iff_positive_of_prime_mod_four
#print axioms conjecture_iff_residual840_positive

-- The same certificate now works written in descending order.
example (hp : (20521 : ℕ).Prime) : HasExpansion 20521 :=
  (hasExpansion_iff_positive_of_prime_mod_four hp (by decide)).mpr
    ⟨108679216, 164168, 5296, by decide, by decide, by decide, by norm_num⟩
