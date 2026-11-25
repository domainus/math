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
