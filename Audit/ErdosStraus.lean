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
