import Math.ErdosStraus
import Math.ReducedRemainder
import Math.SecondCandidate

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

#print axioms seven_mod_eleven
#print axioms fifteen_mod_nineteen
#print axioms nineteen_mod_twenty_three
#print axioms conjecture_iff_residual840_after_fixed_typeII

example : Residual840 (1129 % 840) := by decide
-- 1130 = 2 * 5 * 113; none of its divisors is 3 modulo 4.
example : HasExpansion 1129 := seven_mod_eleven (by decide)
-- Here b = 308 and c = 3.
example : (4 / (1129 : ℚ)) = 1 / 308 + 1 / 3387 + 1 / 1043196 := by norm_num

#print axioms salez14b_of_identity
#print axioms typeII_of_dvd_add_four
#print axioms conjecture_iff_residual840_after_shifted_divisor
#print axioms conjecture_iff_residual840_after_salez14b

example : HasExpansion 3049 :=
  typeII_of_dvd_add_four (q := 43) (by decide) (by decide) (by decide)
example : (4 / (3049 : ℚ)) = 1 / 780 + 1 / 33539 + 1 / 26160420 := by norm_num
example : HasSalez14bCertificate 1009 :=
  ⟨3, 253, 23, 11, 4, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide⟩
example : HasExpansion 1009 :=
  salez14b_of_identity (f := 3) (x := 253) (d := 23) (e := 11) (t := 4)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
example : (4 / (1009 : ℚ)) = 1 / 253 + 1 / 92828 + 1 / 1021108 := by norm_num

#print axioms typeII_of_shifted_multiple
#print axioms conjecture_iff_residual840_after_variable_typeII

example : HasExpansion 2521 :=
  typeII_of_shifted_multiple (a := 4) (c := 3) (q := 47) (k := 55)
    (by decide) (by decide) (by decide) (by decide) (by decide)
example : (4 / (2521 : ℚ)) = 1 / 644 + 1 / 30252 + 1 / 1217643 := by norm_num

example : HasExpansion 66529 :=
  typeII_of_shifted_multiple (a := 8) (c := 3) (q := 95) (k := 703)
    (by decide) (by decide) (by decide) (by decide) (by decide)
example : (4 / (66529 : ℚ)) = 1 / 16808 + 1 / 1596696 + 1 / 419332287 := by norm_num

#print axioms fixed_first_iff_factorization

example : HasExpansion 3842281 :=
  typeII_of_shifted_multiple (a := 2) (c := 6) (q := 47) (k := 81751)
    (by decide) (by decide) (by decide) (by decide) (by decide)
example : (4 / (3842281 : ℚ)) = 1 / 981008 + 1 / 46107372 + 1 / 11307925197744 :=
  (fixed_first_iff_factorization
    (n := 3842281) (x := 981008) (y := 46107372) (z := 11307925197744)
    (by decide) (by decide) (by decide) (by decide) (by decide)).mpr (by decide)

example : HasExpansion 5410441 :=
  typeII_of_shifted_multiple (a := 2) (c := 24) (q := 191) (k := 28327)
    (by decide) (by decide) (by decide) (by decide) (by decide)
example : (4 / (5410441 : ℚ)) = 1 / 1359692 + 1 / 259701168 + 1 / 88278400130064 :=
  (fixed_first_iff_factorization
    (n := 5410441) (x := 1359692) (y := 259701168) (z := 88278400130064)
    (by decide) (by decide) (by decide) (by decide) (by decide)).mpr (by decide)

example : HasExpansion 25569769 :=
  typeII_of_shifted_multiple (a := 4) (c := 3) (q := 47) (k := 544039)
    (by decide) (by decide) (by decide) (by decide) (by decide)
example : (4 / (25569769 : ℚ)) = 1 / 6528452 + 1 / 306837228 + 1 / 125198257175691 :=
  (fixed_first_iff_factorization
    (n := 25569769) (x := 6528452) (y := 306837228) (z := 125198257175691)
    (by decide) (by decide) (by decide) (by decide) (by decide)).mpr (by decide)

example : HasExpansion 86083321 :=
  typeII_of_shifted_multiple (a := 16) (c := 524) (q := 33535) (k := 2567)
    (by decide) (by decide) (by decide) (by decide) (by decide)
example : (4 / (86083321 : ℚ)) = 1 / 21521472 + 1 / 721722563264 + 1 / 60673952879118768 :=
  (fixed_first_iff_factorization
    (n := 86083321) (x := 21521472) (y := 721722563264) (z := 60673952879118768)
    (by decide) (by decide) (by decide) (by decide) (by decide)).mpr (by decide)

#print axioms first_denominator_bounds
#print axioms hasExpansion_iff_bounded_factorization

-- The factor-pair search gives an ordered solution with its 27th candidate x.
example : HasExpansion 8803369 :=
  (hasExpansion_iff_bounded_factorization (by decide)).mpr
    ⟨2200869, 181085300330, 3293760527702370, by decide, by decide, by decide,
      by decide, by decide, by decide⟩

#print axioms reduced_remainder_iff_one_divisor
#print axioms fixed_first_iff_reduced_one_divisor

example : HasExpansion 6 := by
  have hab : IsCoprime (1 : ℤ) 6 := ⟨1, 0, by decide⟩
  obtain ⟨y, z, hy, hz, h⟩ :=
    (fixed_first_iff_reduced_one_divisor (n := 6) (x := 2) (k := 2)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hab (by decide) (by decide)).mpr
      ⟨3, by decide, by decide, ⟨12, by decide⟩, ⟨9, by decide⟩, by decide⟩
  exact ⟨2, y, z, by decide, hy, hz, h⟩

example : HasExpansion 13 := by
  have hab : IsCoprime (3 : ℤ) 52 := ⟨-17, 1, by decide⟩
  obtain ⟨y, z, hy, hz, h⟩ :=
    (fixed_first_iff_reduced_one_divisor (n := 13) (x := 4) (k := 1)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hab (by decide) (by decide)).mpr
      ⟨2, by decide, by decide, ⟨1352, by decide⟩, ⟨18, by decide⟩, by decide⟩
  exact ⟨4, y, z, by decide, hy, hz, h⟩

#print axioms fixed_first_seven_of_factor
#print axioms second_candidate_iff_prime_factor
#print axioms residual840_second_candidate_iff

-- The residue-five construction applies even though no divisor of x is 6 mod 7.
example : HasExpansion 66721 := by
  have hcop : IsCoprime (7 : ℤ) (66721 * 16682) :=
    ⟨-318011349, 2, by decide⟩
  obtain ⟨y, z, hy, hz, he⟩ := fixed_first_seven_of_factor
    (n := 66721) (x := 16682) (q := 19) (t := 29290519)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) hcop (by decide)
  exact ⟨16682, y, z, by decide, hy, hz, he⟩

example : (4 / (66721 : ℚ)) = 1/16682 + 1/175743114 + 1/1669559583 :=
  (fixed_first_iff_factorization
    (n := 66721) (x := 16682) (y := 175743114) (z := 1669559583)
    (by decide) (by decide) (by decide) (by decide) (by decide)).mpr (by decide)
