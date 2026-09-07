import MathlibNt.SieveTheory.LiLiuGoldbachRationalEndpoints
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
#check goldbachPrime_ne_rpow_of_not_dvd
#print axioms goldbachPrime_ne_rpow_of_not_dvd
#check goldbachClosedPrimes_eq_halfOpen_rpow
#print axioms goldbachClosedPrimes_eq_halfOpen_rpow
#check goldbachS3Closed_eq_halfOpen_rpow
#print axioms goldbachS3Closed_eq_halfOpen_rpow

example (A : Finset ℕ) (N : ℕ) (z : ℝ) :
    goldbachS3Closed A N z ((N : ℝ) ^ (1 / 3 : ℝ)) =
      goldbachS3HalfOpen A N z ((N : ℝ) ^ (1 / 3 : ℝ)) := by
  simpa using goldbachS3Closed_eq_halfOpen_rpow A N 1 3 z (by norm_num)

example (A : Finset ℕ) (N : ℕ) (z : ℝ) :
    goldbachS3Closed A N z ((N : ℝ) ^ (3 / 11 : ℝ)) =
      goldbachS3HalfOpen A N z ((N : ℝ) ^ (3 / 11 : ℝ)) := by
  exact goldbachS3Closed_eq_halfOpen_rpow A N 3 11 z (by norm_num)