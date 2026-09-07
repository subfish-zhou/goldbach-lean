import MathlibNt.SieveTheory.LiLiuGoldbachB9NormalizedMainMass

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

#check goldbachB9Plus_upperErrSum_le_levelRemainder
#check goldbachB9Plus_upperErrSum_log_saving
#check goldbachB9PlusSiftedCount_upper_paid
#check goldbachB9PlusBoundingSieve_product_eq_goldbachPrimeProduct
#check goldbachB9PlusBoundingSieve_product_log_le_liuSingularSeries
#check goldbachB9Plus_normalized_cutoff_geometry
#check goldbachB9PlusSiftedCount_normalized_mainMass
#check goldbachS5Closed_normalized_upper_mainMass

#print axioms goldbachB9Plus_upperErrSum_le_levelRemainder
#print axioms goldbachB9Plus_upperErrSum_log_saving
#print axioms goldbachB9PlusSiftedCount_upper_paid
#print axioms goldbachB9PlusBoundingSieve_product_eq_goldbachPrimeProduct
#print axioms goldbachB9PlusBoundingSieve_product_log_le_liuSingularSeries
#print axioms goldbachB9Plus_normalized_cutoff_geometry
#print axioms goldbachB9PlusSiftedCount_normalized_mainMass
#print axioms goldbachS5Closed_normalized_upper_mainMass

example (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (hεu : ε < (2 : ℝ) / 15) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
      (goldbachS5Closed (goldbachDifferenceCarrier N ε) N
        ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ)) : ℝ) ≤
          (8 + δ) * SingularSeries.liuSingularSeries N * goldbachB9PlusMainMass N /
            Real.log (N : ℝ) +
          δ * (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ 2) :=
  goldbachS5Closed_normalized_upper_mainMass δ ε hδ hε hεu

example (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
      (goldbachS5Closed (goldbachDifferenceCarrier N (1 / 15)) N
        ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ)) : ℝ) ≤
          (8 + δ) * SingularSeries.liuSingularSeries N * goldbachB9PlusMainMass N /
            Real.log (N : ℝ) +
          δ * (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ 2) :=
  goldbachS5Closed_normalized_upper_mainMass δ (1 / 15) hδ (by norm_num) (by norm_num)

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig