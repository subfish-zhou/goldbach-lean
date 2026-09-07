import MathlibNt.SieveTheory.LiLiuGoldbachB8NormalizedMainMass

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

#check instDecidableB8NormalizedMainMass
#check goldbachB8PlusBoundingSieve_product_eq_goldbachPrimeProduct
#check goldbachB8PlusBoundingSieve_product_log_le_liuSingularSeries
#check goldbachB8Plus_normalized_cutoff_geometry
#check goldbachB8PlusSiftedCount_normalized_mainMass
#check goldbachS4_normalized_upper_mainMass

#print axioms instDecidableB8NormalizedMainMass
#print axioms goldbachB8PlusBoundingSieve_product_eq_goldbachPrimeProduct
#print axioms goldbachB8PlusBoundingSieve_product_log_le_liuSingularSeries
#print axioms goldbachB8Plus_normalized_cutoff_geometry
#print axioms goldbachB8PlusSiftedCount_normalized_mainMass
#print axioms goldbachS4_normalized_upper_mainMass

example (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (hεu : ε < (2 : ℝ) / 15) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
      (goldbachS4 (goldbachDifferenceCarrier N ε) N ((N : ℝ) ^ ((3 : ℝ) / 11)) : ℝ) ≤
        (8 + δ) * SingularSeries.liuSingularSeries N * goldbachB8PlusMainMass N /
            Real.log (N : ℝ) +
          δ * SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ 2 :=
  goldbachS4_normalized_upper_mainMass δ ε hδ hε hεu

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig