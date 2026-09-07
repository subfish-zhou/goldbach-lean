import MathlibNt.SieveTheory.LiLiuGoldbachS3NormalizedUpper

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

theorem goldbachS3_oneThird_normalized_upper (δ ε : ℝ)
    (hδ : 0 < δ) (hε : 0 < ε) (hεu : ε < (2 : ℝ) / 15) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
      (goldbachS3Closed (goldbachDifferenceCarrier N ε) N
        ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ)) : ℝ) ≤
        ((1 - ε) * (53 / 2 : ℝ) * Real.exp (-Real.eulerMascheroniConstant) *
            goldbachS3_primeKernelIntegral (1 / 3 : ℝ) + δ) *
          (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ 2) := by
  exact goldbachS3_normalized_upper (1 / 3) δ ε (by norm_num) le_rfl hδ hε hεu

theorem goldbachS3_threeElevenths_normalized_upper (δ ε : ℝ)
    (hδ : 0 < δ) (hε : 0 < ε) (hεu : ε < (2 : ℝ) / 15) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
      (goldbachS3Closed (goldbachDifferenceCarrier N ε) N
        ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (3 / 11 : ℝ)) : ℝ) ≤
        ((1 - ε) * (53 / 2 : ℝ) * Real.exp (-Real.eulerMascheroniConstant) *
            goldbachS3_primeKernelIntegral (3 / 11 : ℝ) + δ) *
          (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ 2) := by
  exact goldbachS3_normalized_upper (3 / 11) δ ε (by norm_num) (by norm_num) hδ hε hεu

#check goldbachS3_primeKernelIntegral_nonneg
#print axioms goldbachS3_primeKernelIntegral_nonneg
#check goldbachS3_normalized_upper
#print axioms goldbachS3_normalized_upper
#check goldbachS3_oneThird_normalized_upper
#print axioms goldbachS3_oneThird_normalized_upper
#check goldbachS3_threeElevenths_normalized_upper
#print axioms goldbachS3_threeElevenths_normalized_upper

#check goldbachS3_primeKernelIntegral
#print axioms goldbachS3_primeKernelIntegral
#print goldbachS3_primeKernelIntegral
#check goldbachS3_sieveRatio
#print axioms goldbachS3_sieveRatio
#print goldbachS3_sieveRatio

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig