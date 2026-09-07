import MathlibNt.SieveTheory.LiLiuGoldbachS3IntegralScalarMainBound
import MathlibNt.SieveTheory.LiLiuGoldbachS3CorrectionEvaluation

open MeasureTheory
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

theorem goldbachS3_oneThird_scalar_le_2360636 :
    53 * goldbachS3_oneThirdExpFreeIntegral ≤ (2360636/100000 : ℝ) := by
  rw [goldbachS3_oneThird_integral_split, mul_add]
  have hc : 53 * (∫ s in (5 : ℝ)..(45/8 : ℝ), goldbachS3_scalarCorrectionKernel s) ≤
      (1972364/10^10 : ℝ) := S3Correction.actual_correction_le_rational
  exact (add_le_add s3main4_bound hc).trans (by norm_num [s3B4])

theorem goldbachS3_threeElevenths_scalar_le_1951976 :
    53 * goldbachS3_threeEleventhsExpFreeIntegral ≤ (1951976/100000 : ℝ) := by
  rw [goldbachS3_threeElevenths_integral_split, mul_add]
  have hc : 53 * (∫ s in (5 : ℝ)..(45/8 : ℝ), goldbachS3_scalarCorrectionKernel s) ≤
      (1972364/10^10 : ℝ) := S3Correction.actual_correction_le_rational
  exact (add_le_add s3main5_bound hc).trans (by norm_num [s3B5])

theorem goldbachS3_oneThird_coefficient_le_2360636 :
    (53/2 : ℝ)*Real.exp (-Real.eulerMascheroniConstant)*
      goldbachS3_primeKernelIntegral (1/3 : ℝ) ≤ (2360636/100000 : ℝ) := by
  rw [goldbachS3_oneThird_coefficient_eq]
  exact goldbachS3_oneThird_scalar_le_2360636

theorem goldbachS3_threeElevenths_coefficient_le_1951976 :
    (53/2 : ℝ)*Real.exp (-Real.eulerMascheroniConstant)*
      goldbachS3_primeKernelIntegral (3/11 : ℝ) ≤ (1951976/100000 : ℝ) := by
  rw [goldbachS3_threeElevenths_coefficient_eq]
  exact goldbachS3_threeElevenths_scalar_le_1951976

theorem goldbachS3_normalized_upper_2360636 (δ ε : ℝ)
    (hδ : 0 < δ) (hε : 0 < ε) (hεu : ε < (2 : ℝ)/15) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
      (goldbachS3Closed (goldbachDifferenceCarrier N ε) N
        ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(1/3 : ℝ)) : ℝ) ≤
        ((1-ε)*(2360636/100000 : ℝ)+δ)*
          (SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) := by
  obtain ⟨N₀, hN₀, h⟩ := goldbachS3_normalized_upper_oneThird_exp_free δ ε hδ hε hεu
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN hEven
  have hs : 0 ≤ SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2 :=
    div_nonneg (mul_nonneg (SingularSeries.liuSingularSeries_pos N).le
      (Nat.cast_nonneg N)) (sq_nonneg _)
  exact (h N hN hEven).trans (mul_le_mul_of_nonneg_right
    (add_le_add (mul_le_mul_of_nonneg_left goldbachS3_oneThird_scalar_le_2360636
      (by linarith : 0 ≤ 1-ε)) (le_refl δ)) hs)

theorem goldbachS3_normalized_upper_1951976 (δ ε : ℝ)
    (hδ : 0 < δ) (hε : 0 < ε) (hεu : ε < (2 : ℝ)/15) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
      (goldbachS3Closed (goldbachDifferenceCarrier N ε) N
        ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(3/11 : ℝ)) : ℝ) ≤
        ((1-ε)*(1951976/100000 : ℝ)+δ)*
          (SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) := by
  obtain ⟨N₀, hN₀, h⟩ := goldbachS3_normalized_upper_threeElevenths_exp_free δ ε hδ hε hεu
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN hEven
  have hs : 0 ≤ SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2 :=
    div_nonneg (mul_nonneg (SingularSeries.liuSingularSeries_pos N).le
      (Nat.cast_nonneg N)) (sq_nonneg _)
  exact (h N hN hEven).trans (mul_le_mul_of_nonneg_right
    (add_le_add (mul_le_mul_of_nonneg_left goldbachS3_threeElevenths_scalar_le_1951976
      (by linarith : 0 ≤ 1-ε)) (le_refl δ)) hs)

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig