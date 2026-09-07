import MathlibNt.SieveTheory.LiLiuGoldbachS3IntegralScalarMainBound
import MathlibNt.SieveTheory.LiLiuGoldbachS3CorrectionEvaluation

open MeasureTheory
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

theorem goldbachS3_oneThird_scalar_le_retained236056871187 :
    53 * goldbachS3_oneThirdExpFreeIntegral ≤ (236056871187/10000000000 : ℝ) := by
  rw [goldbachS3_oneThird_integral_split, mul_add]
  have hc : 53 * (∫ s in (5 : ℝ)..(45/8 : ℝ), goldbachS3_scalarCorrectionKernel s) ≤
      (1972364/10^10 : ℝ) := S3Correction.actual_correction_le_rational
  exact (add_le_add s3main4_bound hc).trans (by norm_num [s3B4])

theorem goldbachS3_threeElevenths_scalar_le_retained195190815363 :
    53 * goldbachS3_threeEleventhsExpFreeIntegral ≤ (195190815363/10000000000 : ℝ) := by
  rw [goldbachS3_threeElevenths_integral_split, mul_add]
  have hc : 53 * (∫ s in (5 : ℝ)..(45/8 : ℝ), goldbachS3_scalarCorrectionKernel s) ≤
      (1972364/10^10 : ℝ) := S3Correction.actual_correction_le_rational
  exact (add_le_add s3main5_bound hc).trans (by norm_num [s3B5])

theorem goldbachS3_oneThird_coefficient_le_retained236056871187 :
    (53/2 : ℝ)*Real.exp (-Real.eulerMascheroniConstant)*
      goldbachS3_primeKernelIntegral (1/3 : ℝ) ≤ (236056871187/10000000000 : ℝ) := by
  rw [goldbachS3_oneThird_coefficient_eq]
  exact goldbachS3_oneThird_scalar_le_retained236056871187

theorem goldbachS3_threeElevenths_coefficient_le_retained195190815363 :
    (53/2 : ℝ)*Real.exp (-Real.eulerMascheroniConstant)*
      goldbachS3_primeKernelIntegral (3/11 : ℝ) ≤ (195190815363/10000000000 : ℝ) := by
  rw [goldbachS3_threeElevenths_coefficient_eq]
  exact goldbachS3_threeElevenths_scalar_le_retained195190815363

theorem goldbachS3_normalized_upper_retained236056871187 (δ ε : ℝ)
    (hδ : 0 < δ) (hε : 0 < ε) (hεu : ε < (2 : ℝ)/15) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
      (goldbachS3Closed (goldbachDifferenceCarrier N ε) N
        ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(1/3 : ℝ)) : ℝ) ≤
        ((1-ε)*(236056871187/10000000000 : ℝ)+δ)*
          (SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) := by
  obtain ⟨N₀, hN₀, h⟩ := goldbachS3_normalized_upper_oneThird_exp_free δ ε hδ hε hεu
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN hEven
  have hs : 0 ≤ SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2 :=
    div_nonneg (mul_nonneg (SingularSeries.liuSingularSeries_pos N).le
      (Nat.cast_nonneg N)) (sq_nonneg _)
  exact (h N hN hEven).trans (mul_le_mul_of_nonneg_right
    (add_le_add (mul_le_mul_of_nonneg_left goldbachS3_oneThird_scalar_le_retained236056871187
      (by linarith : 0 ≤ 1-ε)) (le_refl δ)) hs)

theorem goldbachS3_normalized_upper_retained195190815363 (δ ε : ℝ)
    (hδ : 0 < δ) (hε : 0 < ε) (hεu : ε < (2 : ℝ)/15) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
      (goldbachS3Closed (goldbachDifferenceCarrier N ε) N
        ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(3/11 : ℝ)) : ℝ) ≤
        ((1-ε)*(195190815363/10000000000 : ℝ)+δ)*
          (SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) := by
  obtain ⟨N₀, hN₀, h⟩ := goldbachS3_normalized_upper_threeElevenths_exp_free δ ε hδ hε hεu
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN hEven
  have hs : 0 ≤ SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2 :=
    div_nonneg (mul_nonneg (SingularSeries.liuSingularSeries_pos N).le
      (Nat.cast_nonneg N)) (sq_nonneg _)
  exact (h N hN hEven).trans (mul_le_mul_of_nonneg_right
    (add_le_add (mul_le_mul_of_nonneg_left goldbachS3_threeElevenths_scalar_le_retained195190815363
      (by linarith : 0 ≤ 1-ε)) (le_refl δ)) hs)

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig