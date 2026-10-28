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


end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig