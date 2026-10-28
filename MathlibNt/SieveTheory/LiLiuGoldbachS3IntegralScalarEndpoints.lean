import MathlibNt.SieveTheory.LiLiuGoldbachS3IntegralScalarReduction
import MathlibNt.SieveTheory.LiLiuGoldbachS3NormalizedUpper
open Set MeasureTheory
open MathlibNt.SieveTheory.SwitchingPrinciple

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

set_option autoImplicit false

local notation "S3ScalarBody" => (fun s : ℝ =>
  (ite (s ≤ 3) 1 (ite (s ≤ 5) (1 + jurkatRichertInnerIntegral s)
    (1 + jurkatRichertInnerIntegral 5 +
      ∫ t in (5 : ℝ)..s,
        (Real.log (t - 2) + ∫ v in (3 : ℝ)..t - 2,
          jurkatRichertInnerIntegral v / v) / (t - 1)))) /
    (s * ((53 / 8 : ℝ) - s)))

/-- Exact exp-free integral for beta = 1 / 3; this is not a rational bound. -/
noncomputable def goldbachS3_oneThirdExpFreeIntegral : ℝ :=
  ∫ s in (53 / 24 : ℝ)..(45 / 8 : ℝ), S3ScalarBody s


/-- Exact identification with the unchanged production coefficient. -/
theorem goldbachS3_oneThird_coefficient_eq :
    (53 / 2 : ℝ) * Real.exp (-Real.eulerMascheroniConstant) *
      goldbachS3_primeKernelIntegral (1 / 3 : ℝ) = 53 * goldbachS3_oneThirdExpFreeIntegral := by
  have h := goldbachS3_scalar_exp_free (β := (1 / 3 : ℝ)) (by norm_num) (by norm_num)
  norm_num only at h
  exact h


/-- Exact exp-free integral for beta = 3 / 11; this is not a rational bound. -/
noncomputable def goldbachS3_threeEleventhsExpFreeIntegral : ℝ :=
  ∫ s in (265 / 88 : ℝ)..(45 / 8 : ℝ), S3ScalarBody s


/-- Exact identification with the unchanged production coefficient. -/
theorem goldbachS3_threeElevenths_coefficient_eq :
    (53 / 2 : ℝ) * Real.exp (-Real.eulerMascheroniConstant) *
      goldbachS3_primeKernelIntegral (3 / 11 : ℝ) = 53 * goldbachS3_threeEleventhsExpFreeIntegral := by
  have h := goldbachS3_scalar_exp_free (β := (3 / 11 : ℝ)) (by norm_num) (by norm_num)
  norm_num only at h
  exact h


end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig