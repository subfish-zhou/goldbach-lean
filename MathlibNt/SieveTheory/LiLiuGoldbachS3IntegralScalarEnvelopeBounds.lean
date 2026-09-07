import MathlibNt.SieveTheory.LiLiuGoldbachS3IntegralScalarPolynomial

open Set MeasureTheory
open MathlibNt.SieveTheory.SwitchingPrinciple

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The explicit rational envelope is continuous on the full original integration interval. -/
theorem goldbachS3_fullEnvelope_continuousOn :
    ContinuousOn goldbachS3_fullEnvelope (Icc (53/24 : ℝ) (45/8 : ℝ)) := by
  have hH : ContinuousOn goldbachS3_innerEnvelope (Icc (3 : ℝ) (45/8 : ℝ)) :=
    fun s hs => (goldbachS3_innerEnvelope_hasDerivAt hs.1).continuousAt.continuousWithinAt
  have hmax : ContinuousOn (fun s : ℝ => goldbachS3_innerEnvelope (max s 3))
      (Icc (53/24 : ℝ) (45/8 : ℝ)) := by
    apply hH.comp (continuous_id.max continuous_const).continuousOn
    intro s hs
    exact ⟨le_max_right _ _, max_le hs.2 (by norm_num)⟩
  apply ContinuousOn.div
  · exact (continuousOn_const.add hmax).add
      ((((continuous_id.sub continuous_const).max continuous_const).pow 4).div_const 576).continuousOn
  · exact continuousOn_id.mul (continuousOn_const.sub continuousOn_id)
  · intro s hs
    change s * ((53/8 : ℝ)-s) ≠ 0
    apply mul_ne_zero <;> linarith [hs.1, hs.2]

/-- A genuine integral comparison for the first named endpoint, with no bound hypothesis. -/
theorem goldbachS3_oneThird_integral_le_fullEnvelope :
    goldbachS3_oneThirdExpFreeIntegral ≤
      ∫ s in (53/24 : ℝ)..(45/8 : ℝ), goldbachS3_fullEnvelope s := by
  apply intervalIntegral.integral_mono_on (by norm_num)
    goldbachS3_oneThirdExpFreeIntegral_integrable
  · apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by norm_num : (53/24 : ℝ) ≤ 45/8)]
    exact goldbachS3_fullEnvelope_continuousOn
  · exact fun s hs => goldbachS3_fullEnvelope_majorizes hs

/-- A genuine integral comparison for the second named endpoint, on its unchanged interval. -/
theorem goldbachS3_threeElevenths_integral_le_fullEnvelope :
    goldbachS3_threeEleventhsExpFreeIntegral ≤
      ∫ s in (265/88 : ℝ)..(45/8 : ℝ), goldbachS3_fullEnvelope s := by
  apply intervalIntegral.integral_mono_on (by norm_num)
    goldbachS3_threeEleventhsExpFreeIntegral_integrable
  · apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by norm_num : (265/88 : ℝ) ≤ 45/8)]
    exact goldbachS3_fullEnvelope_continuousOn.mono
      (Icc_subset_Icc (by norm_num) le_rfl)
  · intro s hs
    exact goldbachS3_fullEnvelope_majorizes ⟨by linarith [hs.1], hs.2⟩

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig