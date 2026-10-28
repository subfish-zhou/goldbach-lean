import MathlibNt.SieveTheory.LiLiuGoldbachB9SplitIntegralReduction
import MathlibNt.SieveTheory.LiLiuGoldbachS3CorrectionEvaluation

open Set MeasureTheory
open scoped Interval
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.G9Analytic
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- The production logarithmic polynomial, with the literal split weights. -/
def envelope : ℝ :=
  (36 / 5 : ℝ) * (∫ u in (4 / 53 : ℝ)..(1 / 10),
    S3Correction.L (1 - 3 * u) / (u * (1 - u)^2)) +
  8 * (∫ u in (1 / 10 : ℝ)..(1 / 3),
    S3Correction.L (1 - 3 * u) / (u * (1 - u)))


theorem continuousOn_envelope_kernel (k : ℕ) :
    ContinuousOn (fun u : ℝ => S3Correction.L (1-3*u)/(u*(1-u)^k))
      (Icc (4/53 : ℝ) (1/3)) := by
  have hc : Continuous (fun u : ℝ => S3Correction.L (1-3*u)) := by
    unfold S3Correction.L
    fun_prop
  apply hc.continuousOn.div (continuousOn_id.mul ((continuousOn_const.sub continuousOn_id).pow k))
  intro u hu
  exact mul_ne_zero (by dsimp; linarith [hu.1])
    (pow_ne_zero k (by change 1-u ≠ 0; linarith [hu.2]))

theorem actual_le_envelope : goldbachB9PaperSplitIntegral ≤ envelope := by
  rw [goldbachB9PaperSplitIntegral_eq_singleIntegrals]
  unfold envelope
  have hl : (∫ u in (4/53 : ℝ)..(1/10), Real.log (2-3*u)/(u*(1-u)^2)) ≤
      ∫ u in (4/53 : ℝ)..(1/10), S3Correction.L (1-3*u)/(u*(1-u)^2) := by
    apply intervalIntegral.integral_mono_on (by norm_num)
    · apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le (by norm_num : (4/53 : ℝ) ≤ 1/10)]
      exact continuousOn_goldbachB9WeightedSingleIntegrand.mono (Icc_subset_Icc_right (by norm_num))
    · apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le (by norm_num : (4/53 : ℝ) ≤ 1/10)]
      exact (continuousOn_envelope_kernel 2).mono (Icc_subset_Icc_right (by norm_num))
    · intro u hu
      have h := S3Correction.log_le_L (by linarith [hu.2] : 0 ≤ 1-3*u)
      rw [show (1:ℝ)+(1-3*u) = 2-3*u by ring] at h
      exact div_le_div_of_nonneg_right h (by have := hu.1; positivity)
  have hh : (∫ u in (1/10 : ℝ)..(1/3), Real.log (2-3*u)/(u*(1-u))) ≤
      ∫ u in (1/10 : ℝ)..(1/3), S3Correction.L (1-3*u)/(u*(1-u)) := by
    apply intervalIntegral.integral_mono_on (by norm_num)
    · apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le (by norm_num : (1/10 : ℝ) ≤ 1/3)]
      exact continuousOn_goldbachB9SingleIntegrand.mono (Icc_subset_Icc_left (by norm_num))
    · apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le (by norm_num : (1/10 : ℝ) ≤ 1/3)]
      simpa only [pow_one] using
        (continuousOn_envelope_kernel 1).mono (Icc_subset_Icc_left (by norm_num))
    · intro u hu
      have h := S3Correction.log_le_L (by linarith [hu.2] : 0 ≤ 1-3*u)
      rw [show (1:ℝ)+(1-3*u) = 2-3*u by ring] at h
      exact div_le_div_of_nonneg_right h (mul_nonneg (by linarith [hu.1]) (by linarith [hu.2]))
  exact add_le_add (mul_le_mul_of_nonneg_left hl (by norm_num))
    (mul_le_mul_of_nonneg_left hh (by norm_num))

end
end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.G9Analytic
