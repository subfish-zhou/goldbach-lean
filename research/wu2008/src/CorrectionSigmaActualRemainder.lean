import CorrectionFiveHfReduction

noncomputable section
namespace CorrectionSigmaVariable
open Real Set MeasureTheory NodeExtension FirstFeedbackIntegrals OriginalProfileSigmaPayment
open Wu04WholeCollection
open scoped Interval

/-- The new inner payment is bounded by the exact integrand of the still-unpaid actual sigma. -/
theorem variation_outer_density_le {t : ℝ} (ht : 1 ≤ t) :
    variationMass t/t ≤ sigma 3 (t+2) (t+1)/t-SigmaInnerProfile.weight t := by
  have h := div_le_div_of_nonneg_right (kernel_add_variation_le_sigma ht) (by linarith : 0 ≤ t)
  unfold SigmaInnerProfile.weight
  rw [add_div] at h
  linarith only [h]

/-- Literal actual-profile remainder; the numerator and the original denominator are unchanged. -/
theorem intrinsicSigmaUnpaid_integral : CorrectionD0Joint.intrinsicSigmaUnpaid=
    (∫ t in (1:ℝ)..3,nineProfile NineFeedbackStrength.originalH t*
      (sigma 3 (t+2) (t+1)/t-SigmaInnerProfile.weight t))/(1-D0) := by
  have hp := nineProfile_integrable NineFeedbackStrength.originalH
  have hi := (profile_div_integrable hp).mul_continuousOn original_sigma_continuous
  have hj := hp.mul_continuousOn (SigmaInnerProfile.weight_continuous (by norm_num) (by norm_num))
  unfold CorrectionD0Joint.intrinsicSigmaUnpaid SigmaInnerProfile.actualLower
  rw [aProfile_eq,SigmaInnerProfile.numerator_integral,← sub_div,← intervalIntegral.integral_sub hi hj]
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  ring

end CorrectionSigmaVariable
