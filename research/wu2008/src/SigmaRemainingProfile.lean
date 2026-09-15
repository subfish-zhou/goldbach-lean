import SigmaRemainingOuter
namespace SigmaRemaining
open Real Set MeasureTheory NodeExtension FirstFeedbackIntegrals OriginalProfileSigmaPayment
open OriginalSigmaStrength Wu04WholeCollection SigmaExistingLogError
open scoped Interval BigOperators
noncomputable section

/-- Only the three original collected logs at the original terminal t=3. -/
def d0Paid : ℝ :=
  aCoeff 3*RemainingHf.splitLower (5/3)+bCoeff 3*RemainingHf.splitLower 2+
  cCoeff 3*RemainingHf.splitUpper (4/3)+rationalPart 3

theorem d0Paid_le : d0Paid ≤ D0 := by
  have h1 := mul_le_mul_of_nonneg_left
    (RemainingHf.splitLower_le (by norm_num : (1:ℝ)≤5/3))
    (aCoeff_nonneg (by norm_num : (1:ℝ)≤3) le_rfl)
  have h2 := mul_le_mul_of_nonneg_left
    (RemainingHf.splitLower_le (by norm_num : (1:ℝ)≤2))
    (bCoeff_nonneg (by norm_num : (1:ℝ)≤3))
  have h3 := mul_le_mul_of_nonpos_left
    (RemainingHf.le_splitUpper (by norm_num : (1:ℝ)≤4/3))
    (cCoeff_nonpos (by norm_num : (1:ℝ)≤3))
  have hs := innerKernel_le_sigma (by norm_num : (1:ℝ)≤3) le_rfl
  rw [innerKernel_collected] at hs
  norm_num only [show (3:ℝ)+2=5 by norm_num,show (3:ℝ)+1=4 by norm_num,
    show (4:ℝ)/2=2 by norm_num,show ((2:ℝ)*3+2)/(3+3)=4/3 by norm_num] at hs
  unfold d0Paid
  change _ ≤ sigma 3 5 4
  linarith only [h1,h2,h3,hs]

theorem d0Paid_lt_one : d0Paid<1 := d0Paid_le.trans_lt D0_lt_one

def actualLower (z : Fin 9 → ℝ) : ℝ := SigmaRemaining.numerator z/(1-D0)
def finiteLower (z : Fin 9 → ℝ) : ℝ := SigmaRemaining.numerator z/(1-d0Paid)

theorem actualLower_le_profile {z : Fin 9 → ℝ} (hz : ∀ k,0≤z k) :
    SigmaRemaining.actualLower z ≤ aProfile (nineProfile z) := by
  rw [SigmaRemaining.actualLower,aProfile_eq]
  apply div_le_div_of_nonneg_right _ (sub_pos.mpr D0_lt_one).le
  apply (SigmaRemaining.numerator_le hz).trans
  rw [numerator_integral]
  have hp := nineProfile_integrable z
  apply intervalIntegral.integral_mono_on (by norm_num)
    (hp.mul_continuousOn (weight_continuous (by norm_num) (by norm_num)))
    ((profile_div_integrable hp).mul_continuousOn original_sigma_continuous)
  intro t ht
  have ht0 : 0<t := by linarith [ht.1]
  have h := mul_le_mul_of_nonneg_left (endpointPaid_le_sigma ht.1 ht.2)
    (div_nonneg (nineProfile_nonneg hz t) ht0.le)
  convert h using 1 <;> first | rfl | skip
  unfold weight
  ring

theorem finiteLower_le_profile {z : Fin 9 → ℝ} (hz : ∀ k,0≤z k)
    (hn : 0≤SigmaRemaining.numerator z) :
    SigmaRemaining.finiteLower z ≤ aProfile (nineProfile z) := by
  apply le_trans (b := SigmaRemaining.actualLower z) _ (SigmaRemaining.actualLower_le_profile hz)
  exact div_le_div_of_nonneg_left hn (sub_pos.mpr D0_lt_one) (by linarith only [d0Paid_le])

end
end SigmaRemaining
