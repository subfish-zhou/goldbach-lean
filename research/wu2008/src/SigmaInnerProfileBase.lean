import SigmaInnerEndpointRecovery

namespace SigmaInnerProfile
open Real Set MeasureTheory NodeExtension OriginalSigmaStrength OriginalSigmaCubicRestoration
open Wu2008DoubleSieve SharpLogRecurrence SigmaExistingLogError
open scoped Interval
noncomputable section

/-- The denominator is forced by the parent's actual endpoint parameter. -/
theorem beta_rational {t : ℝ} (ht : 0 < t) :
    SigmaInnerEndpointRecovery.beta t = 12*(t+1)/(t^2+18*t+21) := by
  have hq : 0 < t^2+18*t+21 := by positivity
  unfold SigmaInnerEndpointRecovery.beta SigmaJEndpoint.coefficient
  field_simp
  ring

def weight (t : ℝ) : ℝ := SigmaInnerEndpointRecovery.kernel t/t

theorem weight_continuousAt {t : ℝ} (ht : 0<t) : ContinuousAt weight t := by
  have hq : 0 < t^2+18*t+21 := by positivity
  have hb : SigmaInnerEndpointRecovery.beta =ᶠ[nhds t]
      fun x : ℝ => 12*(x+1)/(x^2+18*x+21) := by
    filter_upwards [eventually_gt_nhds ht] with x hx
    exact beta_rational hx
  have hbc : ContinuousAt SigmaInnerEndpointRecovery.beta t :=
    ContinuousAt.congr_of_eventuallyEq (by fun_prop (disch := positivity)) hb
  unfold weight SigmaInnerEndpointRecovery.kernel retainedKernel cubicKernel upperKernel
    cb ca cc cd ua ub uc
  fun_prop (disch := positivity)

theorem weight_continuous {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    ContinuousOn weight (uIcc a b) := by
  rw [uIcc_of_le hab]
  intro t ht
  exact (weight_continuousAt (ha.trans_le ht.1)).continuousWithinAt

theorem old_weight_le {t : ℝ} (ht : 1≤t) (ht3 : t≤3) :
    SigmaExistingLogError.weight t ≤ weight t := by
  exact div_le_div_of_nonneg_right
    ((endpointPaid_le_inner ht ht3).trans (SigmaInnerEndpointRecovery.old_kernel_le ht ht3))
    (by linarith)

theorem weight_le_sigma {t : ℝ} (ht : 1≤t) :
    weight t ≤ sigma 3 (t+2) (t+1)/t :=
  div_le_div_of_nonneg_right (SigmaInnerEndpointRecovery.kernel_le_sigma ht) (by linarith)

end
end SigmaInnerProfile
