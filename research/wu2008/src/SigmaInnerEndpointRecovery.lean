import SigmaRemainingCoupled
namespace SigmaInnerEndpointRecovery
open Real Set MeasureTheory NodeExtension OriginalSigmaStrength OriginalSigmaCubicRestoration
open Wu2008DoubleSieve SharpLogRecurrence SigmaExistingLogError
open scoped Interval
noncomputable section

def beta (t : ℝ) : ℝ := SigmaJEndpoint.coefficient ((t+1)/2)
def kernel (t : ℝ) : ℝ :=
  (1-beta t)*(retainedKernel t+cubicKernel t)+beta t*upperKernel t

theorem beta_ge {t : ℝ} (ht : 1 ≤ t) (ht3 : t ≤ 3) : (4:ℝ)/7 ≤ beta t := by
  have h := SigmaJEndpoint.coefficient_antitone
    (by linarith : (1:ℝ) ≤ (t+1)/2) (by linarith : (t+1)/2 ≤ 2)
  norm_num [SigmaJEndpoint.coefficient] at h
  exact h

theorem kernel_le_sigma {t : ℝ} (ht : 1 ≤ t) : kernel t ≤ sigma 3 (t+2) (t+1) := by
  have hi : IntervalIntegrable (fun v : ℝ => 2*(t+2-v)/(v*(t+v))) volume 3 (t+2) := by
    apply ContinuousOn.intervalIntegrable_of_Icc (h := by linarith)
    intro v hv
    have hv0 : 0<v := by linarith [hv.1]
    have ht0 : 0<t := by linarith
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := positivity)
  unfold kernel
  rw [← retained_integral ht,← cubic_integral ht,← upperDensity_integral ht,
    ← intervalIntegral.integral_add hi (cubic_integrable ht),
    ← intervalIntegral.integral_const_mul,← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add ((hi.add (cubic_integrable ht)).const_mul (1-beta t))
      ((upperDensity_integrable ht).const_mul (beta t))]
  apply intervalIntegral.integral_mono_on (by linarith)
    (((hi.add (cubic_integrable ht)).const_mul (1-beta t)).add
      ((upperDensity_integrable ht).const_mul (beta t)))
    (sigma_integrable (by norm_num) (by linarith) (by linarith : 0<t+1))
  intro v hv
  have hv0 : 0<v := by linarith [hv.1]
  have hv1 : 0<v-1 := by linarith [hv.1]
  have hx : 1 ≤ (t+1)/(v-1) := (one_le_div hv1).mpr (by linarith [hv.2])
  have hxB : (t+1)/(v-1) ≤ (t+1)/2 := by
    apply (div_le_div_iff₀ hv1 (by norm_num : (0:ℝ)<2)).mpr
    nlinarith [hv.1]
  have h := SigmaJEndpoint.endpoint_error hx hxB
  have hl : (1-beta t)*lowerLog ((t+1)/(v-1))+beta t*upperLog ((t+1)/(v-1)) ≤
      log ((t+1)/(v-1)) := by
    change beta t*(_-_) ≤ _-_ at h
    linarith only [h]
  have hd := div_le_div_of_nonneg_right hl hv0.le
  have hr : ((t+1)/(v-1)-1)/((t+1)/(v-1)+1)=(t+2-v)/(t+v) := by
    field_simp
    ring
  convert hd using 1 <;> first | rfl | skip
  unfold lowerLog upperDensity cubicDensity
  rw [hr]
  field_simp

theorem sigma_le_upper {t : ℝ} (ht : 1 ≤ t) : sigma 3 (t+2) (t+1) ≤ upperKernel t := by
  rw [← upperDensity_integral ht]
  apply intervalIntegral.integral_mono_on (by linarith)
    (sigma_integrable (by norm_num) (by linarith) (by linarith : 0<t+1))
    (upperDensity_integrable ht)
  intro v hv
  have hv0 : 0<v := by linarith [hv.1]
  have hx : 1 ≤ (t+1)/(v-1) := (one_le_div (by linarith [hv.1] : 0<v-1)).mpr (by linarith [hv.2])
  exact div_le_div_of_nonneg_right (log_upper hx) hv0.le

theorem old_kernel_le {t : ℝ} (ht : 1 ≤ t) (ht3 : t ≤ 3) : innerKernel t ≤ kernel t := by
  have hl : retainedKernel t+cubicKernel t ≤ upperKernel t := by
    have h := (innerKernel_le_sigma ht ht3).trans (sigma_le_upper ht)
    unfold innerKernel at h
    linarith only [h]
  have h := mul_nonneg (sub_nonneg.mpr (beta_ge ht ht3)) (sub_nonneg.mpr hl)
  unfold innerKernel kernel
  nlinarith only [h]

end
end SigmaInnerEndpointRecovery
