import CorrectionSigmaVariable

noncomputable section
namespace CorrectionSigmaVariable
open Real Set MeasureTheory Wu2008DoubleSieve SharpLogRecurrence
open SigmaInnerEndpointRecovery OriginalSigmaStrength OriginalSigmaCubicRestoration
open F1FullRecoveryPayment NodeExtension FirstFeedbackIntegrals SigmaExistingLogError
open scoped Interval

theorem oldDensity_eq {t v : ℝ} (ht : 1 ≤ t) (hv : v ∈ Icc 3 (t+2)) :
    oldDensity t v=(1-beta t)*(2*(t+2-v)/(v*(t+v))+cubicDensity t v)+
      beta t*upperDensity t v := by
  have hv0 : 0<v := by linarith [hv.1]
  have hv1 : 0<v-1 := by linarith [hv.1]
  have ht0 : 0<t := by linarith
  have hr : ((t+1)/(v-1)-1)/((t+1)/(v-1)+1)=(t+2-v)/(t+v) := by
    field_simp
    ring
  unfold oldDensity lowerLog upperDensity cubicDensity
  rw [hr]
  field_simp

theorem oldDensity_integrable {t : ℝ} (ht : 1 ≤ t) :
    IntervalIntegrable (oldDensity t) volume 3 (t+2) := by
  apply ContinuousOn.intervalIntegrable_of_Icc (h := by linarith)
  intro v hv
  have hv0 : 0<v := by linarith [hv.1]
  have hv1 : 0<v-1 := by linarith [hv.1]
  have ht0 : 0<t+1 := by linarith
  have hx0 : 0<(t+1)/(v-1) := div_pos ht0 hv1
  apply ContinuousAt.continuousWithinAt
  unfold oldDensity lowerLog upperLog
  fun_prop (disch := positivity)

theorem oldDensity_integral {t : ℝ} (ht : 1 ≤ t) :
    (∫ v in (3:ℝ)..t+2,oldDensity t v)=kernel t := by
  have hi : IntervalIntegrable (fun v : ℝ => 2*(t+2-v)/(v*(t+v))) volume 3 (t+2) := by
    apply ContinuousOn.intervalIntegrable_of_Icc (h := by linarith)
    intro v hv
    have hv0 : 0<v := by linarith [hv.1]
    have ht0 : 0<t := by linarith
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := positivity)
  rw [intervalIntegral.integral_congr (fun v hv => oldDensity_eq ht
    (by simpa only [uIcc_of_le (by linarith : (3:ℝ) ≤ t+2)] using hv))]
  rw [intervalIntegral.integral_add ((hi.add (cubic_integrable ht)).const_mul (1-beta t))
    ((upperDensity_integrable ht).const_mul (beta t)),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add hi (cubic_integrable ht),
    retained_integral ht,cubic_integral ht,upperDensity_integral ht]
  rfl

def variationMass (t : ℝ) : ℝ := ∫ v in (3:ℝ)..t+2,variation t v/v

theorem variation_integrable {t : ℝ} (ht : 1 ≤ t) :
    IntervalIntegrable (fun v => variation t v/v) volume 3 (t+2) := by
  apply ContinuousOn.intervalIntegrable_of_Icc (h := by linarith)
  intro v hv
  have hv0 : 0<v := by linarith [hv.1]
  have hv1 : 0<v-1 := by linarith [hv.1]
  have ht0 : 0<t+1 := by linarith
  have hx0 : 0<(t+1)/(v-1) := div_pos ht0 hv1
  have hq : 0<((t+1)/(v-1))^2+8*((t+1)/(v-1))+1 := by positivity
  apply ContinuousAt.continuousWithinAt
  unfold variation SigmaJEndpoint.coefficient lowerLog upperLog F1LowerResidual.payment F1LowerResidual.denom
  fun_prop (disch := positivity)

theorem variationMass_nonneg {t : ℝ} (ht : 1 ≤ t) : 0 ≤ variationMass t := by
  apply intervalIntegral.integral_nonneg (by linarith)
  intro v hv
  exact div_nonneg (variation_nonneg ht hv) (by linarith [hv.1])

/-- A proved payment of the original inner sigma remainder, on its complete triangle. -/
theorem kernel_add_variation_le_sigma {t : ℝ} (ht : 1 ≤ t) :
    kernel t+variationMass t ≤ sigma 3 (t+2) (t+1) := by
  rw [← oldDensity_integral ht]
  unfold variationMass
  rw [← intervalIntegral.integral_add (oldDensity_integrable ht) (variation_integrable ht)]
  apply intervalIntegral.integral_mono_on (by linarith)
    ((oldDensity_integrable ht).add (variation_integrable ht))
    (sigma_integrable (by norm_num) (by linarith) (by linarith : 0<t+1))
  intro v hv
  exact strengthened_density_le ht hv

end CorrectionSigmaVariable
