import OriginalSigmaStrengthPayment

namespace OriginalSigmaStrength
open Real Set MeasureTheory NodeExtension
open Wu2008DoubleSieve SharpLogRecurrence JointLogTotalComparison
open scoped Interval BigOperators
noncomputable section

/-- Exact integral of the retained coupled denominator, before any endpoint log payment. -/
def retainedKernel (t : ℝ) : ℝ :=
  2*(t+2)/t*log ((t+2)/3)-4*(t+1)/t*log ((2*t+2)/(t+3))

def retainedPrimitive (t v : ℝ) : ℝ :=
  2*(t+2)/t*log v-4*(t+1)/t*log (t+v)

theorem retainedPrimitive_deriv {t v : ℝ} (ht : 0<t) (hv : 0<v) :
    HasDerivAt (retainedPrimitive t) (2*(t+2-v)/(v*(t+v))) v := by
  have htv : t+v≠0 := by positivity
  have h := ((hasDerivAt_log hv.ne').const_mul (2*(t+2)/t)).sub
    ((((hasDerivAt_id v).const_add t).log htv).const_mul (4*(t+1)/t))
  convert h using 1 <;> first | rfl | skip
  dsimp only [id]
  field_simp
  ring

theorem retained_integral {t : ℝ} (ht : 1≤t) :
    (∫ v in (3:ℝ)..(t+2), 2*(t+2-v)/(v*(t+v)))=retainedKernel t := by
  have ht0 : 0<t := by linarith
  have hi : IntervalIntegrable (fun v : ℝ => 2*(t+2-v)/(v*(t+v))) volume 3 (t+2) := by
    apply ContinuousOn.intervalIntegrable_of_Icc (h := by linarith)
    intro v hv
    have hv0 : 0<v := by linarith [hv.1]
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := positivity)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v hv => by
    rw [uIcc_of_le (by linarith : (3:ℝ)≤t+2)] at hv
    exact retainedPrimitive_deriv ht0 (by linarith [hv.1])) hi]
  unfold retainedPrimitive retainedKernel
  rw [log_div (by linarith : t+2≠0) (by norm_num : (3:ℝ)≠0),
    log_div (by linarith : 2*t+2≠0) (by linarith : t+3≠0)]
  have he : t+(t+2)=2*t+2 := by ring
  rw [he]
  ring

theorem retainedKernel_le_sigma {t : ℝ} (ht : 1≤t) :
    retainedKernel t ≤ sigma 3 (t+2) (t+1) := by
  rw [← retained_integral ht]
  have hi : IntervalIntegrable (fun v : ℝ => 2*(t+2-v)/(v*(t+v))) volume 3 (t+2) := by
    apply ContinuousOn.intervalIntegrable_of_Icc (h := by linarith)
    intro v hv
    have hv0 : 0<v := by linarith [hv.1]
    have ht0 : 0<t := by linarith
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := positivity)
  apply intervalIntegral.integral_mono_on (by linarith) hi
    (sigma_integrable (by norm_num) (by linarith) (by linarith : 0<t+1))
  intro v hv
  exact coupled_log_kernel ht hv.1 hv.2

/-- Only the inherited fixed L and V are applied to the two exact logarithmic arguments. -/
def retainedPaid (t : ℝ) : ℝ :=
  2*(t+2)/t*lowerLog ((t+2)/3)-4*(t+1)/t*V ((2*t+2)/(t+3))

theorem retainedPaid_le_sigma {t : ℝ} (ht : 1≤t) :
    retainedPaid t ≤ sigma 3 (t+2) (t+1) := by
  have ht0 : 0<t := by linarith
  have h0 := mul_le_mul_of_nonneg_left
    (log_lower (show 1≤(t+2)/3 by linarith)) (show 0≤2*(t+2)/t by positivity)
  have h1 := mul_le_mul_of_nonneg_left
    (log_le_V ((one_le_div (by linarith : 0<t+3)).mpr (by linarith : t+3≤2*t+2)))
    (show 0≤4*(t+1)/t by positivity)
  apply le_trans (b := retainedKernel t) _ (retainedKernel_le_sigma ht)
  unfold retainedPaid retainedKernel
  linarith only [h0,h1]

/-- The actual endpoint D0, paid without flattening the coupled denominator. -/
def retainedD0 : ℝ := retainedPaid 3

theorem retainedD0_le : retainedD0 ≤ D0 := by
  have h := retainedPaid_le_sigma (t := 3) (by norm_num)
  norm_num only [show (3:ℝ)+2=5 by norm_num, show (3:ℝ)+1=4 by norm_num] at h
  exact h

theorem retainedD0_lt_one : retainedD0 < 1 := retainedD0_le.trans_lt D0_lt_one

def retainedWeight (t : ℝ) : ℝ := retainedPaid t/t

end
end OriginalSigmaStrength
