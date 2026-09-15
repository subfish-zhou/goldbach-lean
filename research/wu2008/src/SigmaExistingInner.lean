import CoupledCorrectedE

namespace SigmaExistingLogError
open Real Set MeasureTheory NodeExtension OriginalSigmaStrength OriginalSigmaCubicRestoration
open Wu2008DoubleSieve SharpLogRecurrence JointLogTotalComparison
open scoped Interval
noncomputable section

/-- Reuses the inherited envelopes; this is not a new Taylor order. -/
def enhanced (x : ℝ) : ℝ := lowerLog x+(4/7)*(upperLog x-lowerLog x)

theorem enhanced_le {x : ℝ} (hx : 1≤x) (hx2 : x≤2) : enhanced x≤log x := by
  have h := OriginalFirstErrorRecovery.terminal_lower_error hx hx2
  unfold enhanced
  linarith only [h]

theorem original_argument {t v : ℝ} (_ht : 1≤t) (ht3 : t≤3)
    (hv : 3≤v) (hvt : v≤t+2) : 1≤(t+1)/(v-1) ∧ (t+1)/(v-1)≤2 := by
  constructor
  · exact (one_le_div (by linarith : 0<v-1)).mpr (by linarith)
  · exact (div_le_iff₀ (by linarith : 0<v-1)).mpr (by linarith)

def upperDensity (t v : ℝ) : ℝ := upperLog ((t+1)/(v-1))/v
def ua (t : ℝ) : ℝ := -(t+2)*(t^2-8*t-8)/(6*t*(t+1))
def ub (t : ℝ) : ℝ := (t+1)/6
def uc (t : ℝ) : ℝ := -8*(t+1)/(3*t)
def upperPrimitive (t v : ℝ) : ℝ :=
  ua t*log v+ub t*log (v-1)+uc t*log (v+t)-v/(6*(t+1))

theorem upperDensity_laurent {t v : ℝ} (ht : 0<t) (hv : 1<v) :
    upperDensity t v=ua t/v+ub t/(v-1)+uc t/(v+t)-1/(6*(t+1)) := by
  have hv0 : v≠0 := by linarith
  have hv1 : v-1≠0 := by linarith
  have hvt : v+t≠0 := by positivity
  have htv : t+v≠0 := by positivity
  have ht1 : t+1≠0 := by positivity
  unfold upperDensity upperLog ua ub uc
  field_simp
  ring_nf
  field_simp [htv]
  ring

theorem upperPrimitive_deriv {t v : ℝ} (ht : 0<t) (hv : 1<v) :
    HasDerivAt (upperPrimitive t) (upperDensity t v) v := by
  rw [upperDensity_laurent ht hv]
  have h0 := (hasDerivAt_log (by linarith : v≠0)).const_mul (ua t)
  have h1 := (((hasDerivAt_id v).sub_const 1).log (by linarith : v-1≠0)).const_mul (ub t)
  have h2 := (((hasDerivAt_id v).add_const t).log (by positivity : v+t≠0)).const_mul (uc t)
  convert ((h0.add h1).add h2).sub ((hasDerivAt_id v).div_const (6*(t+1))) using 1 <;>
    first | rfl | skip
  dsimp only [id]
  ring

theorem upperDensity_integrable {t : ℝ} (ht : 1≤t) :
    IntervalIntegrable (upperDensity t) volume 3 (t+2) := by
  apply ContinuousOn.intervalIntegrable_of_Icc (h := by linarith)
  intro v hv
  have hv0 : 0<v := by linarith [hv.1]
  have hv1 : 0<v-1 := by linarith [hv.1]
  have ht0 : 0<t := by linarith
  unfold upperDensity upperLog
  apply ContinuousAt.continuousWithinAt
  fun_prop (disch := positivity)

def upperKernel (t : ℝ) : ℝ :=
  ua t*log ((t+2)/3)+ub t*log ((t+1)/2)+uc t*log ((2*t+2)/(t+3))-
    (t-1)/(6*(t+1))

theorem upperDensity_integral {t : ℝ} (ht : 1≤t) :
    (∫ v in (3:ℝ)..(t+2), upperDensity t v)=upperKernel t := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v hv => by
    rw [uIcc_of_le (by linarith : (3:ℝ)≤t+2)] at hv
    exact upperPrimitive_deriv (by linarith) (by linarith [hv.1])) (upperDensity_integrable ht)]
  unfold upperPrimitive upperKernel
  rw [log_div (by linarith : t+2≠0) (by norm_num : (3:ℝ)≠0),
    log_div (by linarith : t+1≠0) (by norm_num : (2:ℝ)≠0),
    log_div (by linarith : 2*t+2≠0) (by linarith : t+3≠0)]
  have h1 : t+2-1=t+1 := by ring
  have h2 : t+2+t=2*t+2 := by ring
  have h3 : (3:ℝ)+t=t+3 := by ring
  norm_num only [h1,h2,h3,show (3:ℝ)-1=2 by norm_num]
  ring

def innerKernel (t : ℝ) : ℝ :=
  (3/7)*(retainedKernel t+cubicKernel t)+(4/7)*upperKernel t

/-- Same original triangular sigma, paying L + (4/7)(U-L) inside its integral. -/
theorem innerKernel_le_sigma {t : ℝ} (ht : 1≤t) (ht3 : t≤3) :
    innerKernel t ≤ sigma 3 (t+2) (t+1) := by
  have hi : IntervalIntegrable (fun v : ℝ => 2*(t+2-v)/(v*(t+v))) volume 3 (t+2) := by
    apply ContinuousOn.intervalIntegrable_of_Icc (h := by linarith)
    intro v hv
    have hv0 : 0<v := by linarith [hv.1]
    have ht0 : 0<t := by linarith
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := positivity)
  unfold innerKernel
  rw [← retained_integral ht,← cubic_integral ht,← upperDensity_integral ht,
    ← intervalIntegral.integral_add hi (cubic_integrable ht),
    ← intervalIntegral.integral_const_mul,← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add ((hi.add (cubic_integrable ht)).const_mul (3/7))
      ((upperDensity_integrable ht).const_mul (4/7))]
  apply intervalIntegral.integral_mono_on (by linarith)
    (((hi.add (cubic_integrable ht)).const_mul (3/7)).add ((upperDensity_integrable ht).const_mul (4/7)))
    (sigma_integrable (by norm_num) (by linarith) (by linarith : 0<t+1))
  intro v hv
  have hv0 : 0<v := by linarith [hv.1]
  have hv1 : 0<v-1 := by linarith [hv.1]
  have hx := original_argument ht ht3 hv.1 hv.2
  have h := div_le_div_of_nonneg_right (enhanced_le hx.1 hx.2) hv0.le
  have hr : ((t+1)/(v-1)-1)/((t+1)/(v-1)+1)=(t+2-v)/(t+v) := by
    field_simp
    ring
  convert h using 1 <;> first | rfl | skip
  unfold enhanced lowerLog upperDensity cubicDensity
  rw [hr]
  field_simp
  ring

end
end SigmaExistingLogError
