import RetainedOriginalProfilePayment

namespace OriginalSigmaCubicRestoration
open Real Set MeasureTheory NodeExtension OriginalSigmaStrength
open Wu2008DoubleSieve SharpLogRecurrence JointLogTotalComparison
open scoped Interval
noncomputable section

/-- The cubic summand already present in the inherited L. -/
def cubicDensity (t v : ℝ) : ℝ := 2*(t+2-v)^3/(3*v*(t+v)^3)
def ca (t : ℝ) : ℝ := (t+2)^3/t^3
def cb (t : ℝ) : ℝ := -1-ca t
def cc (t : ℝ) : ℝ := 12*(t+1)^2/t-8*(t+1)^3/t^2
def cd (t : ℝ) : ℝ := -8*(t+1)^3/t

def cubicPrimitive (t v : ℝ) : ℝ :=
  (polePrimitive 0 (ca t) 0 0 v+polePrimitive t (cb t) (cc t) (cd t) v)*2/3

theorem cubicPrimitive_deriv {t v : ℝ} (ht : 0<t) (hv : 0<v) :
    HasDerivAt (cubicPrimitive t) (cubicDensity t v) v := by
  have h := ((polePrimitive_deriv 0 (ca t) 0 0 (by linarith : v+0≠0)).add
    (polePrimitive_deriv t (cb t) (cc t) (cd t) (by positivity : v+t≠0))).mul_const 2
  convert h.div_const 3 using 1 <;> first | rfl | skip
  unfold poleDensity cubicDensity cb ca cc cd
  have htne : t≠0 := ht.ne'
  have hvne : v≠0 := hv.ne'
  have hvtn : v+t≠0 := by positivity
  have htvn : t+v≠0 := by positivity
  field_simp
  ring

def cubicKernel (t : ℝ) : ℝ :=
  (ca t*log ((t+2)/3)+cb t*log ((2*t+2)/(t+3))-
    cc t*(1/(2*t+2)-1/(t+3))-cd t/2*(1/(2*t+2)^2-1/(t+3)^2))*2/3

theorem cubic_integrable {t : ℝ} (ht : 1≤t) :
    IntervalIntegrable (cubicDensity t) volume 3 (t+2) := by
  apply ContinuousOn.intervalIntegrable_of_Icc (h := by linarith)
  intro v hv
  have hv0 : 0<v := by linarith [hv.1]
  have ht0 : 0<t := by linarith
  unfold cubicDensity
  apply ContinuousAt.continuousWithinAt
  fun_prop (disch := positivity)

theorem cubic_integral {t : ℝ} (ht : 1≤t) :
    (∫ v in (3:ℝ)..(t+2), cubicDensity t v)=cubicKernel t := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v hv => by
    rw [uIcc_of_le (by linarith : (3:ℝ)≤t+2)] at hv
    exact cubicPrimitive_deriv (by linarith) (by linarith [hv.1])) (cubic_integrable ht)]
  unfold cubicPrimitive cubicKernel polePrimitive
  rw [log_div (by linarith : t+2≠0) (by norm_num : (3:ℝ)≠0),
    log_div (by linarith : 2*t+2≠0) (by linarith : t+3≠0)]
  have he : t+2+t=2*t+2 := by ring
  have he3 : (3:ℝ)+t=t+3 := by ring
  simp only [add_zero,he,he3,div_eq_mul_inv,mul_inv_rev]
  ring

/-- Both summands of the existing L are retained on the original triangular domain. -/
theorem full_lower_density {t v : ℝ} (ht : 1≤t) (hv : 3≤v) (hvt : v≤t+2) :
    2*(t+2-v)/(v*(t+v))+cubicDensity t v ≤ log ((t+1)/(v-1))/v := by
  have hv0 : 0<v := by linarith
  have hv1 : 0<v-1 := by linarith
  have hl := log_lower ((one_le_div hv1).mpr (by linarith : v-1≤t+1))
  have hr : ((t+1)/(v-1)-1)/((t+1)/(v-1)+1)=(t+2-v)/(t+v) := by
    field_simp
    ring
  unfold lowerLog at hl
  rw [hr] at hl
  convert div_le_div_of_nonneg_right hl hv0.le using 1 <;> first | rfl | skip
  unfold cubicDensity
  field_simp

theorem fullKernel_le_sigma {t : ℝ} (ht : 1≤t) :
    retainedKernel t+cubicKernel t ≤ sigma 3 (t+2) (t+1) := by
  have hi : IntervalIntegrable (fun v : ℝ => 2*(t+2-v)/(v*(t+v))) volume 3 (t+2) := by
    apply ContinuousOn.intervalIntegrable_of_Icc (h := by linarith)
    intro v hv
    have hv0 : 0<v := by linarith [hv.1]
    have ht0 : 0<t := by linarith
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := positivity)
  rw [← retained_integral ht,← cubic_integral ht,← intervalIntegral.integral_add hi (cubic_integrable ht)]
  apply intervalIntegral.integral_mono_on (by linarith) (hi.add (cubic_integrable ht))
    (sigma_integrable (by norm_num) (by linarith) (by linarith : 0<t+1))
  intro v hv
  exact full_lower_density ht hv.1 hv.2

/-- Only the already used L/V endpoint rules; no new series or split. -/
def cubicPaid (t : ℝ) : ℝ :=
  (ca t*lowerLog ((t+2)/3)+cb t*V ((2*t+2)/(t+3))-
    cc t*(1/(2*t+2)-1/(t+3))-cd t/2*(1/(2*t+2)^2-1/(t+3)^2))*2/3

theorem fullPaid_le_sigma {t : ℝ} (ht : 1≤t) :
    retainedPaid t+cubicPaid t ≤ sigma 3 (t+2) (t+1) := by
  have ht0 : 0<t := by linarith
  have ha : 0≤ca t := by unfold ca; positivity
  have hb : cb t≤0 := by unfold cb; linarith only [ha]
  have hL := log_lower (show 1≤(t+2)/3 by linarith)
  have hV := log_le_V ((one_le_div (by linarith : 0<t+3)).mpr (by linarith : t+3≤2*t+2))
  have h1 := mul_le_mul_of_nonneg_left hL (show 0≤2*(t+2)/t by positivity)
  have h2 := mul_le_mul_of_nonneg_left hV (show 0≤4*(t+1)/t by positivity)
  have h3 := mul_le_mul_of_nonneg_left hL ha
  have h4 := mul_le_mul_of_nonpos_left hV hb
  apply le_trans (b := retainedKernel t+cubicKernel t) _ (fullKernel_le_sigma ht)
  unfold retainedPaid retainedKernel cubicPaid cubicKernel
  linarith only [h1,h2,h3,h4]

end
end OriginalSigmaCubicRestoration
