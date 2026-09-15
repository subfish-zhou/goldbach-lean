import OriginalSigmaFiniteConsumers

namespace OriginalSigmaStrength
open Real Set MeasureTheory NodeExtension
open Wu2008DoubleSieve SharpLogRecurrence
open scoped Interval BigOperators
noncomputable section

/-- The original-domain chord of the exact weighted denominator moment. -/
def momentChord (t : ℝ) : ℝ := (19*t+17)/3

/-- A reciprocal lower envelope certified by a complete square, not a series. -/
theorem reciprocal_square_lower {d q : ℝ} (hd : 0<d) (hq : 0<q) :
    2/q-d/q^2 ≤ 1/d := by
  have he : 1/d-(2/q-d/q^2)=(d-q)^2/(d*q^2) := by
    field_simp
    ring
  have hn : 0 ≤ (d-q)^2/(d*q^2) := by positivity
  linarith only [he,hn]

/-- Keep the coupled denominator in the genuine triangular sigma integrand. -/
theorem coupled_log_kernel {t v : ℝ} (ht : 1≤t) (hv : 3≤v) (hvt : v≤t+2) :
    2*(t+2-v)/(v*(t+v)) ≤ log ((t+1)/(v-1))/v := by
  have hv0 : 0<v := by linarith
  have hv1 : 0<v-1 := by linarith
  have htv : 0<t+v := by linarith
  have hx : 1≤(t+1)/(v-1) := (one_le_div hv1).mpr (by linarith)
  have hy : 0≤(((t+1)/(v-1)-1)/((t+1)/(v-1)+1)) := by positivity
  have hl := log_lower hx
  have hc : 0≤2*(((t+1)/(v-1)-1)/((t+1)/(v-1)+1))^3/3 := by positivity
  have hratio : ((t+1)/(v-1)-1)/((t+1)/(v-1)+1)=(t+2-v)/(t+v) := by
    field_simp
    ring
  unfold lowerLog at hl
  rw [hratio] at hl hc
  have hlin : 2*((t+2-v)/(t+v))≤log ((t+1)/(v-1)) := by linarith only [hl,hc]
  convert div_le_div_of_nonneg_right hlin hv0.le using 1 <;> first | rfl | skip
  field_simp

/-- The exact polynomial envelope on the unchanged original triangular domain. -/
def momentDensity (t v : ℝ) : ℝ :=
  2*(t+2-v)*(2/momentChord t-v*(t+v)/(momentChord t)^2)

def momentPrimitive (t v : ℝ) : ℝ :=
  4/momentChord t*((t+2)*v-v^2/2)-
    2/(momentChord t)^2*(t*(t+2)*v^2/2+2*v^3/3-v^4/4)

theorem momentDensity_le {t v : ℝ} (ht : 1≤t) (hv : 3≤v) (hvt : v≤t+2) :
    momentDensity t v ≤ log ((t+1)/(v-1))/v := by
  have hq : 0 < momentChord t := by unfold momentChord; linarith
  have hd : 0<v*(t+v) := mul_pos (by linarith) (by linarith)
  have hm := mul_le_mul_of_nonneg_left (reciprocal_square_lower hd hq)
    (show 0≤2*(t+2-v) by linarith)
  apply le_trans (b := 2*(t+2-v)/(v*(t+v))) _ (coupled_log_kernel ht hv hvt)
  convert hm using 1 <;> first | rfl | ring

theorem momentPrimitive_deriv (t v : ℝ) :
    HasDerivAt (momentPrimitive t) (momentDensity t v) v := by
  have h := (((hasDerivAt_id v).const_mul (t+2)).sub
    (((hasDerivAt_id v).pow 2).div_const 2)).const_mul (4/momentChord t)
  have h' := (((((hasDerivAt_id v).pow 2).const_mul (t*(t+2))).div_const 2).add
    ((((hasDerivAt_id v).pow 3).const_mul 2).div_const 3)).sub
    (((hasDerivAt_id v).pow 4).div_const 4)
  convert h.sub (h'.const_mul (2/(momentChord t)^2)) using 1 <;> first | rfl | skip
  dsimp only [id]
  unfold momentDensity
  ring

def strengthFloor (t : ℝ) : ℝ := 3*(t-1)^2/(19*t+17)

theorem moment_integral_exact {t : ℝ} (ht : 1≤t) :
    (∫ v in (3:ℝ)..(t+2), momentDensity t v) =
      strengthFloor t+9*(t-1)^3*(3-t)/(2*(19*t+17)^2) := by
  have hi : IntervalIntegrable (momentDensity t) volume 3 (t+2) := by
    apply Continuous.intervalIntegrable
    unfold momentDensity
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun v _ => momentPrimitive_deriv t v) hi]
  have hq : 19*t+17≠0 := by linarith
  unfold momentPrimitive momentChord strengthFloor
  field_simp
  ring

/-- Unconditional stronger payment of the original sigma, on its full original domain. -/
theorem strengthFloor_le_sigma {t : ℝ} (ht : 1≤t) (ht3 : t≤3) :
    strengthFloor t ≤ sigma 3 (t+2) (t+1) := by
  have hi : IntervalIntegrable (momentDensity t) volume 3 (t+2) := by
    apply Continuous.intervalIntegrable
    unfold momentDensity
    fun_prop
  have hm := intervalIntegral.integral_mono_on (by linarith : (3:ℝ)≤t+2) hi
    (sigma_integrable (by norm_num) (by linarith) (by linarith : 0<t+1))
    (fun v hv => momentDensity_le ht hv.1 hv.2)
  rw [moment_integral_exact ht] at hm
  have hr : 0≤9*(t-1)^3*(3-t)/(2*(19*t+17)^2) := by positivity
  exact le_trans (by linarith only [hr]) hm

/-- The original normalization is paid using the stronger actual endpoint kernel. -/
theorem D0_strength : (6:ℝ)/37≤D0 := by
  have h := strengthFloor_le_sigma (t := 3) (by norm_num) (by norm_num)
  norm_num [strengthFloor,D0] at h ⊢
  exact h

end
end OriginalSigmaStrength
