import FirstFeedbackTerminalLower
import CoupledEndpointLog

namespace OriginalProfileSigmaPayment
open Real Set MeasureTheory NodeExtension
open scoped Interval BigOperators
noncomputable section

/-- A full-domain lower kernel; neither the profile nor its normalization is changed. -/
def sigmaFloor (t : ℝ) : ℝ := (t-1)^2/(2*(t+1)*(t+2))

theorem sigma_floor_le {t : ℝ} (ht : 1 ≤ t) :
    sigmaFloor t ≤ sigma 3 (t+2) (t+1) := by
  have ht1 : 0<t+1 := by linarith
  have ht2 : 0<t+2 := by linarith
  have hi : IntervalIntegrable (fun v : ℝ => (t+2-v)/((t+1)*(t+2))) volume 3 (t+2) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have he : (∫ v in (3:ℝ)..(t+2), (t+2-v)/((t+1)*(t+2))) = sigmaFloor t := by
    have hd (v : ℝ) : HasDerivAt
        (fun x : ℝ => ((t+2)*x-x^2/2)/((t+1)*(t+2)))
        ((t+2-v)/((t+1)*(t+2))) v := by
      convert (((hasDerivAt_id v).const_mul (t+2)).sub
        (((hasDerivAt_id v).pow 2).div_const 2)).div_const ((t+1)*(t+2)) using 1 <;> first | rfl | skip
      dsimp only [id]
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hd v) hi]
    unfold sigmaFloor
    field_simp
    ring
  rw [← he]
  apply intervalIntegral.integral_mono_on (by linarith) hi
    (sigma_integrable (by norm_num) (by linarith) ht1)
  intro v hv
  have hv0 : 0<v := by linarith [hv.1]
  have hv1 : 0<v-1 := by linarith [hv.1]
  have hn : 0<t+1 := ht1
  have hl := one_sub_inv_le_log_of_pos (div_pos ht1 hv1)
  have hlog : (t+2-v)/(t+1) ≤ log ((t+1)/(v-1)) := by
    convert hl using 1
    field_simp
    ring
  have hdiv := div_le_div_of_nonneg_right hlog hv0.le
  have hden : (t+2-v)/((t+1)*(t+2)) ≤ ((t+2-v)/(t+1))/v := by
    rw [div_div]
    apply div_le_div_of_nonneg_left
    · linarith [hv.2]
    · positivity
    · exact mul_le_mul_of_nonneg_left hv.2 ht1.le
  exact hden.trans hdiv

theorem D0_floor : (1:ℝ)/10 ≤ D0 := by
  have h := sigma_floor_le (t := 3) (by norm_num)
  norm_num [sigmaFloor, D0] at h ⊢
  exact h

/-- Rational weight after both original triangular variables have been paid. -/
def sigmaWeight (t : ℝ) : ℝ := (t-1)^2/(2*t*(t+1)*(t+2))

def sigmaPrimitive (t : ℝ) : ℝ := log t/4-2*log (t+1)+9*log (t+2)/4

theorem sigmaPrimitive_deriv {t : ℝ} (ht : 0<t) :
    HasDerivAt sigmaPrimitive (sigmaWeight t) t := by
  have h1 : t+1≠0 := by linarith
  have h2 : t+2≠0 := by linarith
  have h := (((hasDerivAt_log ht.ne').div_const 4).sub
    ((((hasDerivAt_id t).add_const 1).log h1).const_mul 2)).add
    (((((hasDerivAt_id t).add_const 2).log h2).const_mul 9).div_const 4)
  convert h using 1 <;> first | rfl | skip
  dsimp only [id]
  unfold sigmaWeight
  field_simp
  ring

theorem sigmaWeight_continuous {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    ContinuousOn sigmaWeight (uIcc a b) := by
  rw [uIcc_of_le hab]
  intro t ht
  have ht0 : 0<t := ha.trans_le ht.1
  apply ContinuousAt.continuousWithinAt
  unfold sigmaWeight
  fun_prop (disch := positivity)

theorem sigmaWeight_integral {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    (∫ t in a..b, sigmaWeight t)=sigmaPrimitive b-sigmaPrimitive a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t ht
    rw [uIcc_of_le hab] at ht
    exact sigmaPrimitive_deriv (ha.trans_le ht.1)
  · exact (sigmaWeight_continuous ha hab).intervalIntegrable

end
end OriginalProfileSigmaPayment
