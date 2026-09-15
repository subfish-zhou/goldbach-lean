import OriginalSigmaMomentStrength

namespace OriginalSigmaStrength
open Real Set MeasureTheory NodeExtension FirstFeedbackIntegrals OriginalProfileSigmaPayment
open Wu04WholeCollection
open scoped Interval BigOperators
noncomputable section

def strengthWeight (t : ℝ) : ℝ := 3*(t-1)^2/(t*(19*t+17))
def strengthPrimitive (t : ℝ) : ℝ := 3*t/19+3*log t/17-3888*log (19*t+17)/6137

theorem strengthPrimitive_deriv {t : ℝ} (ht : 0<t) :
    HasDerivAt strengthPrimitive (strengthWeight t) t := by
  have hd : 19*t+17≠0 := by linarith
  have h := ((((hasDerivAt_id t).const_mul 3).div_const 19).add
    (((hasDerivAt_log ht.ne').const_mul 3).div_const 17)).sub
    ((((((hasDerivAt_id t).const_mul 19).add_const 17).log hd).const_mul 3888).div_const 6137)
  convert h using 1 <;> first | rfl | skip
  dsimp only [id]
  unfold strengthWeight
  field_simp
  ring

theorem strengthWeight_continuous {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    ContinuousOn strengthWeight (uIcc a b) := by
  rw [uIcc_of_le hab]
  intro t ht
  have ht0 : 0<t := ha.trans_le ht.1
  apply ContinuousAt.continuousWithinAt
  unfold strengthWeight
  fun_prop (disch := positivity)

theorem strengthWeight_integral {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    (∫ t in a..b, strengthWeight t)=strengthPrimitive b-strengthPrimitive a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t ht
    rw [uIcc_of_le hab] at ht
    exact strengthPrimitive_deriv (ha.trans_le ht.1)
  · exact (strengthWeight_continuous ha hab).intervalIntegrable

/-- Every original cell is retained, without altering the profile. -/
def strengthNumerator (z : Fin 9 → ℝ) : ℝ :=
  ∑ k : Fin 9, z k*(strengthPrimitive (upperNode k)-strengthPrimitive (upperLeft k))

/-- Keep the actual normalization in the analytic payment. -/
def strengthLower (z : Fin 9 → ℝ) : ℝ := strengthNumerator z/(1-D0)

/-- An independently proved endpoint bound pays the same normalization. -/
def strengthFinite (z : Fin 9 → ℝ) : ℝ := strengthNumerator z/(1-(6:ℝ)/37)

theorem strengthNumerator_integral (z : Fin 9 → ℝ) :
    strengthNumerator z = ∫ t in (1:ℝ)..3, nineProfile z t*strengthWeight t := by
  rw [profile_integral_cells z le_rfl (by norm_num [upperNode])
    (strengthWeight_continuous (by norm_num) (by norm_num))]
  apply Finset.sum_congr rfl
  intro k _
  have hb := cell_bounds (a := 1) le_rfl (by norm_num [upperNode]) k
  have he : cellLeft 1 k=upperLeft k := by
    unfold cellLeft upperLeft
    split_ifs <;> rfl
  rw [strengthWeight_integral (by linarith [hb.1] : 0<cellLeft 1 k) hb.2.1,he]

theorem strengthNumerator_nonneg {z : Fin 9 → ℝ} (hz : ∀ k,0≤z k) :
    0 ≤ strengthNumerator z := by
  rw [strengthNumerator_integral]
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro t ht
  apply mul_nonneg (nineProfile_nonneg hz t)
  unfold strengthWeight
  have ht0 : 0<t := by linarith [ht.1]
  positivity

/-- The recovered coupled kernel is consumed by the actual common feedback. -/
theorem strengthLower_le_profile {z : Fin 9 → ℝ} (hz : ∀ k,0≤z k) :
    strengthLower z ≤ aProfile (nineProfile z) := by
  rw [strengthLower,aProfile_eq,strengthNumerator_integral]
  apply div_le_div_of_nonneg_right _ (sub_pos.mpr D0_lt_one).le
  have hp := nineProfile_integrable z
  have hlow := hp.mul_continuousOn (strengthWeight_continuous (by norm_num) (by norm_num))
  have hhigh := (profile_div_integrable hp).mul_continuousOn original_sigma_continuous
  apply intervalIntegral.integral_mono_on (by norm_num) hlow hhigh
  intro t ht
  have ht0 : 0<t := by linarith [ht.1]
  have h := mul_le_mul_of_nonneg_left (strengthFloor_le_sigma ht.1 ht.2)
    (div_nonneg (nineProfile_nonneg hz t) ht0.le)
  convert h using 1 <;> first | rfl | skip
  unfold strengthWeight strengthFloor
  field_simp

theorem strengthFinite_le_profile {z : Fin 9 → ℝ} (hz : ∀ k,0≤z k) :
    strengthFinite z ≤ aProfile (nineProfile z) := by
  apply le_trans (b := strengthLower z) _ (strengthLower_le_profile hz)
  apply div_le_div_of_nonneg_left (strengthNumerator_nonneg hz) (sub_pos.mpr D0_lt_one)
  linarith only [D0_strength]

/-- Combine signed endpoint logarithms before paying the inherited log envelopes. -/
def strengthCellPaid (a b : ℝ) : ℝ :=
  3*(b-a)/19+3*low (b/a)/17-3888*up ((19*b+17)/(19*a+17))/6137

theorem strengthCellPaid_le {a b : ℝ} (ha : 0<a) (hb : 0<b) :
    strengthCellPaid a b ≤ strengthPrimitive b-strengthPrimitive a := by
  have h0 := (bounds (div_pos hb ha)).1
  have h1 := (bounds (div_pos (by linarith : 0<19*b+17) (by linarith : 0<19*a+17))).2
  rw [log_div hb.ne' ha.ne'] at h0
  rw [log_div (by linarith : 19*b+17≠0) (by linarith : 19*a+17≠0)] at h1
  unfold strengthCellPaid strengthPrimitive
  linarith only [h0,h1]

/-- New rational payment, with the genuine stronger endpoint denominator theorem. -/
def strengthRational (z : Fin 9 → ℝ) : ℝ :=
  (∑ k : Fin 9, z k*strengthCellPaid (upperLeft k) (upperNode k))/(1-(6:ℝ)/37)

theorem strengthRational_le_profile {z : Fin 9 → ℝ} (hz : ∀ k,0≤z k) :
    strengthRational z ≤ aProfile (nineProfile z) := by
  apply le_trans (b := strengthFinite z) _ (strengthFinite_le_profile hz)
  unfold strengthRational strengthFinite strengthNumerator
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply Finset.sum_le_sum
  intro k _
  have hc := cell_bounds (a := 1) le_rfl (by norm_num [upperNode]) k
  have he : cellLeft 1 k=upperLeft k := by
    unfold cellLeft upperLeft
    split_ifs <;> rfl
  rw [he] at hc
  exact mul_le_mul_of_nonneg_left
    (strengthCellPaid_le (by linarith [hc.1]) (by linarith [hc.1,hc.2.1])) (hz k)

theorem original_strength_payment :
    strengthRational NineFeedbackStrength.originalH ≤
      aProfile (nineProfile NineFeedbackStrength.originalH) :=
  strengthRational_le_profile CoupledIntegralRecovery.originalH_nonneg

end
end OriginalSigmaStrength
