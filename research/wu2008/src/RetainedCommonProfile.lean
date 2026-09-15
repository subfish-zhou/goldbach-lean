import OriginalSigmaRetainedFTC

namespace RetainedCommonProfile
open Real Set MeasureTheory NodeExtension FirstFeedbackIntegrals OriginalProfileSigmaPayment
open OriginalSigmaStrength Wu04WholeCollection
open scoped Interval BigOperators
noncomputable section

/-- All nine original cells, evaluated by the already certified retained FTC. -/
def numerator (z : Fin 9 → ℝ) : ℝ :=
  ∑ k : Fin 9, z k*(retainedOuterPrimitive (upperNode k)-retainedOuterPrimitive (upperLeft k))

/-- The actual denominator is not replaced in this analytic lower bound. -/
def actualLower (z : Fin 9 → ℝ) : ℝ := numerator z/(1-D0)

/-- Signed finite endpoint payment on the unchanged original nine cells. -/
def paidNumerator (z : Fin 9 → ℝ) : ℝ :=
  ∑ k : Fin 9, z k*retainedCellPaid (upperLeft k) (upperNode k)

def paidActual (z : Fin 9 → ℝ) : ℝ := paidNumerator z/(1-D0)

def finiteLower (z : Fin 9 → ℝ) : ℝ := paidNumerator z/(1-retainedD0)

theorem numerator_integral (z : Fin 9 → ℝ) :
    numerator z = ∫ t in (1:ℝ)..3, nineProfile z t*retainedWeight t := by
  rw [profile_integral_cells z le_rfl (by norm_num [upperNode])
    (retainedWeight_continuous (by norm_num) (by norm_num))]
  apply Finset.sum_congr rfl
  intro k _
  have hb := cell_bounds (a := 1) le_rfl (by norm_num [upperNode]) k
  have he : cellLeft 1 k=upperLeft k := by
    unfold cellLeft upperLeft
    split_ifs <;> rfl
  rw [retainedWeight_integral (by linarith [hb.1] : 0<cellLeft 1 k) hb.2.1,he]

theorem actualLower_le_profile {z : Fin 9 → ℝ} (hz : ∀ k,0≤z k) :
    actualLower z ≤ aProfile (nineProfile z) := by
  rw [actualLower,aProfile_eq,numerator_integral]
  apply div_le_div_of_nonneg_right _ (sub_pos.mpr D0_lt_one).le
  have hp := nineProfile_integrable z
  apply intervalIntegral.integral_mono_on (by norm_num)
    (hp.mul_continuousOn (retainedWeight_continuous (by norm_num) (by norm_num)))
    ((profile_div_integrable hp).mul_continuousOn original_sigma_continuous)
  intro t ht
  have ht0 : 0<t := by linarith [ht.1]
  have h := mul_le_mul_of_nonneg_left (retainedPaid_le_sigma ht.1)
    (div_nonneg (nineProfile_nonneg hz t) ht0.le)
  convert h using 1 <;> first | rfl | skip
  unfold retainedWeight
  ring

theorem paidNumerator_le {z : Fin 9 → ℝ} (hz : ∀ k,0≤z k) :
    paidNumerator z ≤ numerator z := by
  apply Finset.sum_le_sum
  intro k _
  have hc := cell_bounds (a := 1) le_rfl (by norm_num [upperNode]) k
  have he : cellLeft 1 k=upperLeft k := by
    unfold cellLeft upperLeft
    split_ifs <;> rfl
  rw [he] at hc
  exact mul_le_mul_of_nonneg_left
    (retainedCellPaid_le (by linarith [hc.1]) (by linarith [hc.1,hc.2.1])) (hz k)

theorem paidActual_le_profile {z : Fin 9 → ℝ} (hz : ∀ k,0≤z k) :
    paidActual z ≤ aProfile (nineProfile z) :=
  (div_le_div_of_nonneg_right (paidNumerator_le hz) (sub_pos.mpr D0_lt_one).le).trans
    (actualLower_le_profile hz)

/-- Denominator weakening explicitly requires the paid numerator's sign. -/
theorem finiteLower_le_profile {z : Fin 9 → ℝ} (hz : ∀ k,0≤z k)
    (hn : 0≤paidNumerator z) : finiteLower z ≤ aProfile (nineProfile z) := by
  apply le_trans (b := paidActual z) _ (paidActual_le_profile hz)
  apply div_le_div_of_nonneg_left hn (sub_pos.mpr D0_lt_one)
  linarith only [retainedD0_le]

/-- An unconditional payment for the actual original H with its actual normalization. -/
theorem original_paidActual : paidActual NineFeedbackStrength.originalH ≤
    aProfile (nineProfile NineFeedbackStrength.originalH) :=
  paidActual_le_profile CoupledIntegralRecovery.originalH_nonneg

end
end RetainedCommonProfile
