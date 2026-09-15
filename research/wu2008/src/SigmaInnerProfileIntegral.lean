import SigmaInnerProfileBase

namespace SigmaInnerProfile
open Real Set MeasureTheory NodeExtension FirstFeedbackIntegrals OriginalProfileSigmaPayment
open OriginalSigmaStrength Wu04WholeCollection
open scoped Interval BigOperators
noncomputable section

/-- Exact original cell integral. This is not a finite endpoint payment. -/
def cellIntegral (a b : ℝ) : ℝ := ∫ t in a..b, weight t

def numerator (z : Fin 9 → ℝ) : ℝ :=
  ∑ k : Fin 9, z k * cellIntegral (upperLeft k) (upperNode k)

theorem numerator_integral (z : Fin 9 → ℝ) :
    numerator z = ∫ t in (1:ℝ)..3, nineProfile z t * weight t := by
  rw [profile_integral_cells z le_rfl (by norm_num [upperNode])
    (weight_continuous (by norm_num) (by norm_num))]
  apply Finset.sum_congr rfl
  intro k _
  have he : cellLeft 1 k=upperLeft k := by
    unfold cellLeft upperLeft
    split_ifs <;> rfl
  rw [he]
  rfl

theorem old_cell_le {a b : ℝ} (ha : 1≤a) (hab : a≤b) (hb : b≤3) :
    SigmaRemaining.cellPaid a b ≤ cellIntegral a b := by
  apply (SigmaRemaining.cellPaid_le (by linarith) hab).trans
  rw [← SigmaExistingLogError.weight_integral (by linarith : 0<a) hab]
  apply intervalIntegral.integral_mono_on hab
    (SigmaExistingLogError.weight_continuous (by linarith) hab).intervalIntegrable
    (weight_continuous (by linarith) hab).intervalIntegrable
  intro t ht
  exact old_weight_le (ha.trans ht.1) (ht.2.trans hb)

theorem old_ninth_cell_le (k : Fin 9) :
    SigmaRemaining.cellPaid (upperLeft k) (upperNode k) ≤
      cellIntegral (upperLeft k) (upperNode k) := by
  have h := cell_bounds (a := 1) le_rfl (by norm_num [upperNode]) k
  have he : cellLeft 1 k=upperLeft k := by
    unfold cellLeft upperLeft
    split_ifs <;> rfl
  rw [he] at h
  exact old_cell_le h.1 h.2.1 h.2.2.1

theorem old_numerator_le {z : Fin 9 → ℝ} (hz : ∀ k,0≤z k) :
    SigmaRemaining.numerator z ≤ numerator z := by
  apply Finset.sum_le_sum
  intro k _
  exact mul_le_mul_of_nonneg_left (old_ninth_cell_le k) (hz k)

theorem original_numerator_pos : 0 < numerator NineFeedbackStrength.originalH :=
  SigmaRemaining.original_numerator_pos.trans_le
    (old_numerator_le CoupledIntegralRecovery.originalH_nonneg)

/-- The actual denominator is retained. -/
def actualLower (z : Fin 9 → ℝ) : ℝ := numerator z/(1-D0)

/-- The denominator is finite; the numerator remains an exact integral. -/
def d0Lower (z : Fin 9 → ℝ) : ℝ := numerator z/(1-SigmaRemaining.d0Paid)

theorem actualLower_le_profile {z : Fin 9 → ℝ} (hz : ∀ k,0≤z k) :
    actualLower z ≤ aProfile (nineProfile z) := by
  rw [actualLower,aProfile_eq,numerator_integral]
  apply div_le_div_of_nonneg_right _ (sub_pos.mpr D0_lt_one).le
  have hp := nineProfile_integrable z
  apply intervalIntegral.integral_mono_on (by norm_num)
    (hp.mul_continuousOn (weight_continuous (by norm_num) (by norm_num)))
    ((profile_div_integrable hp).mul_continuousOn original_sigma_continuous)
  intro t ht
  have h := mul_le_mul_of_nonneg_left (weight_le_sigma ht.1) (nineProfile_nonneg hz t)
  convert h using 1 <;> first | rfl | skip
  ring

theorem original_d0Lower_le_profile : d0Lower NineFeedbackStrength.originalH ≤
    aProfile (nineProfile NineFeedbackStrength.originalH) := by
  apply le_trans (b := actualLower NineFeedbackStrength.originalH) _
    (actualLower_le_profile CoupledIntegralRecovery.originalH_nonneg)
  exact div_le_div_of_nonneg_left original_numerator_pos.le (sub_pos.mpr D0_lt_one)
    (by linarith only [SigmaRemaining.d0Paid_le])

theorem original_d0Lower_pos : 0 < d0Lower NineFeedbackStrength.originalH :=
  div_pos original_numerator_pos (sub_pos.mpr SigmaRemaining.d0Paid_lt_one)

theorem old_finiteLower_le : SigmaRemaining.finiteLower NineFeedbackStrength.originalH ≤
    d0Lower NineFeedbackStrength.originalH :=
  div_le_div_of_nonneg_right (old_numerator_le CoupledIntegralRecovery.originalH_nonneg)
    (sub_pos.mpr SigmaRemaining.d0Paid_lt_one).le

end
end SigmaInnerProfile
