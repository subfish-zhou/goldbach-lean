import SigmaExistingOuter

namespace SigmaExistingLogError
open Real Set MeasureTheory NodeExtension FirstFeedbackIntegrals OriginalProfileSigmaPayment
open OriginalSigmaStrength Wu04WholeCollection
open scoped Interval BigOperators
noncomputable section

/-- All nine original cells, without changing their endpoints. -/
def numerator (z : Fin 9 → ℝ) : ℝ :=
  ∑ k : Fin 9,z k*(primitive (upperNode k)-primitive (upperLeft k))
def paidNumerator (z : Fin 9 → ℝ) : ℝ :=
  ∑ k : Fin 9,z k*cellPaid (upperLeft k) (upperNode k)
def paidD0 : ℝ := endpointPaid 3
def actualLower (z : Fin 9 → ℝ) : ℝ := paidNumerator z/(1-D0)
def finiteLower (z : Fin 9 → ℝ) : ℝ := paidNumerator z/(1-paidD0)

theorem paidD0_le : paidD0 ≤ D0 := by
  have h := endpointPaid_le_sigma (t := 3) (by norm_num) (by norm_num)
  norm_num only [show (3:ℝ)+2=5 by norm_num,show (3:ℝ)+1=4 by norm_num] at h
  exact h

theorem paidD0_lt_one : paidD0<1 := paidD0_le.trans_lt D0_lt_one

theorem numerator_integral (z : Fin 9 → ℝ) :
    numerator z = ∫ t in (1:ℝ)..3,nineProfile z t*weight t := by
  rw [profile_integral_cells z le_rfl (by norm_num [upperNode])
    (weight_continuous (by norm_num) (by norm_num))]
  apply Finset.sum_congr rfl
  intro k _
  have hb := cell_bounds (a := 1) le_rfl (by norm_num [upperNode]) k
  have he : cellLeft 1 k=upperLeft k := by
    unfold cellLeft upperLeft
    split_ifs <;> rfl
  rw [weight_integral (by linarith [hb.1] : 0<cellLeft 1 k) hb.2.1,he]

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
    (cellPaid_le (by linarith [hc.1]) (by linarith [hc.1,hc.2.1])) (hz k)

/-- The unchanged genuine common profile, retaining its actual denominator 1-D0. -/
theorem actualLower_le_profile {z : Fin 9 → ℝ} (hz : ∀ k,0≤z k) :
    actualLower z ≤ aProfile (nineProfile z) := by
  rw [actualLower,aProfile_eq]
  apply div_le_div_of_nonneg_right _ (sub_pos.mpr D0_lt_one).le
  apply (paidNumerator_le hz).trans
  rw [numerator_integral]
  have hp := nineProfile_integrable z
  apply intervalIntegral.integral_mono_on (by norm_num)
    (hp.mul_continuousOn (weight_continuous (by norm_num) (by norm_num)))
    ((profile_div_integrable hp).mul_continuousOn original_sigma_continuous)
  intro t ht
  have ht0 : 0<t := by linarith [ht.1]
  have h := mul_le_mul_of_nonneg_left (endpointPaid_le_sigma ht.1 ht.2)
    (div_nonneg (nineProfile_nonneg hz t) ht0.le)
  convert h using 1 <;> first | rfl | skip
  unfold weight
  ring

/-- Weakening the denominator is permitted only after numerator nonnegativity is paid. -/
theorem finiteLower_le_profile {z : Fin 9 → ℝ} (hz : ∀ k,0≤z k)
    (hn : 0≤paidNumerator z) : finiteLower z ≤ aProfile (nineProfile z) := by
  apply le_trans (b := actualLower z) _ (actualLower_le_profile hz)
  apply div_le_div_of_nonneg_left hn (sub_pos.mpr D0_lt_one)
  linarith only [paidD0_le]

end
end SigmaExistingLogError
