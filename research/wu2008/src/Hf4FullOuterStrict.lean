import Hf4FullBalance

noncomputable section
namespace Hf4Full
open Real Set MeasureTheory NodeExtension FirstFeedbackIntegrals ActualNineFeedback
open SigmaVariableOuterPayment SigmaVariableFull
open scoped Interval BigOperators

/-- The existing outer envelope is genuinely lossy on the original interior. -/
theorem paidMass_lt_full {t : ℝ} (ht : t ∈ Icc 1 3) (hgt : 1 < t) :
    paidMass t < collectedMass t := by
  have hr : 1 < negRatio t := by
    unfold negRatio
    apply (one_lt_div (by positivity : 0 < 6*(t+1))).mpr
    have hp : 0 < (t-1)*t := mul_pos (sub_pos.mpr hgt) (by linarith)
    nlinarith only [hp]
  have h0 := mul_le_mul_of_nonpos_left (RemainingHf.le_splitUpper (zeroRatio_ge ht.1))
    (zero_coefficient_neg ht.1).le
  have h1 := mul_lt_mul_of_pos_left (Hf4Den.splitLower_lt hr) (neg_coefficient_pos ht.1)
  have hq := mul_le_mul_of_nonneg_left (RemainingHf.splitLower_le (quadRatio_ge ht.1))
    (quad_coefficient_pos ht).le
  have hrad := mul_le_mul_of_nonneg_left (RemainingHf.splitLower_le (radRatio_ge ht.1))
    (rad_coefficient_pos ht).le
  rw [mass_regrouped ht.1]
  unfold paidMass
  linarith only [h0,h1,hq,hrad]

theorem paidWeight_lt_full {t : ℝ} (ht : t ∈ Icc 1 3) (hgt : 1 < t) :
    paidWeight t < SigmaVariableFull.weight t := by
  unfold paidWeight SigmaVariableFull.weight
  rw [← collectedMass_identity]
  exact div_lt_div_of_pos_right (paidMass_lt_full ht hgt) (by linarith)

/-- No FTC is rerun: these cell integrals witness the missing outer-log loss only. -/
theorem outer_cell_loss_pos {a b : ℝ} (ha : 1 ≤ a) (hab : a < b) (hb : b ≤ 3) :
    0 < SigmaVariableFull.cellMass a b - rationalCellMass a b := by
  have hsub : uIcc a b ⊆ uIcc (1:ℝ) 3 := by
    rw [uIcc_of_le hab.le,uIcc_of_le (by norm_num : (1:ℝ)≤3)]
    intro t ht
    exact ⟨ha.trans ht.1,ht.2.trans hb⟩
  have hi := SigmaVariableFull.weight_continuous.mono hsub
  have hj := paidWeight_continuous.mono hsub
  unfold SigmaVariableFull.cellMass rationalCellMass
  rw [← intervalIntegral.integral_sub hi.intervalIntegrable hj.intervalIntegrable]
  exact intervalIntegral.intervalIntegral_pos_of_pos_on
    (hi.sub hj).intervalIntegrable
    (fun t ht => sub_pos.mpr (paidWeight_lt_full
      ⟨ha.trans ht.1.le,ht.2.le.trans hb⟩ (ha.trans_lt ht.1))) hab

/-- Strict, original-profile evidence that the 23-block FTC is not full-variable FTC. -/
theorem outerUnpaid_pos : 0 < outerUnpaid := by
  have he : outerUnpaid = ∑ k : Fin 9, NineFeedbackStrength.originalH k *
      (SigmaVariableFull.cellMass (upperLeft k) (upperNode k) -
        rationalCellMass (upperLeft k) (upperNode k)) := by
    unfold outerUnpaid
    rw [SigmaActualBlockSeparable.endpointNumerator_eq_rational]
    simp only [SigmaVariableFull.numerator,rationalNumerator,mul_sub,Finset.sum_sub_distrib]
  rw [he]
  apply Finset.sum_pos'
  · intro k _
    obtain ⟨ha,_,hb⟩ := SigmaEndpointPayment.original_cell_bounds k
    exact mul_nonneg (CoupledIntegralRecovery.originalH_nonneg k)
      (outer_cell_loss_pos ha (Hf4Next.original_cell_strict k) hb).le
  · obtain ⟨k,hk⟩ := Hf4Next.original_has_positive_weight
    obtain ⟨ha,_,hb⟩ := SigmaEndpointPayment.original_cell_bounds k
    exact ⟨k,Finset.mem_univ k,mul_pos hk
      (outer_cell_loss_pos ha (Hf4Next.original_cell_strict k) hb)⟩

theorem endpointNumerator_lt_full : endpointNumerator < numerator := by
  rw [numerator_endpoint_balance]
  exact lt_add_of_pos_right _ outerUnpaid_pos

theorem endpointProfile_lt_full : endpointProfile < profile :=
  div_lt_div_of_pos_right endpointNumerator_lt_full (sub_pos.mpr D0FullDensity.dPaid_lt_one)

theorem endpointTerminal_lt_full : endpointTerminal < terminal := by
  unfold endpointTerminal terminal
  exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left endpointProfile_lt_full
    (log_pos (by norm_num : (1:ℝ)<2))) le_rfl

end Hf4Full
