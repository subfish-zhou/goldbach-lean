import Hf4RefineMoving

noncomputable section
namespace Hf4Refine
open Real Set MeasureTheory NodeExtension FirstFeedbackIntegrals ActualNineFeedback
open scoped BigOperators

/-- Original nine cells and weights, now with the fully moving lower density. -/
def finiteVariation (z : Fin 9 → ℝ) : ℝ :=
  ∑ k : Fin 9, z k*movingCellPayment (upperLeft k) (upperNode k)

theorem amplified_old_variation_le {z : Fin 9 → ℝ} (hz : ∀ k, 0 ≤ z k) :
    (5/3:ℝ)*Hf4Next.finiteVariation z ≤ finiteVariation z := by
  unfold finiteVariation Hf4Next.finiteVariation
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  obtain ⟨ha,hab,_⟩ := SigmaEndpointPayment.original_cell_bounds k
  have h := (amplified_old_cell_le ha hab).trans (cellPayment_le_moving ha hab)
  convert mul_le_mul_of_nonneg_left h (hz k) using 1
  ring

theorem finiteVariation_nonneg {z : Fin 9 → ℝ} (hz : ∀ k, 0 ≤ z k) :
    0 ≤ finiteVariation z :=
  (mul_nonneg (by norm_num) (Hf4Next.finiteVariation_nonneg hz)).trans (amplified_old_variation_le hz)

theorem old_variation_lt :
    Hf4Next.finiteVariation NineFeedbackStrength.originalH < finiteVariation NineFeedbackStrength.originalH := by
  have hpos := (SigmaEndpointPayment.finiteVariation_nonneg
    CoupledIntegralRecovery.originalH_nonneg).trans_lt Hf4Next.original_variation_strict
  have hamp := amplified_old_variation_le CoupledIntegralRecovery.originalH_nonneg
  linarith only [hpos,hamp]

theorem old_numerator_add_payment_le {z : Fin 9 → ℝ} (hz : ∀ k, 0 ≤ z k) :
    SigmaInnerProfile.numerator z + finiteVariation z ≤ SigmaVariableFull.numerator z := by
  unfold SigmaInnerProfile.numerator finiteVariation SigmaVariableFull.numerator
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro k _
  obtain ⟨ha,hab,hb⟩ := SigmaEndpointPayment.original_cell_bounds k
  simpa only [mul_add] using mul_le_mul_of_nonneg_left (old_cell_add_movingPayment_le ha hab hb) (hz k)

/-- The existing joint maximum and original denominator are retained unchanged. -/
def finiteProfile : ℝ :=
  (CorrectionD0Joint.numerator+finiteVariation NineFeedbackStrength.originalH)/(1-D0FullDensity.finiteD)

theorem old_profile_lt : Hf4Next.finiteProfile < finiteProfile := by
  exact div_lt_div_of_pos_right (add_lt_add_right old_variation_lt _)
    (sub_pos.mpr D0FullDensity.finiteD_lt_one)

theorem finiteProfile_pos : 0 < finiteProfile := Hf4Next.finiteProfile_pos.trans old_profile_lt

theorem finiteProfile_le_full : finiteProfile ≤ SigmaVariableFull.profile NineFeedbackStrength.originalH := by
  apply div_le_div_of_nonneg_right _ (sub_pos.mpr D0FullDensity.finiteD_lt_one).le
  exact (add_le_add CorrectionD0Joint.numerator_le le_rfl).trans
    (old_numerator_add_payment_le CoupledIntegralRecovery.originalH_nonneg)

/-- Parent can supply these two facts to its already-paid generic profile consumer. -/
theorem finiteProfile_le_actual :
    finiteProfile ≤ aProfile (nineProfile NineFeedbackStrength.originalH) :=
  finiteProfile_le_full.trans SigmaVariableFull.profile_le_actual

def terminal : ℝ := log 2*finiteProfile+TerminalESigned.massPaid NineFeedbackStrength.originalH

theorem terminal_le_actual : terminal ≤ firstFeedback NineFeedbackStrength.originalH 3 3 := by
  apply le_trans (b := SigmaVariableFull.terminal)
  · exact add_le_add (mul_le_mul_of_nonneg_left finiteProfile_le_full
      (log_nonneg (by norm_num : (1:ℝ) ≤ 2))) le_rfl
  · exact SigmaVariableFull.terminal_le_actual

theorem old_terminal_lt : Hf4Next.terminal < terminal :=
  add_lt_add_left (mul_lt_mul_of_pos_left old_profile_lt (log_pos (by norm_num : (1:ℝ) < 2))) _

/-- Exact increment is paid against the original unpaid ledger, with E once. -/
theorem payment_le_original_unpaid :
    RemainingHf.splitLower 2*finiteVariation NineFeedbackStrength.originalH/
      (1-D0FullDensity.finiteD) ≤ CorrectionD0Joint.allUnpaid := by
  have hl := mul_le_mul_of_nonneg_right
    (RemainingHf.splitLower_le (by norm_num : (1:ℝ) ≤ 2)) finiteProfile_pos.le
  have ht := terminal_le_actual
  rw [CorrectionD0Joint.actual_terminal_balance] at ht
  unfold terminal at ht
  have hbal : RemainingHf.splitLower 2*finiteProfile+
      TerminalESigned.massPaid NineFeedbackStrength.originalH = CorrectionD0Joint.terminal+
      RemainingHf.splitLower 2*finiteVariation NineFeedbackStrength.originalH/(1-D0FullDensity.finiteD) := by
    unfold finiteProfile CorrectionD0Joint.terminal CorrectionD0Joint.profile
    ring
  linarith only [hl,ht,hbal]

end Hf4Refine
