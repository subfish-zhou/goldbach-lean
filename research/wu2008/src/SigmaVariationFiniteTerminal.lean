import SigmaVariationFiniteCells

noncomputable section
namespace SigmaEndpointPayment
open Real Set MeasureTheory NodeExtension FirstFeedbackIntegrals ActualNineFeedback
open scoped BigOperators

/-- The original nine weights and original cell endpoints, with no new reference profile. -/
def finiteVariation (z : Fin 9 → ℝ) : ℝ :=
  ∑ k : Fin 9, z k * cellPayment (upperLeft k) (upperNode k)

theorem original_cell_bounds (k : Fin 9) :
    1 ≤ upperLeft k ∧
    upperLeft k ≤ upperNode k ∧ upperNode k ≤ 3 := by
  exact SigmaCorrectionFTC.original_cell_bounds k

theorem finiteVariation_nonneg {z : Fin 9 → ℝ} (hz : ∀ k, 0 ≤ z k) :
    0 ≤ finiteVariation z := by
  apply Finset.sum_nonneg
  intro k _
  obtain ⟨ha,hab,_⟩ := original_cell_bounds k
  exact mul_nonneg (hz k) (cellPayment_nonneg ha hab)

/-- This is an unconditional finite payment, rather than an integral-defined remainder. -/
theorem old_numerator_add_payment_le {z : Fin 9 → ℝ} (hz : ∀ k, 0 ≤ z k) :
    SigmaInnerProfile.numerator z + finiteVariation z ≤ SigmaVariableFull.numerator z := by
  unfold SigmaInnerProfile.numerator finiteVariation SigmaVariableFull.numerator
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro k _
  obtain ⟨ha,hab,hb⟩ := original_cell_bounds k
  simpa only [mul_add] using mul_le_mul_of_nonneg_left (old_cell_add_payment_le ha hab hb) (hz k)

/-- The original common-max numerator is paid before any variation is added. -/
def finiteProfile : ℝ :=
  (CorrectionD0Joint.numerator + finiteVariation NineFeedbackStrength.originalH)/
    (1-D0FullDensity.finiteD)

theorem finiteProfile_balance : finiteProfile = CorrectionD0Joint.profile +
    finiteVariation NineFeedbackStrength.originalH/(1-D0FullDensity.finiteD) := by
  exact add_div _ _ _

theorem finiteProfile_pos : 0 < finiteProfile := by
  rw [finiteProfile_balance]
  exact add_pos_of_pos_of_nonneg CorrectionD0Joint.profile_pos
    (div_nonneg (finiteVariation_nonneg CoupledIntegralRecovery.originalH_nonneg)
      (sub_pos.mpr D0FullDensity.finiteD_lt_one).le)

theorem finiteProfile_le_full :
    finiteProfile ≤ SigmaVariableFull.profile NineFeedbackStrength.originalH := by
  apply div_le_div_of_nonneg_right _ (sub_pos.mpr D0FullDensity.finiteD_lt_one).le
  exact (add_le_add CorrectionD0Joint.numerator_le le_rfl).trans
    (old_numerator_add_payment_le CoupledIntegralRecovery.originalH_nonneg)

theorem finiteProfile_le_actual :
    finiteProfile ≤ aProfile (nineProfile NineFeedbackStrength.originalH) :=
  finiteProfile_le_full.trans SigmaVariableFull.profile_le_actual

/-- The unchanged signed E amount occurs exactly once. -/
def finiteTerminal : ℝ := RemainingHf.splitLower 2 * finiteProfile +
  TerminalESigned.massPaid NineFeedbackStrength.originalH

/-- An exact algebraic payment over the original common-max terminal. -/
theorem finiteTerminal_balance : finiteTerminal = CorrectionD0Joint.terminal +
    RemainingHf.splitLower 2 * finiteVariation NineFeedbackStrength.originalH /
      (1-D0FullDensity.finiteD) := by
  unfold finiteTerminal CorrectionD0Joint.terminal
  rw [finiteProfile_balance]
  ring

theorem finiteTerminal_le_actual :
    finiteTerminal ≤ firstFeedback NineFeedbackStrength.originalH 3 3 := by
  have hl := mul_le_mul_of_nonneg_right
    (RemainingHf.splitLower_le (by norm_num : (1:ℝ) ≤ 2)) finiteProfile_pos.le
  have hp := mul_le_mul_of_nonneg_left finiteProfile_le_full
    (log_nonneg (by norm_num : (1:ℝ) ≤ 2))
  apply le_trans (b := SigmaVariableFull.terminal)
  · unfold finiteTerminal SigmaVariableFull.terminal
    linarith only [hl,hp]
  · exact SigmaVariableFull.terminal_le_actual

end SigmaEndpointPayment
