import Hf4DenBalance
import SigmaActualNineCellFTC

noncomputable section
namespace Hf4Full
open Real NodeExtension FirstFeedbackIntegrals ActualNineFeedback

/-- The full-variable numerator is still an outer integral, NOT an endpoint payment. -/
def numerator : ℝ := SigmaVariableFull.numerator NineFeedbackStrength.originalH +
  Hf4Continue.newVariation NineFeedbackStrength.originalH

theorem old_numerator_le : Hf4Den.numerator ≤ numerator := Hf4Den.numerator_le_full

theorem numerator_pos : 0 < numerator := Hf4Den.numerator_pos.trans_le old_numerator_le

/-- The disjoint log-minus-basicLower remainder is consumed only through its proved bridge. -/
theorem numerator_le_actual : numerator ≤
    ∫ t in (1:ℝ)..3, nineProfile NineFeedbackStrength.originalH t/t*sigma 3 (t+2) (t+1) :=
  Hf4Continue.full_numerator_add_new_le

/-- Same original dPaid max and true D0; only the paid numerator is upgraded. -/
def profile : ℝ := numerator/(1-D0FullDensity.dPaid)

theorem profile_pos : 0 < profile :=
  div_pos numerator_pos (sub_pos.mpr D0FullDensity.dPaid_lt_one)

theorem old_profile_le : Hf4Den.profile ≤ profile :=
  div_le_div_of_nonneg_right old_numerator_le (sub_pos.mpr D0FullDensity.dPaid_lt_one).le

theorem profile_le_actual : profile ≤ aProfile (nineProfile NineFeedbackStrength.originalH) := by
  calc
    profile ≤ numerator/(1-D0) :=
      div_le_div_of_nonneg_left numerator_pos.le (sub_pos.mpr D0_lt_one)
        (by linarith only [D0FullDensity.dPaid_le])
    _ ≤ _ := by
      rw [aProfile_eq]
      exact div_le_div_of_nonneg_right numerator_le_actual (sub_pos.mpr D0_lt_one).le

/-- Original E endpoint replaces signed massPaid once, never adds to it. -/
def terminal : ℝ := log 2*profile + TerminalECells.mass NineFeedbackStrength.originalH

theorem terminal_le_actual : terminal ≤ firstFeedback NineFeedbackStrength.originalH 3 3 := by
  have ha := mul_le_mul_of_nonneg_left profile_le_actual (log_nonneg (by norm_num : (1:ℝ)≤2))
  have he := TerminalECells.mass_le CoupledIntegralRecovery.originalH_nonneg
  unfold terminal
  simp only [firstFeedback,profileJ,intervalIntegral.integral_same,zero_div,add_zero]
  linarith only [ha,he]

theorem old_terminal_le : Hf4Den.terminal ≤ terminal :=
  add_le_add (mul_le_mul_of_nonneg_left old_profile_le
    (log_nonneg (by norm_num : (1:ℝ)≤2))) le_rfl

theorem continue_terminal_lt : Hf4Continue.terminal < terminal :=
  Hf4Den.old_terminal_lt.trans_le old_terminal_le

/-- This numerator really uses the frozen complete 23-block primitive endpoint certificate. -/
def endpointNumerator : ℝ := SigmaActualBlockSeparable.endpointNumerator NineFeedbackStrength.originalH +
  Hf4Continue.newVariation NineFeedbackStrength.originalH

/-- FTC identifies the rational paid kernel, not the full logarithmic outer kernel. -/
theorem endpointNumerator_eq_rational : endpointNumerator =
    SigmaVariableOuterPayment.rationalNumerator NineFeedbackStrength.originalH +
      Hf4Continue.newVariation NineFeedbackStrength.originalH := by
  unfold endpointNumerator
  rw [SigmaActualBlockSeparable.endpointNumerator_eq_rational]

theorem endpointNumerator_le_full : endpointNumerator ≤ numerator := by
  rw [endpointNumerator_eq_rational]
  exact add_le_add
    (SigmaVariableOuterPayment.rationalNumerator_le CoupledIntegralRecovery.originalH_nonneg) le_rfl

theorem endpointNumerator_le_actual : endpointNumerator ≤
    ∫ t in (1:ℝ)..3, nineProfile NineFeedbackStrength.originalH t/t*sigma 3 (t+2) (t+1) :=
  endpointNumerator_le_full.trans numerator_le_actual

/-- No max with the old terminal and no unproved positivity assumption. -/
def endpointProfile : ℝ := endpointNumerator/(1-D0FullDensity.dPaid)

theorem endpointProfile_le_full : endpointProfile ≤ profile :=
  div_le_div_of_nonneg_right endpointNumerator_le_full (sub_pos.mpr D0FullDensity.dPaid_lt_one).le

theorem endpointProfile_le_actual : endpointProfile ≤ aProfile (nineProfile NineFeedbackStrength.originalH) :=
  endpointProfile_le_full.trans profile_le_actual

def endpointTerminal : ℝ := log 2*endpointProfile + TerminalECells.mass NineFeedbackStrength.originalH

theorem endpointTerminal_le_full : endpointTerminal ≤ terminal :=
  add_le_add (mul_le_mul_of_nonneg_left endpointProfile_le_full
    (log_nonneg (by norm_num : (1:ℝ)≤2))) le_rfl

/-- Unconditional original consumer of the actual 23-block endpoints plus disjoint log remainder. -/
theorem endpointTerminal_le_actual : endpointTerminal ≤ firstFeedback NineFeedbackStrength.originalH 3 3 :=
  endpointTerminal_le_full.trans terminal_le_actual

end Hf4Full
