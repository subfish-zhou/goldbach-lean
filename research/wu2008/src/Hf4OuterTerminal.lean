import Hf4OuterCells

noncomputable section
namespace Hf4Outer
open Real NodeExtension FirstFeedbackIntegrals ActualNineFeedback

/-- Frozen complete 23-block endpoints, disjoint inner log remainder, and new outer payment. -/
def numerator : ℝ := Hf4Full.endpointNumerator+payment

theorem numerator_eq_finite : numerator =
    SigmaActualBlockSeparable.endpointNumerator NineFeedbackStrength.originalH+
      Hf4Continue.newVariation NineFeedbackStrength.originalH+payment := rfl

theorem numerator_lt_full : numerator < Hf4Full.numerator := by
  rw [Hf4Full.numerator_endpoint_balance]
  unfold numerator
  linarith only [payment_lt_outerUnpaid]

theorem numerator_le_actual : numerator ≤
    ∫ t in (1:ℝ)..3, nineProfile NineFeedbackStrength.originalH t/t*sigma 3 (t+2) (t+1) :=
  numerator_lt_full.le.trans Hf4Full.numerator_le_actual

/-- Same dPaid common maximum; no sign premise for the new finite numerator. -/
def profile : ℝ := numerator/(1-D0FullDensity.dPaid)

theorem profile_lt_full : profile < Hf4Full.profile :=
  div_lt_div_of_pos_right numerator_lt_full (sub_pos.mpr D0FullDensity.dPaid_lt_one)

theorem profile_le_actual : profile ≤ aProfile (nineProfile NineFeedbackStrength.originalH) :=
  profile_lt_full.le.trans Hf4Full.profile_le_actual

/-- Original E endpoint mass occurs exactly once. -/
def terminal : ℝ := log 2*profile+TerminalECells.mass NineFeedbackStrength.originalH

theorem terminal_eq_finite : terminal =
    log 2*((SigmaActualBlockSeparable.endpointNumerator NineFeedbackStrength.originalH+
      Hf4Continue.newVariation NineFeedbackStrength.originalH+payment)/(1-D0FullDensity.dPaid))+
      TerminalECells.mass NineFeedbackStrength.originalH := rfl

theorem terminal_lt_full : terminal < Hf4Full.terminal := by
  exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left profile_lt_full
    (log_pos (by norm_num : (1:ℝ) < 2))) le_rfl

/-- Unconditional finite terminal bound for the actual original first-feedback object. -/
theorem terminal_le_actual : terminal ≤ firstFeedback NineFeedbackStrength.originalH 3 3 :=
  terminal_lt_full.le.trans Hf4Full.terminal_le_actual

theorem terminal_lt_actual : terminal < firstFeedback NineFeedbackStrength.originalH 3 3 :=
  terminal_lt_full.trans_le Hf4Full.terminal_le_actual

theorem terminal_endpoint_gain : terminal =
    Hf4Full.endpointTerminal+log 2*payment/(1-D0FullDensity.dPaid) := by
  unfold terminal profile numerator Hf4Full.endpointTerminal Hf4Full.endpointProfile
  ring

/-- A genuine positive finite payment improves the existing 23-block terminal. -/
theorem endpointTerminal_lt : Hf4Full.endpointTerminal < terminal := by
  rw [terminal_endpoint_gain]
  exact lt_add_of_pos_right _ (div_pos
    (mul_pos (log_pos (by norm_num : (1:ℝ) < 2)) payment_pos)
    (sub_pos.mpr D0FullDensity.dPaid_lt_one))

end Hf4Outer
