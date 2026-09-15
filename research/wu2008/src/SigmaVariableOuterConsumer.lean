import SigmaVariableOuterIntegral

noncomputable section
namespace SigmaVariableOuterPayment
open Real SigmaVariableFull FirstFeedbackIntegrals ActualNineFeedback NodeExtension

/-- The exact original denominator is unchanged, and the old branch is retained. -/
def rationalProfile : ℝ := max CorrectionD0Joint.profile
  (rationalNumerator NineFeedbackStrength.originalH/(1-D0FullDensity.finiteD))

theorem rationalProfile_le : rationalProfile ≤ SigmaVariableFull.profile NineFeedbackStrength.originalH := by
  apply max_le SigmaVariableFull.old_profile_le
  exact div_le_div_of_nonneg_right
    (rationalNumerator_le CoupledIntegralRecovery.originalH_nonneg)
    (sub_pos.mpr D0FullDensity.finiteD_lt_one).le

theorem rationalProfile_le_actual :
    rationalProfile ≤ aProfile (nineProfile NineFeedbackStrength.originalH) :=
  rationalProfile_le.trans SigmaVariableFull.profile_le_actual

/-- The existing S=3 E payment occurs once; the outer rational integrals remain explicit. -/
def rationalTerminal : ℝ := log 2*rationalProfile+
  TerminalESigned.massPaid NineFeedbackStrength.originalH

theorem rationalTerminal_le : rationalTerminal ≤ SigmaVariableFull.terminal := by
  exact add_le_add (mul_le_mul_of_nonneg_left rationalProfile_le
    (log_nonneg (by norm_num : (1:ℝ) ≤ 2))) le_rfl

theorem rationalTerminal_le_actual :
    rationalTerminal ≤ firstFeedback NineFeedbackStrength.originalH 3 3 :=
  rationalTerminal_le.trans SigmaVariableFull.terminal_le_actual

theorem old_terminal_le_rational : CorrectionD0Joint.terminal ≤ rationalTerminal := by
  have hl := mul_le_mul_of_nonneg_right (RemainingHf.splitLower_le (by norm_num : (1:ℝ) ≤ 2))
    CorrectionD0Joint.profile_pos.le
  have hp := mul_le_mul_of_nonneg_left
    (le_max_left CorrectionD0Joint.profile
      (rationalNumerator NineFeedbackStrength.originalH/(1-D0FullDensity.finiteD)))
    (log_nonneg (by norm_num : (1:ℝ) ≤ 2))
  unfold CorrectionD0Joint.terminal rationalTerminal rationalProfile
  linarith only [hl,hp]

end SigmaVariableOuterPayment
