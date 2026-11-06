import CorrectionSigmaVariationIntegral

noncomputable section
namespace CorrectionD0Joint
open Real NodeExtension FirstFeedbackIntegrals ActualNineFeedback

/-- The remaining inner sigma integral, beyond the endpoint-beta kernel. -/
def intrinsicSigmaUnpaid : ℝ := aProfile (nineProfile NineFeedbackStrength.originalH)-
  SigmaInnerProfile.actualLower NineFeedbackStrength.originalH

theorem intrinsicSigmaUnpaid_nonneg : 0 ≤ intrinsicSigmaUnpaid := sub_nonneg.mpr
  (SigmaInnerProfile.actualLower_le_profile CoupledIntegralRecovery.originalH_nonneg)

/-- The old S=3 E remainder is reused, not replaced or added twice. -/
def intrinsicEUnpaid : ℝ := eProfile (nineProfile NineFeedbackStrength.originalH) 3-
  (aProfile (nineProfile NineFeedbackStrength.originalH)*log 2+
    TerminalECells.mass NineFeedbackStrength.originalH)

theorem intrinsicEUnpaid_nonneg : 0 ≤ intrinsicEUnpaid :=
  sub_nonneg.mpr (TerminalECells.mass_le CoupledIntegralRecovery.originalH_nonneg)

def allUnpaid : ℝ := terminalUnpaid+log 2*intrinsicSigmaUnpaid+intrinsicEUnpaid


/-- Exact equality to the original terminal, with both formerly dropped intrinsic integrals. -/
theorem actual_terminal_balance : firstFeedback NineFeedbackStrength.originalH 3 3=
    terminal+allUnpaid := by
  have he := retainedTerminal_balance
  unfold retainedTerminal at he
  unfold allUnpaid intrinsicSigmaUnpaid intrinsicEUnpaid
  simp only [firstFeedback,profileJ,intervalIntegral.integral_same,zero_div,add_zero]
  linarith only [he]

/-- Honest necessary-and-sufficient remaining scalar. No sign certificate is assumed proved. -/
theorem original_hf4_iff_unpaid :
    (NineFeedbackStrength.originalH 8 ≤ firstFeedback NineFeedbackStrength.originalH 3 3) ↔
    NineFeedbackStrength.originalH 8-terminal ≤ allUnpaid := by
  rw [actual_terminal_balance]
  exact (sub_le_iff_le_add').symm


end CorrectionD0Joint
