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

theorem allUnpaid_nonneg : 0 ≤ allUnpaid := add_nonneg
  (add_nonneg terminalUnpaid_nonneg (mul_nonneg (log_nonneg (by norm_num : (1:ℝ) ≤ 2))
    intrinsicSigmaUnpaid_nonneg)) intrinsicEUnpaid_nonneg

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

/-- Reuse the four unchanged original rows; this does not assert the remaining scalar. -/
theorem original_five_iff_unpaid :
    (∀ i : Fin 5, NineFeedbackStrength.originalH (Fin.natAdd 4 i) ≤
      Wu04FirstCore.publication i+
        firstFeedback NineFeedbackStrength.originalH (firstNode i) (firstS i)) ↔
    NineFeedbackStrength.originalH 8-terminal ≤ allUnpaid := by
  rw [← original_hf4_iff_unpaid]
  have hn : firstNode (4 : Fin 5)=3 := by norm_num [firstNode]
  have hs : firstS (4 : Fin 5)=3 := rfl
  have hp : Wu04FirstCore.publication (4 : Fin 5)=0 := rfl
  constructor
  · intro h
    have h4 := h 4
    rw [hn,hs,hp,zero_add] at h4
    exact h4
  · intro h i
    by_cases hi : i.val < 4
    · exact Hf03OriginalTargets.original_hf_first_four i hi
    · have he : i=(4 : Fin 5) := by apply Fin.ext; omega
      subst i
      rw [hn,hs,hp,zero_add]
      exact h

end CorrectionD0Joint
