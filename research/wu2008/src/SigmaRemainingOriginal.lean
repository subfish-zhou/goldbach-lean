import SigmaRemainingPositive
namespace SigmaRemaining
open Real NodeExtension FirstFeedbackIntegrals Wu2008DoubleSieve ActualNineFeedback
open scoped BigOperators
noncomputable section

theorem original_numerator_pos : 0 < numerator NineFeedbackStrength.originalH := by
  have h0 := cell_0_pos
  have h1 := cell_1_pos
  have h2 := cell_2_pos
  have h3 := cell_3_pos
  have h4 := cell_4_pos
  have h5 := cell_5_pos
  have h6 := cell_6_pos
  have h7 := cell_7_pos
  have h8 := cell_8_pos
  simp only [numerator,Fin.sum_univ_succ]
  dsimp [NineFeedbackStrength.originalH]
  positivity

theorem original_finiteLower : finiteLower NineFeedbackStrength.originalH ≤
    aProfile (nineProfile NineFeedbackStrength.originalH) :=
  finiteLower_le_profile CoupledIntegralRecovery.originalH_nonneg original_numerator_pos.le

theorem original_finiteLower_pos : 0 < finiteLower NineFeedbackStrength.originalH :=
  div_pos original_numerator_pos (sub_pos.mpr d0Paid_lt_one)

/-- The original terminal has zero J, with its full log 2 coefficient retained. -/
def terminalLower : ℝ := log 2*finiteLower NineFeedbackStrength.originalH+
  RemainingHf.paidCells NineFeedbackStrength.originalH 3


def terminalFinite : ℝ := RemainingHf.splitLower 2*finiteLower NineFeedbackStrength.originalH+
  RemainingHf.paidCells NineFeedbackStrength.originalH 3


end
end SigmaRemaining
