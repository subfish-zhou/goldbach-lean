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

theorem terminalLower_le : terminalLower ≤ firstFeedback NineFeedbackStrength.originalH 3 3 := by
  have he := RemainingHf.paidCells_le CoupledIntegralRecovery.originalH_nonneg
    (by norm_num : (3:ℝ)≤3) (by norm_num [upperNode] : (3:ℝ)-2≤upperNode 0)
  have ha := mul_le_mul_of_nonneg_left original_finiteLower (log_nonneg (by norm_num : (1:ℝ)≤2))
  norm_num only [show (3:ℝ)-1=2 by norm_num,show (4:ℝ)/2=2 by norm_num] at he
  unfold terminalLower
  simp only [firstFeedback,profileJ,intervalIntegral.integral_same,zero_div,add_zero]
  linarith only [ha,he]

def terminalFinite : ℝ := RemainingHf.splitLower 2*finiteLower NineFeedbackStrength.originalH+
  RemainingHf.paidCells NineFeedbackStrength.originalH 3

theorem terminalFinite_le : terminalFinite ≤ terminalLower := by
  unfold terminalFinite terminalLower
  exact add_le_add (mul_le_mul_of_nonneg_right
    (RemainingHf.splitLower_le (by norm_num : (1:ℝ)≤2)) original_finiteLower_pos.le) le_rfl

end
end SigmaRemaining
