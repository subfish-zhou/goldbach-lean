import WE02JointCreditRankOneNodes

noncomputable section
namespace WuTarget.E02JointCredit
open ActualNineFeedback NodeExtension
open scoped BigOperators

def rankOneWeightedPayment : ℝ :=
  (∑ j : Fin 21, W03.paidWeights j * (rankOneTransferLower j : ℝ)) / 4

theorem rankOneWeightedPayment_le :
    rankOneWeightedPayment ≤ W17Accepted.jointCredit := by
  apply le_trans _ rational_difference_lower
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact Finset.sum_le_sum (fun j _ =>
    mul_le_mul_of_nonneg_left (rankOneTransferLower_le_rational j)
      (W03.paidWeights_pos j).le)

def rankOneAmount : ℝ := 91/500000

theorem rankOneAmount_paid : rankOneAmount ≤ rankOneWeightedPayment := by
  norm_num [rankOneAmount, rankOneWeightedPayment, W03.paidWeights,
    rankOneTransferLower, Fin.sum_univ_succ]

theorem rankOneAmount_le_jointCredit : rankOneAmount ≤ W17Accepted.jointCredit :=
  rankOneAmount_paid.trans rankOneWeightedPayment_le

theorem rankOneAmount_improves_old : 16000 * amount < rankOneAmount := by
  norm_num [rankOneAmount, amount]

theorem rankOneAmount_preserves_old : amount < rankOneAmount := by
  norm_num [rankOneAmount, amount]

def rankOneUpgrade : ℝ := rankOneAmount - amount

theorem rankOneUpgrade_pos : 0 < rankOneUpgrade :=
  sub_pos.mpr rankOneAmount_preserves_old

theorem rankOneUpgrade_lower : (9/50000 : ℝ) < rankOneUpgrade := by
  norm_num [rankOneUpgrade, rankOneAmount, amount]

theorem rankOneUpgrade_paid :
    amount + rankOneUpgrade ≤ W17Accepted.jointCredit := by
  simpa only [rankOneUpgrade, add_sub_cancel] using rankOneAmount_le_jointCredit

theorem rankOne_net_identity :
    W17Accepted.jointCredit =
      amount + rankOneUpgrade + (W17Accepted.jointCredit - rankOneAmount) := by
  unfold rankOneUpgrade
  ring

theorem rankOne_net_remainder_nonneg :
    0 ≤ W17Accepted.jointCredit - rankOneAmount :=
  sub_nonneg.mpr rankOneAmount_le_jointCredit

end WuTarget.E02JointCredit
