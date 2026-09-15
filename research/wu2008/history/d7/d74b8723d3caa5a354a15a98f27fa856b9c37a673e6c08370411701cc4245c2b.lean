import E02JointCreditStructure
import W03Table
import W02Transfer

noncomputable section
namespace WuTarget.E02JointCredit
open ActualNineFeedback NodeExtension DirectFiniteF6
open scoped BigOperators

def transferredDifference : Fin 21 → ℝ := matrixApply transferMatrix difference

theorem transferredDifference_nonneg (j : Fin 21) :
    0 ≤ transferredDifference j :=
  matrixApply_nonneg transferMatrix_nonneg difference_nonneg j

theorem transferredDifference_eq (j : Fin 21) :
    transferredDifference j =
      matrixApply transferMatrix W17Accepted.enhanced j -
        matrixApply transferMatrix W04Accepted.enhanced j := by
  simp only [transferredDifference, matrixApply, difference, mul_sub,
    Finset.sum_sub_distrib]

theorem jointCredit_eq_gamma :
    W17Accepted.jointCredit = Gamma transferredDifference 0 / 4 := by
  rw [W17Accepted.jointCredit_eq]
  unfold W01.lowGain
  simp_rw [W03.Gamma_eq_weights, transferredDifference_eq, mul_sub,
    Finset.sum_sub_distrib]

theorem jointCredit_eq_weights :
    W17Accepted.jointCredit =
      (∑ j : Fin 21, W03.weight j * transferredDifference j) / 4 := by
  rw [jointCredit_eq_gamma, W03.Gamma_eq_weights]

theorem paid_difference_lower :
    (∑ j : Fin 21, W03.paidWeights j * transferredDifference j) / 4 ≤
      W17Accepted.jointCredit := by
  rw [jointCredit_eq_gamma]
  exact div_le_div_of_nonneg_right
    (W03.paid_weights_consumer transferredDifference_nonneg) (by norm_num)

theorem rational_difference_lower :
    (∑ j : Fin 21, W03.paidWeights j *
      matrixApply W02.rationalMatrix difference j) / 4 ≤
        W17Accepted.jointCredit := by
  apply le_trans _ paid_difference_lower
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_left _ (W03.paidWeights_pos j).le
  exact Finset.sum_le_sum (fun k _ =>
    mul_le_mul_of_nonneg_right (W02.rationalMatrix_le_transferMatrix j k)
      (difference_nonneg k))

theorem first_transfer_paid : (1/2 : ℝ) ≤ transferMatrix 0 0 := by
  apply le_trans _ (W02.rationalMatrix_le_transferMatrix 0 0)
  have hs : 0 ≤ ∑ i ∈ W02.gridIndices 0,
      W02.paidNode i 0 * W02.logLower (rNode (i - 1)) (rNode i) := by
    apply Finset.sum_nonneg
    intro i hi
    apply mul_nonneg
    · exact W02.paidNode_nonneg (W02.grid_mem_bounds hi).1
        (W02.grid_mem_bounds hi).2 0
    · exact W02.logLower_nonneg (rNode_pos _) (rNode_mono (by omega))
  have he : nodeBasis (0 : Fin 9) 0 *
      W02.logLower (rNode ((0 : Fin 21).val + 1) - 1)
        (rNode (gridStart ((0 : Fin 21).val + 1))) = (1/2 : ℝ) := by
    norm_num [nodeBasis, W02.logLower, rNode, gridStart]
  unfold W02.rationalMatrix
  rw [he]
  exact le_add_of_nonneg_right hs

theorem first_difference_paid :
    (1/2 : ℝ) * (602223/1000000000000) ≤ transferredDifference 0 := by
  have hi : (602223/1000000000000 : ℝ) ≤ difference 0 := by
    simpa only [W09.increment, Matrix.cons_val_zero] using increment_le_difference 0
  calc
    (1/2 : ℝ) * (602223/1000000000000) ≤ transferMatrix 0 0 * difference 0 :=
      mul_le_mul first_transfer_paid hi (by norm_num)
        (transferMatrix_nonneg 0 0)
    _ ≤ transferredDifference 0 :=
      Finset.single_le_sum
        (fun k _ => mul_nonneg (transferMatrix_nonneg 0 k) (difference_nonneg k))
        (Finset.mem_univ (0 : Fin 9))

def amount : ℝ := 8508808767/793830625000000000

theorem amount_eq :
    amount = (904256/6350645 : ℝ) * (1/2) *
      (602223/1000000000000) / 4 := by
  norm_num [amount]

theorem amount_le_jointCredit : amount ≤ W17Accepted.jointCredit := by
  have hnode :
      (904256/6350645 : ℝ) * ((1/2) * (602223/1000000000000)) ≤
        W03.paidWeights 0 * transferredDifference 0 := by
    have h := mul_le_mul_of_nonneg_left first_difference_paid
      (W03.paidWeights_pos 0).le
    simpa only [W03.paidWeights, Matrix.cons_val_zero] using h
  have hsum : W03.paidWeights 0 * transferredDifference 0 ≤
      ∑ j : Fin 21, W03.paidWeights j * transferredDifference j :=
    Finset.single_le_sum
      (fun j _ => mul_nonneg (W03.paidWeights_pos j).le
        (transferredDifference_nonneg j)) (Finset.mem_univ (0 : Fin 21))
  rw [amount_eq]
  have hp := div_le_div_of_nonneg_right (hnode.trans hsum)
    (show (0 : ℝ) ≤ 4 by norm_num)
  apply le_trans _ paid_difference_lower
  simpa only [mul_assoc] using hp

theorem amount_gt_simple : (1/100000000 : ℝ) < amount := by
  norm_num [amount]

theorem jointCredit_pos : 0 < W17Accepted.jointCredit :=
  (lt_trans (by norm_num : (0 : ℝ) < 1/100000000) amount_gt_simple).trans_le
    amount_le_jointCredit

end WuTarget.E02JointCredit
