import WE02JointCreditRoot
import W02Certified

noncomputable section
namespace WuTarget.E02JointCredit
open Wu2008DoubleSieve ActualNineFeedback NodeExtension
open scoped BigOperators

def rankOneSigmaMass : ℝ := W06.sigmaLower Wu04Bypass.v8

def rankOneRows (i : Fin 9) : ℝ :=
  W09.increment i + W17Joint.rowWeightLower i * rankOneSigmaMass

theorem rankOneSigmaMass_nonneg : 0 ≤ rankOneSigmaMass :=
  W06.sigmaLower_nonneg Wu04Bypass.v8_nonneg

theorem rankOneRows_nonneg (i : Fin 9) : 0 ≤ rankOneRows i :=
  add_nonneg (increment_nonneg i)
    (mul_nonneg (W17Joint.rowWeightLower_bounds i).1 rankOneSigmaMass_nonneg)

theorem sigma_le_addedMatrix (i k : Fin 9) :
    W17Joint.rationalSigmaMatrix i k ≤ addedMatrix i k := by
  have hm := (W04.oldMatrix_le_elementary i k).trans
    (W08.elementaryMatrix_le_paidMatrix i k)
  have hj := W05.jTable_nonneg i k
  have hd := W07.paidMatrix_nonneg i k
  unfold addedMatrix W04.augmentedMatrix W17Joint.jointMatrix W17Joint.remainderMatrix
  linarith only [hm, hj, hd]

theorem rankOne_apply (i : Fin 9) :
    matrixApply W17Joint.rationalSigmaMatrix Wu04Bypass.v8 i =
      W17Joint.rowWeightLower i * rankOneSigmaMass := by
  simp only [matrixApply, W17Joint.rationalSigmaMatrix, rankOneSigmaMass,
    W06.sigmaLower, mul_assoc, Finset.mul_sum]

theorem rankOneRows_le_difference (i : Fin 9) : rankOneRows i ≤ difference i := by
  have hm : matrixApply W17Joint.rationalSigmaMatrix Wu04Bypass.v8 i ≤
      matrixApply addedMatrix Wu04Bypass.v8 i :=
    Finset.sum_le_sum (fun k _ =>
      mul_le_mul_of_nonneg_right (sigma_le_addedMatrix i k) (Wu04Bypass.v8_nonneg k))
  rw [rankOne_apply] at hm
  have hn := (difference_remainders_nonneg i).1
  rw [difference_eq]
  unfold rankOneRows
  linarith only [hm, hn]

theorem rankOne_remainder_eq (i : Fin 9) :
    difference i - rankOneRows i =
      matrixApply W17Joint.jointMatrix
        (fun k => W04Accepted.enhanced k - Wu04Bypass.v8 k) i +
      matrixApply (fun j k => addedMatrix j k - W17Joint.rationalSigmaMatrix j k)
        Wu04Bypass.v8 i := by
  rw [difference_eq]
  unfold rankOneRows
  rw [← rankOne_apply]
  simp only [matrixApply, sub_mul, Finset.sum_sub_distrib]
  ring

theorem rankOne_remainder_nonneg (i : Fin 9) : 0 ≤ difference i - rankOneRows i :=
  sub_nonneg.mpr (rankOneRows_le_difference i)

theorem rankOne_rational_payment :
    (∑ j : Fin 21, W03.paidWeights j *
      matrixApply W02.rationalMatrix rankOneRows j) / 4 ≤ W17Accepted.jointCredit := by
  apply le_trans _ rational_difference_lower
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact Finset.sum_le_sum (fun j _ =>
    mul_le_mul_of_nonneg_left
      (matrixApply_mono W02.rationalMatrix_nonneg rankOneRows_le_difference j)
      (W03.paidWeights_pos j).le)

#print SecondFunctionalParameters.row1
#print SecondFunctionalParameters.row2
#print SecondFunctionalParameters.row3
#print SecondFunctionalParameters.row4

end WuTarget.E02JointCredit
