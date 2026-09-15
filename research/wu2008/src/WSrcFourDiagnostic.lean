import WSrcFourLowerAmount

noncomputable section
open Wu2008DoubleSieve FourRoughClosedMass Wu08OriginalFourWeights

namespace WuSource.SrcFour

theorem lowerAmount_56_exceeds_target : (13/20 : ℝ) < lowerAmount (14/25) := by
  norm_num [lowerAmount,weightFloor,lowerA,lowerB,Fin.sum_univ_succ,lowerCoeff,
    crossFloor,slopeFloor,FourLogAffine.l,SharpLogRecurrence.lowerLog,
    alpha,beta,lam,truncatedSixthLowerAlpha,truncatedSixthLowerBeta,truncatedSixthLowerLambda]

theorem original_pair_gt_target_of_lower
    (hl : ∀ u : ℝ, (3 : ℝ) ≤ u → (14/25 : ℝ) ≤ LiLiuPrereqBuchstab.buchstab u) :
    (13/20 : ℝ) < original10+original11 :=
  lowerAmount_56_exceeds_target.trans_le (original_pair_lowerAmount (by norm_num) hl)

theorem target_incompatible_with_lower
    (hl : ∀ u : ℝ, (3 : ℝ) ≤ u → (14/25 : ℝ) ≤ LiLiuPrereqBuchstab.buchstab u) :
    ¬ original10+original11 ≤ (13/20 : ℝ) :=
  not_le_of_gt (original_pair_gt_target_of_lower hl)

#check @lowerAmount_56_exceeds_target
#check @original_pair_gt_target_of_lower
#check @target_incompatible_with_lower
#print axioms lowerAmount_56_exceeds_target
#print axioms original_pair_gt_target_of_lower
#print axioms target_incompatible_with_lower
end WuSource.SrcFour
