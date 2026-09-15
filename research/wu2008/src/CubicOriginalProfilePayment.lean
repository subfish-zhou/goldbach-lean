import CubicCommonProfile

namespace CubicCommonProfile
open Real NodeExtension FirstFeedbackIntegrals OriginalSigmaStrength OriginalSigmaCubicRestoration
open Wu04WholeCollection Wu2008DoubleSieve Wu04FactorEnvelopes SharpLogRecurrence JointLogTotalComparison
open scoped BigOperators
noncomputable section

theorem original_cubicPaidNumerator_pos : 0<cubicPaidNumerator NineFeedbackStrength.originalH := by
  simp only [cubicPaidNumerator,Fin.sum_univ_succ]
  dsimp [NineFeedbackStrength.originalH]
  norm_num [cubicCellPaid,poleCellPaid,upperNode,upperLeft,signedLow,
    low,up,lower,upper,leftFactor,rightFactor,lowerLog,upperLog,V]

theorem original_fullNumerator_pos : 0<fullNumerator NineFeedbackStrength.originalH :=
  add_pos RetainedCommonProfile.original_paidNumerator_pos original_cubicPaidNumerator_pos

theorem original_finiteLower : finiteLower NineFeedbackStrength.originalH ≤
    aProfile (nineProfile NineFeedbackStrength.originalH) :=
  finiteLower_le_profile CoupledIntegralRecovery.originalH_nonneg original_fullNumerator_pos.le

end
end CubicCommonProfile
