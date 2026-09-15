import RetainedCommonProfile

namespace RetainedCommonProfile
open Real NodeExtension FirstFeedbackIntegrals OriginalSigmaStrength Wu04WholeCollection
open Wu2008DoubleSieve Wu04FactorEnvelopes SharpLogRecurrence JointLogTotalComparison
open scoped BigOperators
noncomputable section

/-- The sign is paid for the original data before weakening the actual denominator. -/
theorem original_paidNumerator_pos : 0<paidNumerator NineFeedbackStrength.originalH := by
  simp only [paidNumerator, Fin.sum_univ_succ]
  dsimp [NineFeedbackStrength.originalH]
  norm_num [retainedCellPaid,poleCellPaid,upperNode,upperLeft,signedLow,
    low,up,lower,upper,leftFactor,rightFactor,lowerLog,upperLog,V]

/-- Finite, unconditional payment for the genuine common profile of the author's H. -/
theorem original_finiteLower : finiteLower NineFeedbackStrength.originalH ≤
    aProfile (nineProfile NineFeedbackStrength.originalH) :=
  finiteLower_le_profile CoupledIntegralRecovery.originalH_nonneg original_paidNumerator_pos.le

end
end RetainedCommonProfile
