import SigmaExistingCellsPositive

namespace SigmaExistingLogError
open Real NodeExtension FirstFeedbackIntegrals OriginalSigmaStrength
open Wu04WholeCollection Wu2008DoubleSieve Wu04FactorEnvelopes SharpLogRecurrence JointLogTotalComparison
open scoped BigOperators
noncomputable section

theorem original_paidNumerator_pos : 0<paidNumerator NineFeedbackStrength.originalH := by
  have h0 := original_cell_0_pos
  have h1 := original_cell_1_pos
  have h2 := original_cell_2_pos
  have h3 := original_cell_3_pos
  have h4 := original_cell_4_pos
  have h5 := original_cell_5_pos
  have h6 := original_cell_6_pos
  have h7 := original_cell_7_pos
  have h8 := original_cell_8_pos
  simp only [paidNumerator,Fin.sum_univ_succ]
  dsimp [NineFeedbackStrength.originalH]
  positivity

theorem original_finiteLower : finiteLower NineFeedbackStrength.originalH ≤
    aProfile (nineProfile NineFeedbackStrength.originalH) :=
  finiteLower_le_profile CoupledIntegralRecovery.originalH_nonneg original_paidNumerator_pos.le

end
end SigmaExistingLogError
