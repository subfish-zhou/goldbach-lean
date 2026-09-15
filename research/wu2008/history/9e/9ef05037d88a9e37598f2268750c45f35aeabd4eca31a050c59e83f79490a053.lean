import WSrcFourBuchstabBridge
import WSrcBuchstabLowerRoot

noncomputable section
namespace WuSource.FourBudgetVerified
open Wu2008DoubleSieve Wu08OriginalFourWeights FourRoughClosedMass

theorem source_parameters : alpha = (100/1327 : ℝ) ∧ beta = (25/206 : ℝ) ∧
    lam = 1/2-2*(100/1327 : ℝ) := by
  norm_num [alpha,beta,lam,truncatedSixthLowerAlpha,truncatedSixthLowerBeta,
    truncatedSixthLowerLambda]

theorem actual_pair_lower : SrcFour.lowerAmount (14/25) ≤ original10+original11 :=
  SrcFour.original_pair_lowerAmount (by norm_num) SrcBuchstabLower.buchstab_lower56

theorem actual_pair_gt_065 : (13/20 : ℝ) < original10+original11 :=
  SrcFour.original_pair_gt_target_of_lower SrcBuchstabLower.buchstab_lower56

theorem target_065_impossible : ¬ original10+original11 ≤ (13/20 : ℝ) :=
  not_le_of_gt actual_pair_gt_065

/-- Comparison with the two literal numbers only, not a refutation of Wu's theorem. -/
theorem printed_pair_cannot_both_be_upper :
    ¬ (original10 ≤ (104305/1000000 : ℝ) ∧
      original11 ≤ (543858/1000000 : ℝ)) := by
  rintro ⟨h10,h11⟩
  linarith only [actual_pair_gt_065,h10,h11]

theorem actual_pair_bracket : (13/20 : ℝ) < original10+original11 ∧
    original10+original11 < (86/125 : ℝ) :=
  ⟨actual_pair_gt_065,FourBuchstabAccepted.original_pair_lt_688⟩

end WuSource.FourBudgetVerified
