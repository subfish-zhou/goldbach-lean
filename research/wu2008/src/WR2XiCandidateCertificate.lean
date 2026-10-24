import WR2XiConditionalCertificate
import W06SigmaV2

/-! Discharge the common sigma premise once for the complete corrected matrix. -/
noncomputable section
namespace WuPaper.R2Xi.RationalCandidate
open NodeExtension ActualNineFeedback

private theorem sigmaCoeff_cast (k : Fin 9) :
    (Xi2RationalTop.sigmaCoeff k : ℝ) = WuTarget.W06.sigmaCoeff k := by
  fin_cases k <;> norm_num [Xi2RationalTop.sigmaCoeff, Xi2RationalTop.massLower,
    WuTarget.W06.sigmaCoeff, WuTarget.W06.massLower, WuTarget.W06.denominatorLower]

theorem candidate_entry_bounds (i k : Fin 9) : lowerMatrix i k ≤ correctedNineMatrix i k := by
  apply candidate_entries_of_sigma (fun k => ?_) i k
  rw [sigmaCoeff_cast]
  exact WuTarget.W06.sigmaCoeff_le_aProfile k

theorem candidate_actual_lower :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1/10 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d →
      ∀ i, lowerH i ≤ actualNine δ i :=
  actual_lower_of_entry_bounds candidate_entry_bounds

theorem candidate_actual_nodes :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1/10 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d →
      (∀ i, lowerH i ≤ actualNine δ i) ∧
      (∀ j : Fin 21, matrixApply transferMatrix lowerH j ≤
        Wu2008DoubleSieve.wuImprovementLimit false δ (rNode (j.val+1))) :=
  candidate_nodes_of_entry_bounds candidate_entry_bounds

end WuPaper.R2Xi.RationalCandidate
#print axioms WuPaper.R2Xi.RationalCandidate.candidate_actual_lower
#print axioms WuPaper.R2Xi.RationalCandidate.candidate_actual_nodes
