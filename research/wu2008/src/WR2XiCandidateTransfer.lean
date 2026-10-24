import WR2XiRationalCandidate
import NodeTransfer

/-! Transfer the corrected nine-node subsolution to the twenty-one actual lower nodes. -/
noncomputable section
namespace WuPaper.R2Xi.RationalCandidate
open Wu2008DoubleSieve NodeExtension ActualNineFeedback

/-- The same delta interval controls both the upper and lower node vectors. -/
theorem candidate_nodes_of_entry_bounds
    (hentry : ∀ i k, lowerMatrix i k ≤ correctedNineMatrix i k) :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1/10 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d →
      (∀ i, lowerH i ≤ actualNine δ i) ∧
      (∀ j : Fin 21, matrixApply transferMatrix lowerH j ≤
        wuImprovementLimit false δ (rNode (j.val+1))) := by
  obtain ⟨d, hd, hcap, hnodes⟩ := actual_lower_of_entry_bounds hentry
  refine ⟨d, hd, hcap, ?_⟩
  intro δ hδ hδd
  have hx := hnodes δ hδ hδd
  refine ⟨hx, ?_⟩
  intro j
  exact (matrixApply_mono transferMatrix_nonneg hx j).trans
    (actual_twentyone_matrix hδ (hδd.trans hcap) j)

end WuPaper.R2Xi.RationalCandidate
#print axioms WuPaper.R2Xi.RationalCandidate.candidate_nodes_of_entry_bounds
