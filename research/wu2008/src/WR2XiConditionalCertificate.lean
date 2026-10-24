import WR2XiTerminalConditional
import WR2XiFirstConditional
import WR2XiSecondCertificate
import WR2XiCandidateTransfer

/-! All corrected matrix entries share only the same nine sigma lower bounds. -/
noncomputable section
namespace WuPaper.R2Xi.RationalCandidate
open NodeExtension ActualNineFeedback

theorem candidate_entries_of_sigma
    (hsigma : ∀ k, (Xi2RationalTop.sigmaCoeff k : ℝ) ≤ aProfile (nineProfile (nodeBasis k)))
    (i k : Fin 9) : lowerMatrix i k ≤ correctedNineMatrix i k := by
  refine Fin.addCases (m := 4) (n := 5) (fun r => ?_) (fun j => ?_) i
  · exact second_functional_entries r k (hsigma k)
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · exact terminal_entries_of_sigma k (hsigma k)
    · exact first_four_entries_of_sigma j k (hsigma k)

theorem candidate_nodes_of_sigma
    (hsigma : ∀ k, (Xi2RationalTop.sigmaCoeff k : ℝ) ≤ aProfile (nineProfile (nodeBasis k))) :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1/10 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d →
      (∀ i, lowerH i ≤ actualNine δ i) ∧
      (∀ j : Fin 21, matrixApply transferMatrix lowerH j ≤
        Wu2008DoubleSieve.wuImprovementLimit false δ (rNode (j.val+1))) :=
  candidate_nodes_of_entry_bounds (candidate_entries_of_sigma hsigma)

end WuPaper.R2Xi.RationalCandidate
#print axioms WuPaper.R2Xi.RationalCandidate.candidate_nodes_of_sigma
