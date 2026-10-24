import WR2XiCandidateCertificate
import WSrcGridTables

/-! One common small-parameter radius for the candidate's complete source grid. -/
noncomputable section
namespace WuPaper.R2Xi.CandidateGrid
open Wu2008DoubleSieve NodeExtension

def upper (i : ℕ) : ℝ := extendedNode RationalCandidate.lowerH i
def lower (j : ℕ) : ℝ := originalTransfer RationalCandidate.lowerH j

theorem upper_nonneg {i : ℕ} (hi : 2 ≤ i) (hi29 : i ≤ 29) : 0 ≤ upper i :=
  extendedNode_nonneg RationalCandidate.lowerH_nonneg hi hi29

theorem lower_nonneg {j : ℕ} (hj : j ≤ 29) : 0 ≤ lower j :=
  WuSource.SrcGrid.originalTransfer_nonneg_all RationalCandidate.lowerH_nonneg hj

theorem actual_tables : ∃ d : ℝ, 0 < d ∧ d ≤ 1/10 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ d →
      (∀ i : ℕ, 2 ≤ i → i ≤ 29 → upper i ≤ wuImprovementLimit true δ (rNode i)) ∧
      (∀ j : ℕ, j ≤ 29 → lower j ≤ wuImprovementLimit false δ (rNode j)) := by
  obtain ⟨d, hd, hcap, hnodes⟩ := RationalCandidate.candidate_actual_lower
  exact ⟨d, hd, hcap, fun δ hδ hδd =>
    WuSource.SrcGrid.full_tables_lower hδ (hδd.trans hcap) (hnodes δ hδ hδd)⟩

end WuPaper.R2Xi.CandidateGrid
#print axioms WuPaper.R2Xi.CandidateGrid.actual_tables
