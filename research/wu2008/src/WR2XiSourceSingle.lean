import WR2XiCandidateGrid
import WSrcSingleOriginalLedger

/-! The corrected candidate feeds the original single-prime signed source block. -/
noncomputable section
namespace WuPaper.R2Xi.SourceSingle
open Wu2008DoubleSieve NodeExtension WuSource.SrcSingle
open CandidateGrid
open scoped BigOperators

/-- The seven high-window Psi terms are kept separate from this low H/h payment. -/
def amount : ℝ := secondNodeGain (lower 22) (upper 12) + 2*fourthNodeSum upper

private theorem sourceNode_eq (i : ℕ) : sourceNode i = rNode i := by
  unfold sourceNode rNode
  ring

theorem actual_single_count {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (Wu08TerminalAlignment.secondMain-Wu08TerminalAlignment.thirdMain-
        Wu08TerminalAlignment.fourthMain+amount-ε)*truncatedSixthMassScale N ≤
          signedSingleCount N := by
  obtain ⟨d, hd, _, htables⟩ := actual_tables
  have hn : ∀ i ∈ Finset.Icc 14 29, 0 ≤ upper i := by
    intro i hi
    exact upper_nonneg
      (by have := (Finset.mem_Icc.mp hi).1; omega) (Finset.mem_Icc.mp hi).2
  have hs : ∀ δ : ℝ, 0 < δ → δ ≤ d → δ ≤ 1/100 →
      lower 22 ≤ wuImprovementLimit false δ (sourceNode 22) ∧
      upper 12 ≤ wuImprovementLimit true δ (sourceNode 12) ∧
      ∀ i ∈ Finset.Icc 14 29, upper i ≤ wuImprovementLimit true δ (sourceNode i) := by
    intro δ hδ hδd _
    have ht := htables δ hδ hδd
    simp only [sourceNode_eq]
    refine ⟨ht.2 22 (by norm_num), ht.1 12 (by norm_num) (by norm_num), ?_⟩
    intro i hi
    exact ht.1 i (by have := (Finset.mem_Icc.mp hi).1; omega) (Finset.mem_Icc.mp hi).2
  simpa only [amount, add_assoc] using original_log_Hh_input_to_count hd hn hs hε

end WuPaper.R2Xi.SourceSingle
#print axioms WuPaper.R2Xi.SourceSingle.actual_single_count
