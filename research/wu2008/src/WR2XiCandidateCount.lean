import WR2XiCandidateBaseCount
import WR2XiContinuousMonotone
import W17AcceptedCount

/-! Feed the corrected candidate into the actual continuous ordinary-P2 count. -/
noncomputable section
namespace WuPaper.R2Xi.CandidateCount
open Wu2008DoubleSieve NodeExtension ActualNineFeedback
open WuTarget.W01Continuous

def nodes (i : Fin 9) : ℝ := max (WuTarget.W17Accepted.enhanced i) (RationalCandidate.lowerH i)

theorem old_le_nodes (i : Fin 9) : WuTarget.W17Accepted.enhanced i ≤ nodes i := le_max_left _ _
theorem candidate_le_nodes (i : Fin 9) : RationalCandidate.lowerH i ≤ nodes i := le_max_right _ _
theorem nodes_nonneg (i : Fin 9) : 0 ≤ nodes i :=
  (RationalCandidate.lowerH_nonneg i).trans (candidate_le_nodes i)

theorem nodes_actual : ∃ d : ℝ, 0 < d ∧ d ≤ 1/10 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ d → ∀ i, nodes i ≤ actualNine δ i := by
  obtain ⟨a, ha, hcap, hold⟩ := WuTarget.W17Accepted.enhanced_actual
  obtain ⟨b, hb, _, hnew⟩ := RationalCandidate.candidate_actual_lower
  refine ⟨min a b, lt_min ha hb, (min_le_left _ _).trans hcap, ?_⟩
  intro δ hδ hd i
  exact max_le (hold δ hδ (hd.trans (min_le_left _ _)) i)
    (hnew δ hδ (hd.trans (min_le_right _ _)) i)

def coefficient : ℝ := continuousCoefficient nodes

theorem old_coefficient_le : continuousCoefficient WuTarget.W17Accepted.enhanced ≤ coefficient :=
  continuousCoefficient_mono WuTarget.W17Accepted.enhanced_nonneg old_le_nodes

theorem candidate_coefficient_le : CandidateBaseCount.coefficient ≤ coefficient :=
  continuousCoefficient_mono RationalCandidate.lowerH_nonneg candidate_le_nodes

theorem ordinary_count {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (coefficient-ε)*U8CanonicalMother.M N ≤
        ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
          ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) := by
  obtain ⟨d, hd, _, hnodes⟩ := nodes_actual
  obtain ⟨δ, _, _, _, _, T, hT, hcount⟩ :=
    continuous_ordinary_P2 nodes_nonneg hd hnodes hε (by norm_num : (0:ℝ)<1)
  exact ⟨T, hT, hcount⟩

end WuPaper.R2Xi.CandidateCount
#print axioms WuPaper.R2Xi.CandidateCount.ordinary_count
