import WR2XiCandidateCertificate
import W01ContinuousCount

/-! The corrected candidate alone supplies an actual ordinary-P2 count. -/
noncomputable section
namespace WuPaper.R2Xi.CandidateBaseCount
open WuTarget.W01Continuous

def coefficient : ℝ := continuousCoefficient RationalCandidate.lowerH

theorem ordinary_count {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (coefficient-ε)*U8CanonicalMother.M N ≤
        ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
          ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) := by
  obtain ⟨d, hd, _, hnodes⟩ := RationalCandidate.candidate_actual_lower
  obtain ⟨δ, _, _, _, _, T, hT, hcount⟩ :=
    continuous_ordinary_P2 RationalCandidate.lowerH_nonneg hd hnodes hε
      (by norm_num : (0:ℝ)<1)
  exact ⟨T, hT, hcount⟩

end WuPaper.R2Xi.CandidateBaseCount
#print axioms WuPaper.R2Xi.CandidateBaseCount.ordinary_count
