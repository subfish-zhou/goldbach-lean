import WR2XiSourceSingleSevenPsi
import WR2XiSourceFifth

noncomputable section
namespace WuPaper.R2Xi.SourceBlock
open Wu2008DoubleSieve Wu08TerminalAlignment WuSource.SrcSingle

def coefficient : ℝ := 3*firstMain+secondMain-thirdMain-fourthMain+
  SourceSingle.amount+WuSource.SrcSingle.psiSevenPaid+fifthMain+SourceFifth.amount

theorem actual_count {ε : ℝ} (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (coefficient-ε)*truncatedSixthMassScale N ≤
        3*(sieveCount N 1 N ((N : ℝ)^truncatedSixthLowerAlpha) : ℝ)+
          signedSingleCount N+(fifthPairCount N : ℝ) := by
  have he5 : 0 < ε/5 := by positivity
  obtain ⟨T1,hT1,h1⟩ := first_actual_count he5
  obtain ⟨T2,_,h2⟩ := SourceSingle.actual_single_count_with_seven_psi he5
  obtain ⟨T5,_,h5⟩ := SourceFifth.actual_fifth_count he5
  refine ⟨max T1 (max T2 T5), by omega, fun N hN hEven => ?_⟩
  have ha := h1 N (by omega) hEven
  have hb := h2 N (by omega) hEven
  have hc := h5 N (by omega) hEven
  unfold coefficient fifthMain truncatedSixthMassScale at *
  ring_nf at ha hb hc ⊢
  linarith only [ha,hb,hc]

end WuPaper.R2Xi.SourceBlock
#print axioms WuPaper.R2Xi.SourceBlock.actual_count
