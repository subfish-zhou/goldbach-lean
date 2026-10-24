import WR2XiCandidateGrid
import WSrcFifthGainSmallDelta

/-! Feed the corrected candidate into the original thirteen-cell fifth count. -/
noncomputable section
namespace WuPaper.R2Xi.SourceFifth
open Wu2008DoubleSieve NodeExtension Real
open CandidateGrid

def amount : ℝ := WuSource.SrcFifthGain.gridGain lower

private theorem node_eq (i : ℕ) : WuSource.SrcFifthGain.node i = rNode i := by
  unfold WuSource.SrcFifthGain.node rNode
  ring

theorem actual_fifth_count {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (fifthPairFlin+amount-ε)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
        (fifthPairCount N : ℝ) := by
  obtain ⟨d, hd, _, htables⟩ := actual_tables
  apply WuSource.SrcFifthGain.grid_count_below hd (h := lower) ?_ ?_ hε
  · intro j hj
    exact lower_nonneg (by omega)
  · intro δ hδ _ hδd j hj
    have ht := htables δ hδ hδd
    simpa only [node_eq] using ht.2 (15+j) (by omega)

end WuPaper.R2Xi.SourceFifth
#print axioms WuPaper.R2Xi.SourceFifth.actual_fifth_count
