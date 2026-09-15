import WSrcNineGridInstance
import WSrcFifthGainSmallDelta

noncomputable section
namespace WuTarget.SourceFifthInstance
open Wu2008DoubleSieve SharpMassBalance NodeExtension Real

/-- Exact thirteen-cell amount for the concrete certified h profile; no decimal claim. -/
def amount : ℝ := WuSource.SrcFifthGain.gridGain SourceNodeInstance.h

theorem node_eq (i : ℕ) : WuSource.SrcFifthGain.node i = rNode i := by
  unfold WuSource.SrcFifthGain.node rNode
  ring

/-- The nine-node and full h-grid premises are discharged, not passed to the caller. -/
theorem actual_fifth_count {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (fifthPairFlin+amount-ε)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
        (fifthPairCount N : ℝ) := by
  apply WuSource.SrcFifthGain.grid_count_below WuSource.SrcNine.d_pos
    (h := SourceNodeInstance.h) ?_ ?_ hε
  · intro j hj
    exact SourceNodeInstance.lower_nonneg (by omega)
  · intro δ hδ _ hd j hj
    simpa only [node_eq] using
      (SourceNodeInstance.actual_tables hδ hd).2 (15+j) (by omega)

end WuTarget.SourceFifthInstance

set_option pp.fullNames true
set_option pp.explicit true
#check @WuTarget.SourceFifthInstance.actual_fifth_count
#print axioms WuTarget.SourceFifthInstance.actual_fifth_count
