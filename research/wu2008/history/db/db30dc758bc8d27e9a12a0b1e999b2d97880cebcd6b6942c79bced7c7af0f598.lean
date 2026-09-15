import WSrcFifthGridInstance
import WSrcFifthGainAnalyticRoot

noncomputable section
namespace WuTarget.SourceFifthAnalyticInstance
open Wu2008DoubleSieve SharpMassBalance NodeExtension Real

def amount : ℝ := WuSource.SrcFifthGain.Analytic.massGain SourceNodeInstance.h
def roundedAmount : ℝ := WuSource.SrcFifthGain.Analytic.rationalGain SourceNodeInstance.h

theorem gain_sandwich : roundedAmount ≤ amount ∧ amount ≤ SourceFifthInstance.amount :=
  ⟨WuSource.SrcFifthGain.Analytic.rational_gain_le_mass
      (fun j hj => SourceNodeInstance.lower_nonneg (by omega)),
    WuSource.SrcFifthGain.Analytic.mass_gain_le_grid
      (fun j hj => SourceNodeInstance.lower_nonneg (by omega))⟩

/-- All h-node and thirteen weight hypotheses are discharged. -/
theorem actual_fifth_count {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (fifthPairFlin+amount-ε)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
        (fifthPairCount N : ℝ) := by
  apply WuSource.SrcFifthGain.Analytic.mass_gain_count WuSource.SrcNine.d_pos
    (h := SourceNodeInstance.h) ?_ ?_ hε
  · intro j hj
    exact SourceNodeInstance.lower_nonneg (by omega)
  · intro δ hδ _ hd j hj
    simpa only [SourceFifthInstance.node_eq] using
      (SourceNodeInstance.actual_tables hδ hd).2 (15+j) (by omega)

end WuTarget.SourceFifthAnalyticInstance

#check @WuTarget.SourceFifthAnalyticInstance.gain_sandwich
#check @WuTarget.SourceFifthAnalyticInstance.actual_fifth_count
#print axioms WuTarget.SourceFifthAnalyticInstance.gain_sandwich
#print axioms WuTarget.SourceFifthAnalyticInstance.actual_fifth_count
