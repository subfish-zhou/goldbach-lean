import WSrcNineGridInstance
import WSrcSingleCount

noncomputable section
namespace WuTarget.SourceSingleInstance
open Wu2008DoubleSieve NodeExtension Real Set MeasureTheory

/-- Low H/h gain only; the seven high-window Psi gains are not included. -/
def amount : ℝ :=
  8*WuSource.SrcSingle.secondTransfer (SourceNodeInstance.h 22)
    (fun _ => SourceNodeInstance.H 12) +
    2*WuSource.SrcSingle.fourthNodeSum SourceNodeInstance.H

theorem node_eq (i : ℕ) : WuSource.SrcSingle.sourceNode i = rNode i := by
  unfold WuSource.SrcSingle.sourceNode rNode
  ring

theorem small_profile_integrable :
    IntervalIntegrable (fun t : ℝ => SourceNodeInstance.H 12/t) volume
      (78/25) (16/5) := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le (by norm_num : (78/25 : ℝ) ≤ 16/5)]
  exact continuousOn_const.div continuousOn_id
    (fun t ht => ne_of_gt (lt_of_lt_of_le (by norm_num) ht.1))

theorem actual_single_count {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (Wu08TerminalAlignment.secondMain-Wu08TerminalAlignment.thirdMain-
        Wu08TerminalAlignment.fourthMain+amount-ε)*truncatedSixthMassScale N ≤
          WuSource.SrcSingle.signedSingleCount N := by
  simpa only [amount, add_assoc] using
    (WuSource.SrcSingle.original_Hh_input_to_count WuSource.SrcNine.d_pos
      small_profile_integrable (Hnodes := SourceNodeInstance.H)
      (h22 := SourceNodeInstance.h 22) ?_ ?_ hε)
  · intro i hi
    exact SourceNodeInstance.upper_nonneg (by have := (Finset.mem_Icc.mp hi).1; omega)
      (Finset.mem_Icc.mp hi).2
  · intro δ hδ hr _
    have htable := SourceNodeInstance.actual_tables hδ hr
    refine ⟨?_, ?_, ?_⟩
    · simpa only [rNode] using htable.2 22 (by norm_num)
    · intro t ht
      have hu := htable.1 12 (by norm_num) (by norm_num)
      apply hu.trans
      apply wuImprovementLimit_upper_antitone hδ (hr.trans WuSource.SrcNine.d_cap)
      · constructor <;> linarith [ht.1,ht.2]
      · norm_num [rNode]
      · norm_num [rNode] at *
        linarith [ht.2]
    · intro i hi
      simpa only [node_eq] using htable.1 i
        (by have := (Finset.mem_Icc.mp hi).1; omega) (Finset.mem_Icc.mp hi).2

end WuTarget.SourceSingleInstance

#check @WuTarget.SourceSingleInstance.actual_single_count
#print axioms WuTarget.SourceSingleInstance.actual_single_count
