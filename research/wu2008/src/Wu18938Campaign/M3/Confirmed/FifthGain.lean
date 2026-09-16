import Wu18938Campaign.M3.Confirmed.FifthGainTransfer
import WSrcFifthAnalyticInstance
import Wu18938Campaign.M3.Confirmed.AnalyticAssembly

noncomputable section

namespace Wu18938Campaign.M3.Confirmed

open Real Wu2008DoubleSieve Wu08TerminalAlignment WuTarget
open FifthGainNodes

theorem source_vector_eq : sourceVector = WuSource.SrcNine.z := rfl

theorem fifth_source_lower_nodes (k : Fin 13) :
    transferFloor k ≤ SourceNodeInstance.h (15+k) := by
  rw [SourceNodeInstance.h,← source_vector_eq]
  exact transferred_lower_nodes k

theorem fifth_rounded_gain_lower :
    (10959/10000000:ℝ) ≤ SourceFifthAnalyticInstance.roundedAmount := by
  have h0 := fifth_source_lower_nodes 0
  have h1 := fifth_source_lower_nodes 1
  have h2 := fifth_source_lower_nodes 2
  have h3 := fifth_source_lower_nodes 3
  have h4 := fifth_source_lower_nodes 4
  have h5 := fifth_source_lower_nodes 5
  have h6 := fifth_source_lower_nodes 6
  have h7 := fifth_source_lower_nodes 7
  have h8 := fifth_source_lower_nodes 8
  have h9 := fifth_source_lower_nodes 9
  have h10 := fifth_source_lower_nodes 10
  have h11 := fifth_source_lower_nodes 11
  have h12 := fifth_source_lower_nodes 12
  norm_num [transferFloor] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  rw [SourceFifthAnalyticInstance.roundedAmount,
    WuSource.SrcFifthGain.Analytic.rational_gain_literal]
  linarith only [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12]

theorem fifth_actual_gain_lower :
    (10959/10000000:ℝ) ≤ SourceFifthAnalyticInstance.amount :=
  fifth_rounded_gain_lower.trans SourceFifthAnalyticInstance.gain_sandwich.1

theorem fifth_actual_gain_sufficient :
    (108734/100000000:ℝ) < SourceFifthAnalyticInstance.amount :=
  lt_of_lt_of_le (by norm_num) fifth_actual_gain_lower

theorem fifth_actual_count_paid {ε : ℝ} (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (fifthMain+10959/10000000-ε)*truncatedSixthMassScale N ≤
        (fifthPairCount N : ℝ) := by
  obtain ⟨T,hT,h⟩ := SourceFifthAnalyticInstance.actual_fifth_count he
  refine ⟨T,hT,fun N hN hEven => ?_⟩
  have hn := h N hN hEven
  change (fifthMain+SourceFifthAnalyticInstance.amount-ε)*
    wuSingularSeries N*N/log N^(2:ℕ) ≤ _ at hn
  have hc := mul_le_mul_of_nonneg_right
    (show fifthMain+10959/10000000-ε ≤
      fifthMain+SourceFifthAnalyticInstance.amount-ε by
      linarith only [fifth_actual_gain_lower])
    (truncatedSixthClosure_scale_nonneg (hT.trans hN))
  exact hc.trans (by convert hn using 1 <;> unfold truncatedSixthMassScale <;> ring)

end Wu18938Campaign.M3.Confirmed
