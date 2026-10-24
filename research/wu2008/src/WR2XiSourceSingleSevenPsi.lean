import WR2SevenPair
import WR2XiSourceSingle

noncomputable section
namespace WuPaper.R2Seven
open Wu2008DoubleSieve WuSource.SrcSingle R2OmegaHigh

theorem single_fixed_count {δ ε : ℝ} (hd : 0 < δ) (hh : δ ≤ 1/100) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (singleClassical δ + lowSingleSource δ + psiSevenPaid - ε)*
        truncatedSixthMassScale N ≤ signedSingleCount N := by
  obtain ⟨T2, h2, hc2⟩ := second_source_actual_count hd hh (half_pos he)
  obtain ⟨T34, _, hc34⟩ := pair_integral_upper hd hh (half_pos he)
  refine ⟨max T2 T34, h2.trans (le_max_left _ _), fun N hN hEven => ?_⟩
  have h2N := hc2 N (by omega) hEven
  have h34N := hc34 N (by omega) hEven
  simp only [SingleUpperHIntegral.gainH34, windowGain_eq_fourthSource] at h34N
  unfold signedSingleCount singleClassical lowSingleSource
  linarith only [h2N, h34N]

end WuPaper.R2Seven

namespace WuPaper.R2Xi.SourceSingle
open Wu2008DoubleSieve Wu08TerminalAlignment WuSource.SrcSingle CandidateGrid R2OmegaHigh

theorem actual_single_count_with_seven_psi {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (secondMain-thirdMain-fourthMain+amount+psiSevenPaid-ε)*
        truncatedSixthMassScale N ≤ signedSingleCount N := by
  have he : 0 < ε/2 := by positivity
  obtain ⟨d, hd, _, htables⟩ := actual_tables
  obtain ⟨a, ha, hahi, hclass⟩ := classical_common_radius he
  let δ := min d a/2
  have hcap : 0 < min d a := lt_min hd ha
  have hδ : 0 < δ := half_pos hcap
  have hδcap : δ < min d a := half_lt_self hcap
  have hδd : δ ≤ d := hδcap.le.trans (min_le_left _ _)
  have hδa : δ < a := hδcap.trans_le (min_le_right _ _)
  have hδhi : δ ≤ 1/100 := hδa.le.trans hahi
  have ht := htables δ hδ hδd
  have hn : ∀ i ∈ Finset.Icc 14 29, 0 ≤ upper i := by
    intro i hi
    exact upper_nonneg (by have := (Finset.mem_Icc.mp hi).1; omega)
      (Finset.mem_Icc.mp hi).2
  have hH : ∀ i ∈ Finset.Icc 14 29,
      upper i ≤ wuImprovementLimit true δ (sourceNode i) := by
    intro i hi
    exact ht.1 i (by have := (Finset.mem_Icc.mp hi).1; omega)
      (Finset.mem_Icc.mp hi).2
  have hg : amount ≤ lowSingleSource δ := by
    have h2 := second_node_gain_to_source hδ hδhi
      (ht.2 22 (by norm_num)) (ht.1 12 (by norm_num) (by norm_num))
    have h4 := fourth_nodes_to_source hδ hδhi hn hH
    unfold amount lowSingleSource
    linarith only [h2, h4]
  have hc := hclass δ hδ hδa
  have hcoef : secondMain-thirdMain-fourthMain+amount+psiSevenPaid-ε ≤
      singleClassical δ+lowSingleSource δ+psiSevenPaid-ε/2 := by
    nlinarith only [hc, hg]
  obtain ⟨T, hT, hcount⟩ := R2Seven.single_fixed_count hδ hδhi he
  refine ⟨T, hT, fun N hN hEven => ?_⟩
  exact (mul_le_mul_of_nonneg_right hcoef
    (truncatedSixthClosure_scale_nonneg (hT.trans hN))).trans (hcount N hN hEven)

end WuPaper.R2Xi.SourceSingle
#print axioms WuPaper.R2Xi.SourceSingle.actual_single_count_with_seven_psi
