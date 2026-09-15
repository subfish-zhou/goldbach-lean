import BaseHCount
import FifthHPositiveCount
import MathlibNt.Wu2008DoubleSieve.FifthPairPositiveAssembly

namespace Wu2008DoubleSieve.JointHPositive
open Real
open scoped Classical

/-- Rebuild all four positive terms from their actual producers. F1 has weight three;
F2, F5, F6 have weight one. Their internal deltas need not agree. -/
theorem first_second_fifth_sixth_actual_lower {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (24*wuLowerCoefficient (1/(2*truncatedSixthLowerAlpha)) +
        8*wuLowerCoefficient (1/(2*truncatedSixthLowerBeta)) +
        (8*BaseHGain.originalGain+fifthHGain) + fifthPairFlin +
        truncatedSixthLowerF6lin + 47/481250-ε)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
      3*(sieveCount N 1 N ((N : ℝ)^truncatedSixthLowerAlpha) : ℝ) +
        (sieveCount N 1 N ((N : ℝ)^truncatedSixthLowerBeta) : ℝ) +
        (fifthPairCount N : ℝ) +
        (truncatedSixthMass N ((N : ℝ)^truncatedSixthLowerAlpha)
          ((N : ℝ)^truncatedSixthLowerBeta) ((N : ℝ)^truncatedSixthLowerSigma)
          ((N : ℝ)^truncatedSixthLowerLambda) : ℝ) := by
  have heps : 0 < ε/6 := by positivity
  obtain ⟨T1,hT1,h1⟩ := BaseLowerCounts.actual_count_lower
    BaseLowerCounts.original_exponents.1 BaseLowerCounts.original_exponents.2.1 heps
  obtain ⟨T2,_,h2⟩ := BaseHGain.original_F2_actual_count heps
  obtain ⟨T5,_,h5⟩ := fifthH_actual_improved_lower heps
  obtain ⟨T6,_,h6⟩ := TruncatedSixthSmallDeltaGain.actual_count_lower heps
  refine ⟨max T1 (max T2 (max T5 T6)),hT1.trans (le_max_left _ _),?_⟩
  intro N hN he
  have hN1 := (le_max_left T1 (max T2 (max T5 T6))).trans hN
  have hN256 := (le_max_right T1 (max T2 (max T5 T6))).trans hN
  have hN2 := (le_max_left T2 (max T5 T6)).trans hN256
  have hN56 := (le_max_right T2 (max T5 T6)).trans hN256
  have hN5 := (le_max_left T5 T6).trans hN56
  have hN6 := (le_max_right T5 T6).trans hN56
  have ha := h1 N hN1 he
  have hb := h2 N hN2 he
  have hc := h5 N hN5 he
  have hd := h6 N hN6 he
  change ((8*wuLowerCoefficient (1/(2*truncatedSixthLowerBeta))+
    8*BaseHGain.originalGain)-ε/6)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
    (sieveCount N 1 N ((N : ℝ)^truncatedSixthLowerBeta) : ℝ) at hb
  ring_nf at ha hb hc hd ⊢
  linarith only [ha,hb,hc,hd]

end Wu2008DoubleSieve.JointHPositive
