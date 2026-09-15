import MathlibNt.Wu2008DoubleSieve.TruncatedSixthTableComparison

/-!
# Actual truncated-sixth counts with the nine explicit coefficients
-/

namespace Wu2008DoubleSieve

open Real
open scoped Classical BigOperators

theorem truncatedSixthTable_fixed_delta_count {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 100) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (truncatedSixthLowerFdelta δ +
        (∑ j : Fin 9, truncatedSixthTableBeta δ j * tableFeedbackActualVector δ j) - ε) *
        wuSingularSeries N * N / log N ^ (2 : ℕ) ≤
      (truncatedSixthMass N ((N : ℝ) ^ truncatedSixthLowerAlpha)
        ((N : ℝ) ^ truncatedSixthLowerBeta) ((N : ℝ) ^ truncatedSixthLowerSigma)
        ((N : ℝ) ^ truncatedSixthLowerLambda) : ℝ) := by
  obtain ⟨T, hT, hc⟩ := truncatedSixthClosure_actual_lower hδ hδhi hε
  refine ⟨T, hT, ?_⟩
  intro N hN he
  have hg := truncatedSixthTable_actual_gain_le hδ hδhi
  have hcoef : truncatedSixthLowerFdelta δ +
      (∑ j : Fin 9, truncatedSixthTableBeta δ j * tableFeedbackActualVector δ j) - ε ≤
      truncatedSixthLowerFdelta δ + truncatedSixthLowerHadmdelta δ - ε := by linarith
  have hm := mul_le_mul_of_nonneg_right hcoef
    (truncatedSixthClosure_scale_nonneg (hT.trans hN))
  have hm' := hc N hN he
  exact le_trans (by
    simpa only [truncatedSixthMassScale, mul_div_assoc, mul_assoc] using hm) hm'

theorem truncatedSixthTable_classical_count {ε : ℝ} (hε : 0 < ε) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 100 ∧
      ∀ δ : ℝ, 0 < δ → δ < δ0 →
        ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
          (truncatedSixthLowerF6lin +
            (∑ j : Fin 9, truncatedSixthTableBeta δ j * tableFeedbackActualVector δ j) - ε) *
            wuSingularSeries N * N / log N ^ (2 : ℕ) ≤
          (truncatedSixthMass N ((N : ℝ) ^ truncatedSixthLowerAlpha)
            ((N : ℝ) ^ truncatedSixthLowerBeta) ((N : ℝ) ^ truncatedSixthLowerSigma)
            ((N : ℝ) ^ truncatedSixthLowerLambda) : ℝ) := by
  obtain ⟨δ0, hδ0, hδ0hi, hc⟩ := truncatedSixthZeroDelta_actual_lower hε
  refine ⟨δ0, hδ0, hδ0hi, ?_⟩
  intro δ hδ hsmall
  obtain ⟨T, hT, hcount⟩ := hc δ hδ hsmall
  refine ⟨T, hT, ?_⟩
  intro N hN he
  have hg := truncatedSixthTable_actual_gain_le hδ (hsmall.trans_le hδ0hi)
  have hcoef : truncatedSixthLowerF6lin +
      (∑ j : Fin 9, truncatedSixthTableBeta δ j * tableFeedbackActualVector δ j) - ε ≤
      truncatedSixthLowerF6lin + truncatedSixthLowerHadmdelta δ - ε := by linarith
  have hm := mul_le_mul_of_nonneg_right hcoef
    (truncatedSixthClosure_scale_nonneg (hT.trans hN))
  exact le_trans (by
    simpa only [truncatedSixthMassScale, mul_div_assoc, mul_assoc] using hm) (hcount N hN he)

end Wu2008DoubleSieve
