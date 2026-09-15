import MathlibNt.Wu2008DoubleSieve.TruncatedSixthTableCount
import MathlibNt.Wu2008DoubleSieve.TruncatedSixthTablePayment

/-!
# Actual truncated-sixth count with the nine zero-delta coefficients

Epsilon determines a delta threshold first. After a fixed delta is
chosen, the actual count supplies its N threshold. The true H vector
is never replaced by a zero-delta limit.
-/

namespace Wu2008DoubleSieve

open Real
open scoped Classical BigOperators

theorem truncatedSixthTable_actual_count {ε : ℝ} (hε : 0 < ε) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 100 ∧
      ∀ δ : ℝ, 0 < δ → δ < δ0 →
        ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
          (truncatedSixthLowerF6lin +
            (∑ j : Fin 9, truncatedSixthTableBeta 0 j * tableFeedbackActualVector δ j) - ε) *
            wuSingularSeries N * N / log N ^ (2 : ℕ) ≤
          (truncatedSixthMass N ((N : ℝ) ^ truncatedSixthLowerAlpha)
            ((N : ℝ) ^ truncatedSixthLowerBeta) ((N : ℝ) ^ truncatedSixthLowerSigma)
            ((N : ℝ) ^ truncatedSixthLowerLambda) : ℝ) := by
  obtain ⟨dC, hdC, hdChi, hc⟩ := truncatedSixthTable_classical_count (half_pos hε)
  obtain ⟨dB, hdB, _, hb⟩ := truncatedSixthTable_coefficient_payment (half_pos hε)
  refine ⟨min dC dB, lt_min hdC hdB, (min_le_left _ _).trans hdChi, ?_⟩
  intro δ hδ hsmall
  have hδC := hsmall.trans_le (min_le_left dC dB)
  have hδB := hsmall.trans_le (min_le_right dC dB)
  obtain ⟨T, hT, hcount⟩ := hc δ hδ hδC
  have hpaid := hb δ hδ hδB
  refine ⟨T, hT, ?_⟩
  intro N hN he
  have hcoef : truncatedSixthLowerF6lin +
      (∑ j : Fin 9, truncatedSixthTableBeta 0 j * tableFeedbackActualVector δ j) - ε ≤
      truncatedSixthLowerF6lin +
      (∑ j : Fin 9, truncatedSixthTableBeta δ j * tableFeedbackActualVector δ j) - ε / 2 := by
    linarith
  have hm := mul_le_mul_of_nonneg_right hcoef
    (truncatedSixthClosure_scale_nonneg (hT.trans hN))
  exact le_trans (by
    simpa only [truncatedSixthMassScale, mul_div_assoc, mul_assoc] using hm) (hcount N hN he)

theorem truncatedSixthTable_certified_seed_count {ε : ℝ} (hε : 0 < ε) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 100 ∧
      ∀ δ : ℝ, 0 < δ → δ < δ0 →
        ∀ q : Fin 9 → ℝ, (∀ j, q j ≤ tableFeedbackActualVector δ j) →
          ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
            (truncatedSixthLowerF6lin +
              (∑ j : Fin 9, truncatedSixthTableBeta 0 j * q j) - ε) *
              wuSingularSeries N * N / log N ^ (2 : ℕ) ≤
            (truncatedSixthMass N ((N : ℝ) ^ truncatedSixthLowerAlpha)
              ((N : ℝ) ^ truncatedSixthLowerBeta) ((N : ℝ) ^ truncatedSixthLowerSigma)
              ((N : ℝ) ^ truncatedSixthLowerLambda) : ℝ) := by
  obtain ⟨δ0, hδ0, hδ0hi, hc⟩ := truncatedSixthTable_actual_count hε
  refine ⟨δ0, hδ0, hδ0hi, ?_⟩
  intro δ hδ hsmall q hq
  obtain ⟨T, hT, hcount⟩ := hc δ hδ hsmall
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
    mul_le_mul_of_nonneg_left (hq j) (truncatedSixthTable_beta_nonneg (le_refl 0) j))
  refine ⟨T, hT, ?_⟩
  intro N hN he
  have hcoef : truncatedSixthLowerF6lin +
      (∑ j : Fin 9, truncatedSixthTableBeta 0 j * q j) - ε ≤
      truncatedSixthLowerF6lin +
      (∑ j : Fin 9, truncatedSixthTableBeta 0 j * tableFeedbackActualVector δ j) - ε := by
    linarith
  have hm := mul_le_mul_of_nonneg_right hcoef
    (truncatedSixthClosure_scale_nonneg (hT.trans hN))
  exact le_trans (by
    simpa only [truncatedSixthMassScale, mul_div_assoc, mul_assoc] using hm) (hcount N hN he)

end Wu2008DoubleSieve
