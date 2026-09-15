import MathlibNt.Wu2008DoubleSieve.TruncatedSixthZeroDeltaLimit

/-!
# Small fixed-delta actual counts with the full classical coefficient

Only the classical coefficient is sent to its zero-delta limit.
The actual admissible improvement is retained at each fixed delta,
and the count threshold is chosen after that delta.
-/

namespace Wu2008DoubleSieve

open Real
open scoped Classical

theorem truncatedSixthZeroDelta_actual_lower {ε : ℝ} (hε : 0 < ε) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 100 ∧
      ∀ δ : ℝ, 0 < δ → δ < δ0 →
        ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
          (truncatedSixthLowerF6lin + truncatedSixthLowerHadmdelta δ - ε) *
            wuSingularSeries N * N / log N ^ (2 : ℕ) ≤
          (truncatedSixthMass N ((N : ℝ) ^ truncatedSixthLowerAlpha)
            ((N : ℝ) ^ truncatedSixthLowerBeta) ((N : ℝ) ^ truncatedSixthLowerSigma)
            ((N : ℝ) ^ truncatedSixthLowerLambda) : ℝ) := by
  obtain ⟨δ0, hδ0, hδ0hi, hclose⟩ := truncatedSixthZeroDelta_Fdelta_close (half_pos hε)
  refine ⟨δ0, hδ0, hδ0hi, ?_⟩
  intro δ hδ hδsmall
  have hclassical := (abs_lt.mp (hclose δ hδ hδsmall)).1
  obtain ⟨T, hT, hcount⟩ :=
    truncatedSixthClosure_actual_lower hδ (hδsmall.trans_le hδ0hi) (half_pos hε)
  refine ⟨T, hT, ?_⟩
  intro N hN he
  have hcoef : truncatedSixthLowerF6lin + truncatedSixthLowerHadmdelta δ - ε ≤
      truncatedSixthLowerFdelta δ + truncatedSixthLowerHadmdelta δ - ε / 2 := by
    linarith
  have hmain := mul_le_mul_of_nonneg_right hcoef
    (truncatedSixthClosure_scale_nonneg (hT.trans hN))
  have hmain' :
      (truncatedSixthLowerF6lin + truncatedSixthLowerHadmdelta δ - ε) *
        wuSingularSeries N * N / log N ^ (2 : ℕ) ≤
      (truncatedSixthLowerFdelta δ + truncatedSixthLowerHadmdelta δ - ε / 2) *
        wuSingularSeries N * N / log N ^ (2 : ℕ) := by
    simpa only [truncatedSixthMassScale, mul_div_assoc, mul_assoc] using hmain
  exact hmain'.trans (hcount N hN he)

theorem truncatedSixthZeroDelta_full_rectangle_actual_lower {ε : ℝ} (hε : 0 < ε) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 100 ∧
      ∀ δ : ℝ, 0 < δ → δ < δ0 →
        ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
          ((4 * ∫ x in truncatedSixthLowerAlpha..truncatedSixthLowerBeta,
              ∫ y in truncatedSixthLowerBeta..truncatedSixthLowerSigma,
                wuLowerCoefficient ((1 / 2 - x - y) / truncatedSixthLowerAlpha) /
                  (x * y * (1 / 2 - x - y))) +
              truncatedSixthLowerHadmdelta δ - ε) *
            wuSingularSeries N * N / log N ^ (2 : ℕ) ≤
          (truncatedSixthMass N ((N : ℝ) ^ truncatedSixthLowerAlpha)
            ((N : ℝ) ^ truncatedSixthLowerBeta) ((N : ℝ) ^ truncatedSixthLowerSigma)
            ((N : ℝ) ^ truncatedSixthLowerLambda) : ℝ) := by
  simpa only [truncatedSixthZeroDelta_full_rectangle] using truncatedSixthZeroDelta_actual_lower hε

end Wu2008DoubleSieve
