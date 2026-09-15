import MathlibNt.Wu2008DoubleSieve.TruncatedSixthSmallDeltaGain
import MathlibNt.Wu2008DoubleSieve.TruncatedSixthZeroDeltaEndpoint

namespace Wu2008DoubleSieve.TruncatedSixthSmallDeltaGain
open Real
open scoped Classical

/-- The delta is chosen internally after epsilon; the threshold follows that fixed delta. -/
theorem actual_count_lower {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (truncatedSixthLowerF6lin + 47/481250 - ε) *
        wuSingularSeries N * N / log N ^ (2 : ℕ) ≤
      (truncatedSixthMass N ((N : ℝ) ^ truncatedSixthLowerAlpha)
        ((N : ℝ) ^ truncatedSixthLowerBeta) ((N : ℝ) ^ truncatedSixthLowerSigma)
        ((N : ℝ) ^ truncatedSixthLowerLambda) : ℝ) := by
  obtain ⟨δ0, hδ0, _hδ0hi, hcount⟩ := truncatedSixthZeroDelta_actual_lower hε
  let δ : ℝ := min (δ0/2) (1/1000)
  have hδ : 0 < δ := lt_min (half_pos hδ0) (by norm_num)
  have hδhi : δ ≤ 1/1000 := min_le_right _ _
  have hδsmall : δ < δ0 := (min_le_left _ _).trans_lt (by linarith)
  obtain ⟨T, hT4, hT⟩ := hcount δ hδ hδsmall
  refine ⟨T, hT4, ?_⟩
  intro N hN he
  have hc : truncatedSixthLowerF6lin + 47/481250 - ε ≤
      truncatedSixthLowerF6lin + truncatedSixthLowerHadmdelta δ - ε := by
    linarith [hadmdelta_lower hδ hδhi]
  have hmain := mul_le_mul_of_nonneg_right hc
    (truncatedSixthClosure_scale_nonneg (hT4.trans hN))
  have hmain' : (truncatedSixthLowerF6lin + 47/481250 - ε) *
      wuSingularSeries N * N / log N ^ (2 : ℕ) ≤
      (truncatedSixthLowerF6lin + truncatedSixthLowerHadmdelta δ - ε) *
        wuSingularSeries N * N / log N ^ (2 : ℕ) := by
    simpa only [truncatedSixthMassScale, mul_div_assoc, mul_assoc] using hmain
  exact hmain'.trans (hT N hN he)

/-- The gain refers to the unchanged original masked integral and outer factor. -/
theorem hadmdelta_object (δ : ℝ) : truncatedSixthLowerHadmdelta δ =
    4 * ∫ x in truncatedSixthLowerAlpha..truncatedSixthLowerBeta,
      ∫ y in truncatedSixthLowerBeta..truncatedSixthLowerSigma,
        if truncatedSixthLowerAdmissibleRegion δ x y then
          wuImprovementLimit false δ (truncatedSixthLowerS δ x y) /
            (x * y * (truncatedSixthLowerC δ - x - y)) else 0 := rfl

/-- The headline mass has no delta parameter and keeps the original sieve-count atom. -/
theorem actual_count_object (N : ℕ) :
    truncatedSixthMass N ((N : ℝ) ^ truncatedSixthLowerAlpha)
      ((N : ℝ) ^ truncatedSixthLowerBeta) ((N : ℝ) ^ truncatedSixthLowerSigma)
      ((N : ℝ) ^ truncatedSixthLowerLambda) =
    ∑ t ∈ truncatedSixthKept N ((N : ℝ) ^ truncatedSixthLowerAlpha)
      ((N : ℝ) ^ truncatedSixthLowerBeta) ((N : ℝ) ^ truncatedSixthLowerSigma)
      ((N : ℝ) ^ truncatedSixthLowerLambda),
      sieveCount N (t.1 * t.2) N ((N : ℝ) ^ truncatedSixthLowerAlpha) := rfl

end Wu2008DoubleSieve.TruncatedSixthSmallDeltaGain
