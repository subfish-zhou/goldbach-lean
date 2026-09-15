import MathlibNt.Wu2008DoubleSieve.BaseLowerCounts

namespace Wu2008DoubleSieve.BaseLowerCounts
open Real
open scoped Classical

/-- The two original exponents lie in the fixed-exponent classical range. -/
theorem original_exponents :
    (1/20 : ℝ) ≤ truncatedSixthLowerAlpha ∧ truncatedSixthLowerAlpha ≤ 1/4 ∧
    (1/20 : ℝ) ≤ truncatedSixthLowerBeta ∧ truncatedSixthLowerBeta ≤ 1/4 := by
  norm_num [truncatedSixthLowerAlpha, truncatedSixthLowerBeta]

/-- The original first and second terms, with weights three and one. -/
theorem first_second_actual_lower {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (24*wuLowerCoefficient (1/(2*truncatedSixthLowerAlpha)) +
        8*wuLowerCoefficient (1/(2*truncatedSixthLowerBeta))-ε)*
        wuSingularSeries N*N/log N^(2 : ℕ) ≤
      3*(sieveCount N 1 N ((N : ℝ)^truncatedSixthLowerAlpha) : ℝ) +
        (sieveCount N 1 N ((N : ℝ)^truncatedSixthLowerBeta) : ℝ) := by
  obtain ⟨Tα, hTα4, hTα⟩ := actual_count_lower original_exponents.1
    original_exponents.2.1 (show 0 < ε/4 by positivity)
  obtain ⟨Tβ, _hTβ4, hTβ⟩ := actual_count_lower original_exponents.2.2.1
    original_exponents.2.2.2 (show 0 < ε/4 by positivity)
  refine ⟨max Tα Tβ, hTα4.trans (le_max_left _ _), ?_⟩
  intro N hN he
  have hα := hTα N ((le_max_left _ _).trans hN) he
  have hβ := hTβ N ((le_max_right _ _).trans hN) he
  calc
    _ = 3*((8*wuLowerCoefficient (1/(2*truncatedSixthLowerAlpha))-ε/4)*
        wuSingularSeries N*N/log N^(2 : ℕ)) +
        (8*wuLowerCoefficient (1/(2*truncatedSixthLowerBeta))-ε/4)*
        wuSingularSeries N*N/log N^(2 : ℕ) := by ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hα (by norm_num)) hβ

/-- One threshold for the actual first, second and retained sixth terms.
The fifth term and every negative term remain outside this statement. -/
theorem first_second_sixth_actual_lower {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (24*wuLowerCoefficient (1/(2*truncatedSixthLowerAlpha)) +
        8*wuLowerCoefficient (1/(2*truncatedSixthLowerBeta)) +
        truncatedSixthLowerF6lin + 47/481250-ε)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
      3*(sieveCount N 1 N ((N : ℝ)^truncatedSixthLowerAlpha) : ℝ) +
        (sieveCount N 1 N ((N : ℝ)^truncatedSixthLowerBeta) : ℝ) +
        (truncatedSixthMass N ((N : ℝ)^truncatedSixthLowerAlpha)
          ((N : ℝ)^truncatedSixthLowerBeta) ((N : ℝ)^truncatedSixthLowerSigma)
          ((N : ℝ)^truncatedSixthLowerLambda) : ℝ) := by
  obtain ⟨T12, hT124, hT12⟩ := first_second_actual_lower (show 0 < ε/2 by positivity)
  obtain ⟨T6, _hT64, hT6⟩ := TruncatedSixthSmallDeltaGain.actual_count_lower
    (show 0 < ε/2 by positivity)
  refine ⟨max T12 T6, hT124.trans (le_max_left _ _), ?_⟩
  intro N hN he
  have h12 := hT12 N ((le_max_left _ _).trans hN) he
  have h6 := hT6 N ((le_max_right _ _).trans hN) he
  calc
    _ = (24*wuLowerCoefficient (1/(2*truncatedSixthLowerAlpha)) +
        8*wuLowerCoefficient (1/(2*truncatedSixthLowerBeta))-ε/2)*
        wuSingularSeries N*N/log N^(2 : ℕ) +
        (truncatedSixthLowerF6lin+47/481250-ε/2)*
        wuSingularSeries N*N/log N^(2 : ℕ) := by ring
    _ ≤ _ := add_le_add h12 h6

end Wu2008DoubleSieve.BaseLowerCounts
