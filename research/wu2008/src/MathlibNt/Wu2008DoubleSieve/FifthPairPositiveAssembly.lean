import MathlibNt.Wu2008DoubleSieve.FifthPairEndpoint
import MathlibNt.Wu2008DoubleSieve.BaseLowerAssembly

namespace Wu2008DoubleSieve
open Finset Real
open scoped Classical

/-- Literal term five of `finiteElevenExpression` specialized to the original sieve.
The larger prime is the outer index, with multiplicity one and no symmetry factor. -/
theorem fifthPair_count_literal (N : ℕ) :
    fifthPairCount N =
      ∑ q ∈ primeWindow N ((N : ℝ)^truncatedSixthLowerAlpha)
        ((N : ℝ)^truncatedSixthLowerBeta),
        ∑ p ∈ primeWindow N ((N : ℝ)^truncatedSixthLowerAlpha) (q : ℝ),
          sieveCount N (p*q) N ((N : ℝ)^truncatedSixthLowerAlpha) := rfl

/-- Actual positive terms 1, 2, 5 and the retained sixth, with weights 3, 1, 1, 1.
Both existing producers receive epsilon/2 before one common maximum threshold.
No negative term, signed-expression positivity or numerical coefficient estimate is asserted. -/
theorem first_second_fifth_sixth_actual_lower {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (24*wuLowerCoefficient (1/(2*truncatedSixthLowerAlpha)) +
        8*wuLowerCoefficient (1/(2*truncatedSixthLowerBeta)) + fifthPairFlin +
        truncatedSixthLowerF6lin + 47/481250-ε)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
      3*(sieveCount N 1 N ((N : ℝ)^truncatedSixthLowerAlpha) : ℝ) +
        (sieveCount N 1 N ((N : ℝ)^truncatedSixthLowerBeta) : ℝ) +
        (fifthPairCount N : ℝ) +
        (truncatedSixthMass N ((N : ℝ)^truncatedSixthLowerAlpha)
          ((N : ℝ)^truncatedSixthLowerBeta) ((N : ℝ)^truncatedSixthLowerSigma)
          ((N : ℝ)^truncatedSixthLowerLambda) : ℝ) := by
  obtain ⟨T126, hT1264, hT126⟩ := BaseLowerCounts.first_second_sixth_actual_lower
    (show 0 < ε/2 by positivity)
  obtain ⟨T5, _hT54, hT5⟩ := fifthPair_actual_lower (show 0 < ε/2 by positivity)
  refine ⟨max T126 T5, hT1264.trans (le_max_left _ _), ?_⟩
  intro N hN he
  have h126 := hT126 N ((le_max_left _ _).trans hN) he
  have h5 := hT5 N ((le_max_right _ _).trans hN) he
  calc
    _ = (24*wuLowerCoefficient (1/(2*truncatedSixthLowerAlpha)) +
        8*wuLowerCoefficient (1/(2*truncatedSixthLowerBeta)) +
        truncatedSixthLowerF6lin + 47/481250-ε/2)*wuSingularSeries N*N/log N^(2 : ℕ) +
        (fifthPairFlin-ε/2)*wuSingularSeries N*N/log N^(2 : ℕ) := by ring
    _ ≤ _ := by linarith [add_le_add h126 h5]

end Wu2008DoubleSieve
