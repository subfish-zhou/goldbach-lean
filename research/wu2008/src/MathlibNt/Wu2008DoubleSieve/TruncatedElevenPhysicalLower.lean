import MathlibNt.Wu2008DoubleSieve.TruncatedElevenSignedLower
import MathlibNt.Wu2008DoubleSieve.SeventhEighthFixedEndpoint

/-! A direct consumer of the actual seventh/eighth switching bound.
The two four-prime counts remain on their original domains. -/
namespace Wu2008DoubleSieve.TruncatedElevenPhysicalLower
open Finset Real SingleUpperCounts SingleUpperClassicalLimit
open scoped Classical

/-- One threshold and one error budget, with no physical-count bound assumed. -/
theorem truncated_fixed_physical_lower {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      let z := (N : ℝ)^truncatedSixthLowerAlpha
      let w := (N : ℝ)^truncatedSixthLowerBeta
      let V := (N : ℝ)^truncatedSixthLowerLambda
      (24*wuLowerCoefficient (1/(2*truncatedSixthLowerAlpha)) +
        8*wuLowerCoefficient (1/(2*truncatedSixthLowerBeta)) + fifthPairFlin +
        truncatedSixthLowerF6lin + 47/481250 -
        Glin (1/3) - Glin truncatedSixthLowerSigma - 8*J9 - ε)*
          wuSingularSeries N*N/log N^(2 : ℕ) -
        2*((SeventhEighth.physicalT7 N).card : ℝ) -
        ((SeventhEighth.physicalT8 N).card : ℝ) -
        ((∑ t ∈ s3DistinctQuadruples N (orderedTriples (primeWindow N z w)),
          sieveCount N (t.1*t.2.1*t.2.2.1*t.2.2.2) N (t.2.1 : ℝ)) : ℤ) -
        ((∑ t ∈ s3Upsilon11Range N z w V,
          sieveCount N (t.1*t.2.1*t.2.2.1*t.2.2.2) N (t.2.1 : ℝ)) : ℤ) ≤
      (truncatedSixthFixedExpression N : ℝ) := by
  obtain ⟨T1, hT1, h1⟩ :=
    TruncatedElevenSignedLower.truncated_fixed_actual_lower (half_pos hε)
  obtain ⟨T2, _, h2⟩ :=
    SeventhEighth.fixed_weighted_switching_epsilon (half_pos hε)
  refine ⟨max T1 T2, hT1.trans (le_max_left _ _), ?_⟩
  intro N hN he
  dsimp only
  have ha := h1 N ((le_max_left T1 T2).trans hN) he
  dsimp only at ha
  have hb := h2 N ((le_max_right T1 T2).trans hN) he
  have hz : SeventhEighth.z N = (N : ℝ)^truncatedSixthLowerAlpha := rfl
  have hw : SeventhEighth.w N = (N : ℝ)^truncatedSixthLowerBeta := rfl
  have hu : SeventhEighth.u N = (N : ℝ)^truncatedSixthLowerSigma := rfl
  have hv : SeventhEighth.v N = (N : ℝ)^(1/3 : ℝ) := rfl
  rw [hz, hw, hu, hv] at hb
  push_cast at hb
  ring_nf at ha hb ⊢
  linarith only [ha, hb]

end Wu2008DoubleSieve.TruncatedElevenPhysicalLower
