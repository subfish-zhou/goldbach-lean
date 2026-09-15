import MathlibNt.Wu2008DoubleSieve.TruncatedElevenPhysicalLower
import MathlibNt.Wu2008DoubleSieve.TruncatedFourPayment

/-! All four residual negative counts replaced by their literal physical families.
No classical density estimate or positivity conclusion is asserted here. -/
namespace Wu2008DoubleSieve.TruncatedElevenAllPhysicalLower
open Finset Real SingleUpperCounts SingleUpperClassicalLimit
open scoped Classical

theorem truncated_fixed_all_physical_lower {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (24*wuLowerCoefficient (1/(2*truncatedSixthLowerAlpha)) +
        8*wuLowerCoefficient (1/(2*truncatedSixthLowerBeta)) + fifthPairFlin +
        truncatedSixthLowerF6lin + 47/481250 -
        Glin (1/3) - Glin truncatedSixthLowerSigma - 8*J9 - ε)*
          wuSingularSeries N*N/log N^(2 : ℕ) -
        2*((SeventhEighth.physicalT7 N).card : ℝ) -
        ((SeventhEighth.physicalT8 N).card : ℝ) -
        ((TruncatedFourPhysical.Physical10 N).card : ℝ) -
        ((TruncatedFourPhysical.Physical11 N).card : ℝ) ≤
      (truncatedSixthFixedExpression N : ℝ) := by
  obtain ⟨T1, hT1, h1⟩ :=
    TruncatedElevenPhysicalLower.truncated_fixed_physical_lower (half_pos hε)
  obtain ⟨T2, _, h2⟩ := TruncatedFourPhysical.original_sums_upper (half_pos hε)
  refine ⟨max T1 T2, hT1.trans (le_max_left _ _), ?_⟩
  intro N hN he
  have ha := h1 N ((le_max_left T1 T2).trans hN) he
  have hb := h2 N ((le_max_right T1 T2).trans hN) he
  dsimp only at ha hb
  ring_nf at ha hb ⊢
  linarith only [ha, hb]

end Wu2008DoubleSieve.TruncatedElevenAllPhysicalLower
