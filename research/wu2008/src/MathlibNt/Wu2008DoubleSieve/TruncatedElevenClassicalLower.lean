import MathlibNt.Wu2008DoubleSieve.FourClassicalCoefficient
import MathlibNt.Wu2008DoubleSieve.TruncatedElevenSeventhEighthClassicalLower

/-! The two remaining physical counts are replaced by their actual classical
integrals. The sixth term retains its original truncation. No positivity of the
resulting coefficient, and no full Goldbach endpoint, is asserted here. -/
namespace Wu2008DoubleSieve.TruncatedElevenClassicalLower
open Finset Real SingleUpperCounts SingleUpperClassicalLimit
open scoped Classical

theorem truncated_fixed_classical_lower {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (24*wuLowerCoefficient (1/(2*truncatedSixthLowerAlpha)) +
        8*wuLowerCoefficient (1/(2*truncatedSixthLowerBeta)) + fifthPairFlin +
        truncatedSixthLowerF6lin + 47/481250 -
        Glin (1/3) - Glin truncatedSixthLowerSigma - 8*J9 -
        16*SeventhEighth.J7 - 8*SeventhEighth.J8 -
        8*FourRoughClosedMass.I10 - 8*FourRoughClosedMass.I11 - ε)*
          wuSingularSeries N*N/log N^(2 : ℕ) ≤
      (truncatedSixthFixedExpression N : ℝ) := by
  obtain ⟨T1, hT1, h1⟩ :=
    TruncatedElevenSeventhEighthClassicalLower.truncated_fixed_seventh_eighth_classical_lower
      (half_pos hε)
  obtain ⟨T2, _, h2⟩ := FourClassical.physical10_physical11_sum_classical_upper (half_pos hε)
  refine ⟨max T1 T2, hT1.trans (le_max_left _ _), ?_⟩
  intro N hN he
  have ha := h1 N ((le_max_left T1 T2).trans hN) he
  have hb := h2 N ((le_max_right T1 T2).trans hN) he
  ring_nf at ha hb ⊢
  linarith only [ha, hb]

end Wu2008DoubleSieve.TruncatedElevenClassicalLower
