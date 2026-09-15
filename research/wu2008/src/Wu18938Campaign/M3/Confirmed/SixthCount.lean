import Wu18938Campaign.M3.Confirmed.TableCertificate
import Wu18938Campaign.M3.Confirmed.SixthSupport
import Wu18938Campaign.M3.Confirmed.ConservativeCount

noncomputable section

namespace Wu18938Campaign.M3.Confirmed

open Wu2008DoubleSieve Real ActualNineFeedback DirectFiniteF6
open scoped Classical

theorem literal_sixth_gain_on_kept_support :
    (3 / 50 : ℝ) <
      4 * (∫ v : ℝ × ℝ,
        if truncatedSixthLowerRegion 0 v.1 v.2 then
          QuarterTrim.kernel (profile originalHeight) v.1 v.2 else 0) := by
  rw [sixth_twentyone_on_kept_support]
  exact literalTableGain_gt_six_percent

theorem literal_sixth_coefficient_gt
    (hC6 : (3819092 / 1000000 : ℝ) ≤ truncatedSixthLowerF6lin) :
    (3879092 / 1000000 : ℝ) <
      truncatedSixthLowerF6lin + Wu08G6High.published originalHeight := by
  rw [← literalTableGain_published]
  linarith only [hC6, literalTableGain_gt_six_percent]

theorem sixth_numeric_from_literal_transport
    (hC6 : (3819092 / 1000000 : ℝ) ≤ truncatedSixthLowerF6lin)
    (htransport : ∀ ε : ℝ, 0 < ε →
      ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (truncatedSixthLowerF6lin + Wu08G6High.published originalHeight - ε) *
          truncatedSixthMassScale N ≤
            (truncatedSixthMass N
              ((N : ℝ) ^ truncatedSixthLowerAlpha)
              ((N : ℝ) ^ truncatedSixthLowerBeta)
              ((N : ℝ) ^ truncatedSixthLowerSigma)
              ((N : ℝ) ^ truncatedSixthLowerLambda) : ℝ))
    {ε : ℝ} (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ((3879092 / 1000000 : ℝ) - ε) * truncatedSixthMassScale N ≤
        (truncatedSixthMass N
          ((N : ℝ) ^ truncatedSixthLowerAlpha)
          ((N : ℝ) ^ truncatedSixthLowerBeta)
          ((N : ℝ) ^ truncatedSixthLowerSigma)
          ((N : ℝ) ^ truncatedSixthLowerLambda) : ℝ) := by
  obtain ⟨T, hT, hc⟩ := htransport ε heps
  refine ⟨T, hT, fun N hN he => ?_⟩
  have hscale : 0 ≤ truncatedSixthMassScale N := by
    have hpos := wuSingularSeries_pos N (by omega)
    unfold truncatedSixthMassScale
    positivity
  exact (mul_le_mul_of_nonneg_right
    (sub_le_sub_right (literal_sixth_coefficient_gt hC6).le ε) hscale).trans
      (hc N hN he)

end Wu18938Campaign.M3.Confirmed
