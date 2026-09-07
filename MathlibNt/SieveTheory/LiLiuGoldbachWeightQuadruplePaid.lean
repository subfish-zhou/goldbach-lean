import MathlibNt.SieveTheory.LiLiuGoldbachWeightQuadruple
import MathlibNt.SieveTheory.LiLiuGoldbachWeightInitialPaid

open MathlibNt.SieveTheory.LiLiuOnePlusOneNine
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The actual first refinement after the two proved quadruple comparisons.
The positive triple resources T14/T15 remain explicit; S6 coverage is not assumed. -/
theorem goldbachWeight_quadruple_paid_eventually (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ α β γ : ℝ,
      (1 : ℝ) / 21 < α → α ≤ β → β ≤ γ →
      (goldbachS1 (goldbachDifferenceCarrier N ε) N ((N : ℝ) ^ β) : ℝ) -
        goldbachS3Closed (goldbachDifferenceCarrier N ε) N ((N : ℝ) ^ β) ((N : ℝ) ^ γ) ≥
      (goldbachS1 (goldbachDifferenceCarrier N ε) N ((N : ℝ) ^ α) : ℝ) -
        goldbachS3Closed (goldbachDifferenceCarrier N ε) N ((N : ℝ) ^ α) ((N : ℝ) ^ γ) +
        goldbachWeightG6 (goldbachDifferenceCarrier N ε) N ((N : ℝ) ^ α) ((N : ℝ) ^ β) +
        goldbachWeightG7 (goldbachDifferenceCarrier N ε) N ((N : ℝ) ^ α) ((N : ℝ) ^ β) ((N : ℝ) ^ γ) -
        goldbachWeightG11 (goldbachDifferenceCarrier N ε) N ((N : ℝ) ^ α) ((N : ℝ) ^ β) -
        goldbachWeightG12 (goldbachDifferenceCarrier N ε) N ((N : ℝ) ^ α) ((N : ℝ) ^ β) ((N : ℝ) ^ γ) -
        goldbachWeightT14 (goldbachDifferenceCarrier N ε) N ((N : ℝ) ^ α) ((N : ℝ) ^ β) -
        goldbachWeightT15 (goldbachDifferenceCarrier N ε) N ((N : ℝ) ^ α) ((N : ℝ) ^ β) ((N : ℝ) ^ γ) -
        42 * (N : ℝ) ^ (1 - α) := by
  obtain ⟨N₀, hN₀⟩ := goldbachWeight_initial_paid_eventually ε hε
  refine ⟨N₀, ?_⟩
  intro N hN α β γ hα hαβ hβγ
  have hbase := hN₀ N hN α β γ hα hαβ hβγ
  have h14 := (Int.cast_le (R := ℝ)).mpr
    (goldbachWeightG14_le_goldbachWeightT14_add_goldbachWeightG11
      (goldbachDifferenceCarrier N ε) N ((N : ℝ) ^ α) ((N : ℝ) ^ β))
  have h15 := (Int.cast_le (R := ℝ)).mpr
    (goldbachWeightG15_le_goldbachWeightT15_add_goldbachWeightG12
      (goldbachDifferenceCarrier N ε) N ((N : ℝ) ^ α) ((N : ℝ) ^ β) ((N : ℝ) ^ γ))
  push_cast at h14 h15
  linarith

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig