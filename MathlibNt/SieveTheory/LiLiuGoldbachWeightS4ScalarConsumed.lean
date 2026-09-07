import MathlibNt.SieveTheory.LiLiuGoldbachS4IntegralScalar
import MathlibNt.SieveTheory.LiLiuGoldbachWeightRemainingFive

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Preserve the external multiplicity two and the actual signed remaining count. -/
theorem goldbachWeight_remainingFive_s4Scalar_consumed
    (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (hεu : ε < (2 : ℝ)/15) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
      (goldbachWeightRemainingFive (goldbachDifferenceCarrier N ε) N
        ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ))
        ((N : ℝ)^(3/11 : ℝ)) : ℝ) +
        (goldbachWeightSixCoefficient ε - 2*(60962/100000 : ℝ) - δ) *
          (SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) ≤
        4*(D19 N : ℝ) := by
  obtain ⟨N₀, hN₀, h⟩ :=
    goldbachWeight_remainingFive_S1_S2_S3_S4_I10_consumed_eventually δ ε hδ hε hεu
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN hEven
  have hs : 0 ≤ SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2 :=
    div_nonneg (mul_nonneg (SingularSeries.liuSingularSeries_pos N).le
      (Nat.cast_nonneg N)) (sq_nonneg _)
  have hc : goldbachWeightSixCoefficient ε - 2*(60962/100000 : ℝ) - δ ≤
      goldbachWeightFiveCoefficient ε - δ := by
    unfold goldbachWeightFiveCoefficient
    linarith [goldbachB8MainIntegral_eight_mul_le_60962]
  exact (add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hc hs)).trans (h N hN hEven)

/-- The epsilon cutoff precedes epsilon, and the N threshold may depend on epsilon. -/
theorem goldbachWeight_remainingFive_s4Scalar_small_epsilon (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ (2/15 : ℝ) ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
          (goldbachWeightRemainingFive (goldbachDifferenceCarrier N ε) N
            ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ))
            ((N : ℝ)^(3/11 : ℝ)) : ℝ) +
            (goldbachWeightSixCoefficient 0 - 2*(60962/100000 : ℝ) - δ)*
              (SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) ≤
            4*(D19 N : ℝ) := by
  obtain ⟨ε₀, hε₀, hε₀u, h⟩ := goldbachWeight_remainingFive_small_epsilon δ hδ
  refine ⟨ε₀, hε₀, hε₀u, ?_⟩
  intro ε hε hεlt
  obtain ⟨N₀, hN₀, hN⟩ := h ε hε hεlt
  refine ⟨N₀, hN₀, ?_⟩
  intro N hNN hEven
  have hs : 0 ≤ SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2 :=
    div_nonneg (mul_nonneg (SingularSeries.liuSingularSeries_pos N).le
      (Nat.cast_nonneg N)) (sq_nonneg _)
  have hc : goldbachWeightSixCoefficient 0 - 2*(60962/100000 : ℝ) - δ ≤
      goldbachWeightFiveCoefficient 0 - δ := by
    unfold goldbachWeightFiveCoefficient
    linarith [goldbachB8MainIntegral_eight_mul_le_60962]
  exact (add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hc hs)).trans (hN N hNN hEven)

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig