import MathlibNt.SieveTheory.LiLiuGoldbachS3RetainedScalar
import MathlibNt.SieveTheory.LiLiuGoldbachB10RetainedEndpoints
import MathlibNt.SieveTheory.LiLiuGoldbachS4RetainedEndpoints
import MathlibNt.SieveTheory.LiLiuGoldbachPositiveScalarClosed
import MathlibNt.SieveTheory.LiLiuGoldbachG11AuthorIntegralBound
import MathlibNt.SieveTheory.LiLiuBuchstabSharpClosure
import MathlibNt.SieveTheory.LiLiuGoldbachG11NormalizedIntegralEnvelope


open MathlibNt.SieveTheory.SwitchingPrinciple
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- All already-proved endpoint bounds, with the external S4 multiplier two. -/
theorem goldbachWeightFiveCoefficient_zero_ge_allRetained :
    (124341093/200000000 : ℝ) ≤ goldbachWeightFiveCoefficient 0 := by
  have hp := goldbachWeightFiveNegativeScalarCoefficient_ge_62033529
  have h4 := goldbachS3_oneThird_coefficient_le_retained236056871187
  have h5 := goldbachS3_threeElevenths_coefficient_le_retained195190815363
  have h8 := S4Retained.goldbachB8MainIntegral_eight_mul_le_60961168
  have h10 := B10Retained.goldbachB10I10_eight_mul_le_540995781
  have h2 := goldbachS2_g3_scalar_le_84289
  unfold goldbachWeightFiveCoefficient
  rw [goldbachWeightSixCoefficient_zero, goldbachWeightKnownCoefficient_zero]
  unfold goldbachWeightFiveNegativeScalarCoefficient at hp
  simp only [mul_add] at hp ⊢
  linarith only [hp, h4, h5, h8, h10, h2]

/-- The improved constant is consumed in the actual remaining-five theorem. -/
theorem goldbachWeight_remainingFive_allRetained_small_epsilon
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ (2/15 : ℝ) ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
          (goldbachWeightRemainingFive (goldbachDifferenceCarrier N ε) N
            ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ))
            ((N : ℝ)^(3/11 : ℝ)) : ℝ) +
            ((124341093/200000000 : ℝ)-δ)*
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
  exact (add_le_add (le_refl _) (mul_le_mul_of_nonneg_right
    (sub_le_sub_right goldbachWeightFiveCoefficient_zero_ge_allRetained δ) hs)).trans
      (hN N hNN hEven)


end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig