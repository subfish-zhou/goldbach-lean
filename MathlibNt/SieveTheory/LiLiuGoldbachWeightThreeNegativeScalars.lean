import MathlibNt.SieveTheory.LiLiuGoldbachS2IntegralScalar
import MathlibNt.SieveTheory.LiLiuGoldbachB10IntegralScalar
import MathlibNt.SieveTheory.LiLiuGoldbachWeightS4ScalarConsumed

open MathlibNt.SieveTheory.SwitchingPrinciple
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Certified negative scalar entries; the lower-sieve and S3 integrals are not estimated. -/
noncomputable def goldbachWeightThreeNegativeScalarCoefficient : ℝ :=
  Real.exp (-Real.eulerMascheroniConstant) *
    ((159/2 : ℝ)*dimensionOneLowerLinearSieveFactor 6 +
      (33/2 : ℝ)*dimensionOneLowerLinearSieveFactor (33/8 : ℝ)) -
    (53/2 : ℝ)*Real.exp (-Real.eulerMascheroniConstant)*
      (goldbachS3_primeKernelIntegral (1/3) + goldbachS3_primeKernelIntegral (3/11)) -
    4*(84289/100000 : ℝ) - (540996/100000 : ℝ) - 2*(60962/100000 : ℝ)

theorem goldbachWeightThreeNegativeScalarCoefficient_le :
    goldbachWeightThreeNegativeScalarCoefficient ≤
      goldbachWeightSixCoefficient 0 - 2*(60962/100000 : ℝ) := by
  unfold goldbachWeightThreeNegativeScalarCoefficient
  rw [goldbachWeightSixCoefficient_zero, goldbachWeightKnownCoefficient_zero]
  linarith [goldbachS2_g3_scalar_le_84289, goldbachB10I10_eight_mul_le_540996]

/-- Actual D19 signed bound with the three certified negative constants.
No positivity of the remaining count or of the coefficient is assumed or asserted. -/
theorem goldbachWeight_remainingFive_threeNegativeScalars_small_epsilon
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ (2/15 : ℝ) ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
          (goldbachWeightRemainingFive (goldbachDifferenceCarrier N ε) N
            ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ))
            ((N : ℝ)^(3/11 : ℝ)) : ℝ) +
            (goldbachWeightThreeNegativeScalarCoefficient-δ)*
              (SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) ≤
            4*(D19 N : ℝ) := by
  obtain ⟨ε₀, hε₀, hε₀u, h⟩ := goldbachWeight_remainingFive_s4Scalar_small_epsilon δ hδ
  refine ⟨ε₀, hε₀, hε₀u, ?_⟩
  intro ε hε hεlt
  obtain ⟨N₀, hN₀, hN⟩ := h ε hε hεlt
  refine ⟨N₀, hN₀, ?_⟩
  intro N hNN hEven
  have hs : 0 ≤ SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2 :=
    div_nonneg (mul_nonneg (SingularSeries.liuSingularSeries_pos N).le
      (Nat.cast_nonneg N)) (sq_nonneg _)
  exact (add_le_add (le_refl _) (mul_le_mul_of_nonneg_right
    (sub_le_sub_right goldbachWeightThreeNegativeScalarCoefficient_le δ) hs)).trans
      (hN N hNN hEven)

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig