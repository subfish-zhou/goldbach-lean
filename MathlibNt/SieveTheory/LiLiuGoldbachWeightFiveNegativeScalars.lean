import MathlibNt.SieveTheory.LiLiuGoldbachS3IntegralScalarClosed
import MathlibNt.SieveTheory.LiLiuGoldbachWeightThreeNegativeScalars

open MathlibNt.SieveTheory.SwitchingPrinciple
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The five certified negative scalar entries; the positive lower factors remain literal. -/
noncomputable def goldbachWeightFiveNegativeScalarCoefficient : ℝ :=
  Real.exp (-Real.eulerMascheroniConstant) *
    ((159/2 : ℝ)*dimensionOneLowerLinearSieveFactor 6 +
      (33/2 : ℝ)*dimensionOneLowerLinearSieveFactor (33/8 : ℝ)) -
    (2360636/100000 : ℝ) - (1951976/100000 : ℝ) -
    4*(84289/100000 : ℝ) - (540996/100000 : ℝ) - 2*(60962/100000 : ℝ)

theorem goldbachWeightFiveNegativeScalarCoefficient_le :
    goldbachWeightFiveNegativeScalarCoefficient ≤ goldbachWeightThreeNegativeScalarCoefficient := by
  unfold goldbachWeightFiveNegativeScalarCoefficient goldbachWeightThreeNegativeScalarCoefficient
  simp only [mul_add]
  linarith [goldbachS3_oneThird_coefficient_le_2360636,
    goldbachS3_threeElevenths_coefficient_le_1951976]

/-- The actual signed D19 inequality; no positivity of the coefficient or remaining count asserted. -/
theorem goldbachWeight_remainingFive_fiveNegativeScalars_small_epsilon
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ (2/15 : ℝ) ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
          (goldbachWeightRemainingFive (goldbachDifferenceCarrier N ε) N
            ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ))
            ((N : ℝ)^(3/11 : ℝ)) : ℝ) +
            (goldbachWeightFiveNegativeScalarCoefficient-δ)*
              (SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) ≤
            4*(D19 N : ℝ) := by
  obtain ⟨ε₀, hε₀, hε₀u, h⟩ := goldbachWeight_remainingFive_threeNegativeScalars_small_epsilon δ hδ
  refine ⟨ε₀, hε₀, hε₀u, ?_⟩
  intro ε hε hεlt
  obtain ⟨N₀, hN₀, hN⟩ := h ε hε hεlt
  refine ⟨N₀, hN₀, ?_⟩
  intro N hNN hEven
  have hs : 0 ≤ SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2 :=
    div_nonneg (mul_nonneg (SingularSeries.liuSingularSeries_pos N).le
      (Nat.cast_nonneg N)) (sq_nonneg _)
  exact (add_le_add (le_refl _) (mul_le_mul_of_nonneg_right
    (sub_le_sub_right goldbachWeightFiveNegativeScalarCoefficient_le δ) hs)).trans
      (hN N hNN hEven)

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig