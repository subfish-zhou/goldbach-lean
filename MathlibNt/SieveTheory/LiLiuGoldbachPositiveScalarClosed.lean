import MathlibNt.SieveTheory.LiLiuGoldbachPositiveScalarAnalytic
import MathlibNt.SieveTheory.LiLiuGoldbachPositiveScalarValues
open Set MeasureTheory Finset
open MathlibNt.SieveTheory.SwitchingPrinciple
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
set_option maxRecDepth 10000
set_option maxHeartbeats 0

/-- Full analytic error budget, before the one final rational rounding. -/
theorem goldbachPositiveScalar_exact_bounds :
    goldbachPositiveScalarExactRational ≤ goldbachWeightFiveNegativeScalarCoefficient ∧
    goldbachWeightFiveNegativeScalarCoefficient ≤
      goldbachPositiveScalarExactRational + 3/5000000 := by
  have h5 := goldbachPositiveScalar_integral_bounds (b := (5 : ℝ)) (by constructor <;> norm_num)
  have h25 := goldbachPositiveScalar_integral_bounds (b := (25/8 : ℝ)) (by constructor <;> norm_num)
  have hL5 := goldbachPositiveScalarL_bounds (z := (2/3 : ℝ)) (by norm_num) le_rfl
  have hL25 := goldbachPositiveScalarL_bounds (z := (17/33 : ℝ)) (by norm_num) (by norm_num)
  norm_num only at h5 h25 hL5 hL25
  rw [goldbachPositiveScalar_actual_eq]
  unfold goldbachPositiveScalarExactRational
  constructor <;> linarith [h5.1, h5.2, h25.1, h25.2, hL5.1, hL5.2, hL25.1, hL25.2]

/-- Unconditional named rational lower bound for the complete literal five-negative coefficient. -/
theorem goldbachWeightFiveNegativeScalarCoefficient_ge_62033529 :
    (62033529/100000000 : ℝ) ≤ goldbachWeightFiveNegativeScalarCoefficient :=
  goldbachPositiveScalar_rounding.1.trans goldbachPositiveScalar_exact_bounds.1

/-- The whole certified gap, including the final downward rounding, is at most 10^-6. -/
theorem goldbachWeightFiveNegativeScalarCoefficient_rational_error :
    0 ≤ goldbachWeightFiveNegativeScalarCoefficient - (62033529/100000000 : ℝ) ∧
    goldbachWeightFiveNegativeScalarCoefficient - (62033529/100000000 : ℝ) ≤ 1/10^6 := by
  have hlo := goldbachWeightFiveNegativeScalarCoefficient_ge_62033529
  have hhi := goldbachPositiveScalar_exact_bounds.2
  have hr := goldbachPositiveScalar_rounding.2
  unfold goldbachPositiveScalarRationalLower at hr
  constructor <;> linarith

/-- Actual signed D19 terminal. No sign assertion is made for RemainingFive or D19. -/
theorem goldbachWeight_remainingFive_rationalPositiveScalar_small_epsilon
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ (2/15 : ℝ) ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
          (goldbachWeightRemainingFive (goldbachDifferenceCarrier N ε) N
            ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ))
            ((N : ℝ)^(3/11 : ℝ)) : ℝ) +
            ((62033529/100000000 : ℝ)-δ)*
              (SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) ≤
            4*(D19 N : ℝ) := by
  obtain ⟨ε₀, hε₀, hε₀u, h⟩ := goldbachWeight_remainingFive_fiveNegativeScalars_small_epsilon δ hδ
  refine ⟨ε₀, hε₀, hε₀u, ?_⟩
  intro ε hε hεlt
  obtain ⟨N₀, hN₀, hN⟩ := h ε hε hεlt
  refine ⟨N₀, hN₀, ?_⟩
  intro N hNN hEven
  have hs : 0 ≤ SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2 :=
    div_nonneg (mul_nonneg (SingularSeries.liuSingularSeries_pos N).le
      (Nat.cast_nonneg N)) (sq_nonneg _)
  exact (add_le_add (le_refl _) (mul_le_mul_of_nonneg_right
    (sub_le_sub_right goldbachWeightFiveNegativeScalarCoefficient_ge_62033529 δ) hs)).trans
      (hN N hNN hEven)

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig