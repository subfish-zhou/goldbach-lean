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


end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig