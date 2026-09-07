import MathlibNt.SieveTheory.LiLiuGoldbachPositiveScalarPolynomial
open Set MeasureTheory Finset
open MathlibNt.SieveTheory.SwitchingPrinciple
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
set_option maxHeartbeats 0
set_option maxRecDepth 10000

/-- The one fixed log truncation; its degree is not selected by a search. -/
noncomputable def goldbachPositiveScalarL (z : ℝ) : ℝ :=
  2 * ∑ i ∈ range 32, z^(2*i+1)/(2*(i : ℝ)+1)

/-- Uniform analytic log error on the complete closed transformed interval. -/
theorem goldbachPositiveScalarL_bounds {z : ℝ} (hz : 0 ≤ z) (hzu : z ≤ 2/3) :
    goldbachPositiveScalarL z ≤ Real.log ((1+z)/(1-z)) ∧
    Real.log ((1+z)/(1-z)) ≤ goldbachPositiveScalarL z + 1/10^9 := by
  have hz1 : z < 1 := by linarith
  have hlo := Real.sum_range_le_log_div hz hz1 32
  have hhi := Real.log_div_le_sum_range_add hz hz1 32
  have he : 2*z^65/(1-z^2) ≤ (1 : ℝ)/10^9 := by
    have hd : (5/9 : ℝ) ≤ 1-z^2 := by nlinarith
    calc
      _ ≤ 2*(2/3 : ℝ)^65/(5/9) := by gcongr
      _ ≤ (1 : ℝ)/10^9 := by norm_num
  unfold goldbachPositiveScalarL
  constructor
  · linarith
  · norm_num only at hhi
    rw [mul_div_assoc] at he
    linarith

/-- Source identification for the literal f(6), f(33/8), not f(53/8). -/
theorem goldbachPositiveScalar_actual_eq :
    goldbachWeightFiveNegativeScalarCoefficient =
      (53/2 : ℝ)*(Real.log 5 + ∫ v in (3 : ℝ)..5, jurkatRichertInnerIntegral v/v) +
      8*(Real.log (25/8 : ℝ) + ∫ v in (3 : ℝ)..(25/8 : ℝ), jurkatRichertInnerIntegral v/v) -
      (2360636/100000 : ℝ) - (1951976/100000 : ℝ) -
      4*(84289/100000 : ℝ) - (540996/100000 : ℝ) - 2*(60962/100000 : ℝ) := by
  unfold goldbachWeightFiveNegativeScalarCoefficient dimensionOneLowerLinearSieveFactor
  norm_num only
  have he := goldbachPositiveScalar_exp_cancel
    ((53/2 : ℝ)*(Real.log 5 + ∫ v in (3 : ℝ)..5, jurkatRichertInnerIntegral v/v) +
      8*(Real.log (25/8 : ℝ) + ∫ v in (3 : ℝ)..(25/8 : ℝ), jurkatRichertInnerIntegral v/v))
  linear_combination he

/-- The fixed exact rational analytic expression, prior to decimal rounding. -/
noncomputable def goldbachPositiveScalarExactRational : ℝ :=
  (53/2 : ℝ)*(goldbachPositiveScalarL (2/3) + goldbachPositiveScalarA (1/2)) +
    8*(goldbachPositiveScalarL (17/33) + goldbachPositiveScalarA (1/17)) -
    (2360636/100000 : ℝ) - (1951976/100000 : ℝ) -
    4*(84289/100000 : ℝ) - (540996/100000 : ℝ) - 2*(60962/100000 : ℝ)

/-- Single downward rounding of the fixed exact expression to denominator 10^8. -/
noncomputable def goldbachPositiveScalarRationalLower : ℝ := 62033529/100000000

/-- Kernel-checked exact rational comparison; no approximate evaluation is used. -/
theorem goldbachPositiveScalar_rounding :
    goldbachPositiveScalarRationalLower ≤ goldbachPositiveScalarExactRational ∧
    goldbachPositiveScalarExactRational < goldbachPositiveScalarRationalLower + 1/10^8 := by
  norm_num [goldbachPositiveScalarRationalLower, goldbachPositiveScalarExactRational,
    goldbachPositiveScalarL, goldbachPositiveScalarA, Finset.sum_range_succ]

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig