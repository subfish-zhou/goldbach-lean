import MathlibNt.SieveTheory.LiLiuGoldbachS3IntegralScalarCoefficients

open Set MeasureTheory Finset
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem s3base_log {a : ℝ} (ha : 0 < a) (haU : a ≤ 45/8) :
    53 * (∫ s in a..(45/8 : ℝ), 1/(s*((53/8 : ℝ)-s))) =
      8 * Real.log ((45/8 : ℝ)*((53/8 : ℝ)-a)/a) := by
  rw [goldbachS3_scalar_base_integral ha haU (by norm_num)]
  have hc : (53/8 : ℝ)-a ≠ 0 := by linarith
  rw [Real.log_div (mul_ne_zero (by norm_num) hc) (ne_of_gt ha),
    Real.log_mul (by norm_num) hc]
  norm_num
  ring

theorem s3base4_bound :
    53 * (∫ s in (53/24 : ℝ)..(45/8 : ℝ), 1/(s*((53/8 : ℝ)-s))) ≤
      (s3Base4 : ℝ) := by
  rw [s3base_log (by norm_num) (by norm_num)]
  norm_num only [div_mul_div_comm, div_div, mul_div_assoc] -- normalize the rational log argument
  have h := Real.log_div_le_sum_range_add (by norm_num : (0 : ℝ) ≤ 41/49)
    (by norm_num : (41/49 : ℝ) < 1) 128
  norm_num [Finset.sum_range_succ, pow_succ] at h
  norm_num [s3Base4]
  linarith

theorem s3base5_bound :
    53 * (∫ s in (265/88 : ℝ)..(45/8 : ℝ), 1/(s*((53/8 : ℝ)-s))) ≤
      (s3Base5 : ℝ) := by
  rw [s3base_log (by norm_num) (by norm_num)]
  have h := Real.log_div_le_sum_range_add (by norm_num : (0 : ℝ) ≤ 23/31)
    (by norm_num : (23/31 : ℝ) < 1) 128
  norm_num [Finset.sum_range_succ, pow_succ] at h
  norm_num [s3Base5]
  linarith

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig