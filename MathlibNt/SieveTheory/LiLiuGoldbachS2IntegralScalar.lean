import MathlibNt.SieveTheory.LiLiuGoldbachSmallEpsilon

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- A fixed six-term logarithm estimate, certified by an analytic remainder. -/
theorem goldbachS2_g3_scalar_le_84289 :
    8 * Real.log (10/9 : ℝ) ≤ (84289/100000 : ℝ) := by
  have h := Real.log_div_le_sum_range_add
    (by norm_num : (0 : ℝ) ≤ 1/19) (by norm_num : (1/19 : ℝ) < 1) 6
  norm_num [Finset.sum_range_succ] at h
  linarith


end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig