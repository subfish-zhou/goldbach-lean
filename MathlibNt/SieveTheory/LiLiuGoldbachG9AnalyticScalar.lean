import MathlibNt.SieveTheory.LiLiuGoldbachG9AnalyticLogBounds

open Finset
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.G9Analytic
set_option maxHeartbeats 32000000
set_option maxRecDepth 100000

theorem endpoints_le_target : endpointExpression ≤ (527231/100000 : ℝ) := by
  have h1 := scaled_log_bounds (by norm_num : (1:ℝ) ≤ 64/53) 4
  have h2 := scaled_log_bounds (by norm_num : (1:ℝ) ≤ 8/5) 4
  have h3 := scaled_log_bounds (by norm_num : (1:ℝ) ≤ 4/3) 2
  have h4 := scaled_log_bounds (by norm_num : (1:ℝ) ≤ 98/53) 1
  have h5 := scaled_log_bounds (by norm_num : (1:ℝ) ≤ 9/5) 1
  have h6 := scaled_log_bounds (by norm_num : (1:ℝ) ≤ 4/3) 1
  norm_num [logLower, logUpper, Finset.sum_range_succ] at h1 h2 h3 h4 h5 h6
  norm_num [endpointExpression, primitive1, primitive2, H1, H2]
  linarith only [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, h5.1, h5.2, h6.1, h6.2]

theorem actual_le_target : goldbachB9PaperSplitIntegral ≤ (527231/100000 : ℝ) :=
  actual_le_endpoints.trans endpoints_le_target

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.G9Analytic
