import MathlibNt.SieveTheory.LiLiuGoldbachG12EvaluationFTC
noncomputable section
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
namespace G12AnalyticCertificate
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000

/-- Fixed endpoint log estimates close the original rational envelope. -/
theorem rationalIntegral_le_target :
    (2*S3Correction.L (1/2))*endpoints ≤ (66821/100000 : ℝ) := by
  have h49 := (G9Analytic.log_bounds (by norm_num : (1 : ℝ) ≤ 49/33)).2
  have h36 := (G9Analytic.log_bounds (by norm_num : (1 : ℝ) ≤ 12/11)).1
  have h40 := (G9Analytic.log_bounds (by norm_num : (1 : ℝ) ≤ 40/33)).2
  norm_num [G9Analytic.logUpper, G9Analytic.logLower, Finset.sum_range_succ] at h49 h36 h40
  norm_num [endpoints, lowF, highF, lowH, highH, S3Correction.L]
  linarith only [h49, h36, h40]

/-- Unconditional bound for the production sharp G12 integral constant. -/
theorem actual_le_target : goldbachG12SharpIntegralConstant ≤ (66821/100000 : ℝ) := by
  apply sharp_le_rationalIntegral.trans
  rw [upperMass_eq_endpoints]
  exact rationalIntegral_le_target

end G12AnalyticCertificate
