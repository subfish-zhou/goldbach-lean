import MathlibNt.SieveTheory.LiLiuGoldbachG67CenteredBridge
import MathlibNt.SieveTheory.LiLiuGoldbachG67CenteredEndpoint

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Both independently proved halves use the same frozen polynomial and loss. -/
theorem goldbachG67_piecewise_lower_certified :
    (54233/10000 : ℝ) ≤ 4*G67SumCoordinate.piecewiseIntegral := by
  have h := G67CenteredEvaluation.centered_endpoint_bound.trans
    G67CenteredEnvelope.polynomialIntegral_sub_errorBudget_le_piecewiseIntegral
  linarith only [h]

theorem goldbachG67IntegralConstant_lower_certified :
    (54233/10000 : ℝ) ≤ goldbachG67IntegralConstant :=
  goldbachG67_piecewise_lower_certified.trans G67SumCoordinate.actual_constant_lower_piecewise

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
