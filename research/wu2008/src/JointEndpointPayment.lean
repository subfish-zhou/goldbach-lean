import TotalEndpointComparison
import JointJLossStrength

namespace Wu2008DoubleSieve.JointEndpointPayment
open Real
noncomputable section

/-- Restore the genuine ninth integral error on top of the jointly compared endpoints. -/
def analyticLower : ℝ :=
  TotalEndpointComparison.affineTotal + JointJLossStrength.recovery/4

def fixedRecoveryLower : ℝ :=
  TotalEndpointComparison.affineTotal + JointJLossStrength.fixedRecovery/4

/-- Strictness is supplied by the retained positive endpoint square, not by a target hypothesis. -/
theorem analyticLower_lt_actual :
    analyticLower < JointHMotherPayment.unroundedCoefficient := by
  have hs := TotalEndpointComparison.affineTotal_lt_coefficient
  have hj := JointJLossStrength.strengthened_coefficient_lower
  unfold analyticLower
  linarith only [hs,hj]

theorem fixedRecoveryLower_lt_actual :
    fixedRecoveryLower < JointHMotherPayment.unroundedCoefficient := by
  have hs := TotalEndpointComparison.affineTotal_lt_coefficient
  have hj := JointJLossStrength.fixed_coefficient_lower
  unfold fixedRecoveryLower
  linarith only [hs,hj]

/-- Each coefficient spends its own full positive gap in the same accepted count family. -/
theorem full_analytic_count : CorrelationPayment.CountBound analyticLower :=
  CorrelationPayment.pay analyticLower_lt_actual

theorem full_fixed_recovery_count : CorrelationPayment.CountBound fixedRecoveryLower :=
  CorrelationPayment.pay fixedRecoveryLower_lt_actual

theorem strict_gain_over_restored :
    SharedRationalPayment.residualCoefficient + Phase20.psiPaymentLoss +
      JointJLossStrength.fixedRecovery/4 < fixedRecoveryLower := by
  have h := TotalEndpointComparison.restored_certificate_lt_affineTotal
  unfold fixedRecoveryLower
  linarith only [h]

theorem fixed_le_analytic : fixedRecoveryLower ≤ analyticLower := by
  have h := JointJLossStrength.fixedRecovery_le_recovery
  unfold fixedRecoveryLower analyticLower
  linarith only [h]

/-- Exact remaining margin against the fully recovered endpoint certificate. -/
theorem exact_square_gap :
    AnalyticTotalThreshold.coefficient + JointJLossStrength.recovery/4 - analyticLower =
      TotalEndpointComparison.quad/4 *
        (TotalEndpointComparison.D-FifthClassicalShape.ell)^2 := by
  unfold analyticLower
  have h := TotalEndpointComparison.total_square_identity
  linarith only [h]

end
end Wu2008DoubleSieve.JointEndpointPayment
