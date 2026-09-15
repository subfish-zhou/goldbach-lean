import SixthLogTotalMagnitude
import FourActualCapRecovery

namespace Wu2008DoubleSieve.JointSixthFourDiagnostic
open Real
noncomputable section

/-- Spend the full sixth-log recovery and the new Four recovery in the same mother identity. -/
def coefficient : ℝ := ClassicalLossBottleneck.recoveredCoefficient+FourActualCapRecovery.recovery/4

/-- Preserve the exact unrounded debit from the previous proof, rather than its coarser export. -/
theorem sixth_deficit_retained : (249/50000 : ℝ) <
    AnalyticTotalThreshold.target-ClassicalLossBottleneck.recoveredCoefficient := by
  have hD : (7/50:ℝ) < JointLogTotalComparison.rationalDeficit := by
    norm_num [JointLogTotalComparison.rationalDeficit]
  have hP := PsiG18Strength.two_recoveries_bounds.2
  have hL := SixthLogTotalMagnitude.log_remainder_cap.2
  have hJ := SixthLogTotalMagnitude.jextra_bounds.2
  have hT := SixthLogTotalMagnitude.target_slack_bounds.2
  have hS := SixthLogTotalMagnitude.square_bounds.2
  have h6 := SixthLogTotalMagnitude.sixth_loss_bounds.2
  rw [SixthLogTotalMagnitude.recovered_exact_difference]
  linarith only [hD,hP,hL,hJ,hT,hS,h6]

/-- Both recoveries consume different actual losses, so there is no addition of independent counts. -/
theorem coefficient_le_actual : coefficient ≤ JointHMotherPayment.unroundedCoefficient := by
  have hgap := AnalyticTotalThreshold.actual_gap_identity
  rw [AnalyticTotalThreshold.signed_loss_identity] at hgap
  have hs := AnalyticTotalThreshold.signed_losses_nonnegative
  have hl := AnalyticTotalThreshold.losses_nonnegative
  have hj := JointJLossStrength.actual_jLoss_lower
  have h6 := ClassicalLossBottleneck.sixth_recurrence_integral_cap.1
  have h4 := FourActualCapRecovery.actual_fourLoss_lower
  unfold coefficient ClassicalLossBottleneck.recoveredCoefficient
  unfold AnalyticTotalThreshold.sixthLoss at hgap h6
  linarith only [hgap,hs.1,hs.2.1,hs.2.2.2,hl.2.1,hj,h6,h4]

/-- An exact positive shortfall of this specific combined certificate, not an upper bound on Q. -/
def shortfall : ℝ := 249/50000-FourActualCapRecovery.recovery/4

theorem shortfall_exact : shortfall =
    209401394940962493932272408748851/37910419442290545827097474796579200000 := by
  unfold shortfall
  rw [FourActualCapRecovery.recovery_exact]
  norm_num

theorem shortfall_positive : 0 < shortfall := by rw [shortfall_exact]; norm_num

theorem certificate_strictly_insufficient :
    shortfall < AnalyticTotalThreshold.target-coefficient := by
  unfold shortfall coefficient
  linarith only [sixth_deficit_retained]

/-- The failure belongs to this lower certificate; actual Q remains unrestricted above it. -/
theorem coefficient_lt_target : coefficient < AnalyticTotalThreshold.target := by
  linarith only [certificate_strictly_insufficient,shortfall_positive]

end
end Wu2008DoubleSieve.JointSixthFourDiagnostic
