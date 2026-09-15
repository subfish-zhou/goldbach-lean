import JointSharedTightEnclosure
import JFourRemainingMagnitude

namespace Wu2008DoubleSieve.ActualQTotalEnclosure
open Real
noncomputable section

/-- The remaining error of the actual Q after the complete triple and fifth-log restorations. -/
theorem actual_error_interval :
    0 ≤ JointHMotherPayment.unroundedCoefficient-JointSharedTightEnclosure.coefficient ∧
    JointHMotherPayment.unroundedCoefficient-JointSharedTightEnclosure.coefficient < 23121/400000 := by
  have he := JointSharedTightEnclosure.remaining_error_exact
  have hj := JFourRemainingMagnitude.actual_residual_magnitude
  have h5 := FifthActualIntegralRecovery.unpaid_fifth_quarter
  have h6 := ClassicalLossBottleneck.unpaid_sixth_quarter_cap
  unfold JFourRemainingMagnitude.jRemaining JFourRemainingMagnitude.fourRemaining at hj
  constructor <;> linarith only [he,hj.1,hj.2,h5.1,h5.2,h6.1,h6.2]

/-- A genuine two-sided enclosure of Q itself, not a claim that a lower certificate is too small. -/
theorem actual_q_enclosure :
    JointSharedTightEnclosure.coefficient ≤ JointHMotherPayment.unroundedCoefficient ∧
    JointHMotherPayment.unroundedCoefficient < JointSharedTightEnclosure.coefficient+23121/400000 := by
  constructor <;> linarith only [actual_error_interval.1,actual_error_interval.2]

/-- The target interval still crosses zero: neither threshold direction is asserted. -/
theorem actual_target_interval :
    -(55121/400000:ℝ) < AnalyticTotalThreshold.target-JointHMotherPayment.unroundedCoefficient ∧
    AnalyticTotalThreshold.target-JointHMotherPayment.unroundedCoefficient < 63/500 := by
  have hc := JointSharedTightEnclosure.total_target_localization
  have hq := actual_error_interval
  constructor <;> linarith only [hc.1,hc.2,hq.1,hq.2]

end
end Wu2008DoubleSieve.ActualQTotalEnclosure
