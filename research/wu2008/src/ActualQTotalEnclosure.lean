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



end
end Wu2008DoubleSieve.ActualQTotalEnclosure
