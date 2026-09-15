import RefinedActualQComparison
import JCorrelatedResidualTight
import FourTrueLowerTight

namespace Wu2008DoubleSieve.TightActualQComparison
open Real
noncomputable section

/-- Actual remaining errors, each with its original quarter weight and no second payment. -/
theorem actual_error_interval :
    0 ≤ JointHMotherPayment.unroundedCoefficient-JointSharedTightEnclosure.coefficient ∧
    JointHMotherPayment.unroundedCoefficient-JointSharedTightEnclosure.coefficient < 4409/200000 := by
  have he := JointSharedTightEnclosure.remaining_error_exact
  have hj := JCorrelatedResidualTight.mother_J_error_interval
  have h4 := FourTrueLowerTight.mother_four_uncertainty
  have h5 := FifthActualIntegralRecovery.unpaid_fifth_quarter
  have h6 := ClassicalLossBottleneck.unpaid_sixth_quarter_cap
  unfold JFourRemainingMagnitude.fourRemaining at h4
  constructor <;> linarith only [he,hj.1,hj.2,h4.1,h4.2,h5.1,h5.2,h6.1,h6.2]


/-- Explicit rational endpoints for the original actual target difference. -/
def floor : ℝ := 7/50-1/200-1/20-1/100-1/100000-1/100000-
  7/400-FourActualCapRecovery.recovery/4-(9007/100000)/4-(2258/10000)/4-4409/200000

def ceiling : ℝ := 3/20-3/10000-FourActualCapRecovery.recovery/4-
  (2539/100000)/4-(652/10000)/4

/-- Every upper error bound, including the improved full sixth bound, is charged once. -/
theorem actual_difference_bounds :
    floor < AnalyticTotalThreshold.target-JointHMotherPayment.unroundedCoefficient ∧
    AnalyticTotalThreshold.target-JointHMotherPayment.unroundedCoefficient < ceiling := by
  have he := JointSharedTightEnclosure.target_exact_difference
  have hq := actual_error_interval
  have hd : (7/50:ℝ) < JointLogTotalComparison.rationalDeficit ∧
      JointLogTotalComparison.rationalDeficit < 3/20 := by
    norm_num [JointLogTotalComparison.rationalDeficit]
  have hp := PsiG18Strength.two_recoveries_bounds
  have hl := SixthLogTotalMagnitude.log_remainder_cap
  have hj := SixthLogTotalMagnitude.jextra_bounds
  have ht := SixthLogTotalMagnitude.target_slack_bounds
  have hs := SixthLogTotalMagnitude.square_bounds
  have h6n := SixthFullRationalEnclosure.sixth_log_loss_enclosure.1
  have h6u := SixthFullRationalEnclosure.sixth_log_loss_lt
  have h5 := FifthLogTotalMagnitude.recovery_decimal_rational_bounds
  have hb := JointSharedTightEnclosure.triple_magnitude
  unfold floor ceiling
  constructor <;> linarith only [he,hq.1,hq.2,hd.1,hd.2,hp.1,hp.2,hl.1,hl.2,hj.1,hj.2,
    ht.1,ht.2,hs.1,hs.2,h6n,h6u,h5.1,h5.2,hb.1,hb.2]

/-- These certified endpoints still straddle zero; no direction for Q versus target follows. -/
theorem endpoints_straddle_zero : floor < 0 ∧ 0 < ceiling := by
  unfold floor ceiling
  rw [FourActualCapRecovery.recovery_exact]
  norm_num

end
end Wu2008DoubleSieve.TightActualQComparison
