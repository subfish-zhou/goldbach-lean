import ActualQTotalEnclosure
import SixthFullRationalEnclosure

namespace Wu2008DoubleSieve.RefinedActualQComparison
open Real
noncomputable section

/-- Explicit rational endpoints for the original actual target difference. -/
def floor : ℝ := 7/50-1/200-1/20-1/100-1/100000-1/100000-
  7/400-FourActualCapRecovery.recovery/4-(9007/100000)/4-(2258/10000)/4-23121/400000

def ceiling : ℝ := 3/20-3/10000-FourActualCapRecovery.recovery/4-
  (2539/100000)/4-(652/10000)/4

/-- Every upper error bound, including the improved full sixth bound, is charged once. -/
theorem actual_difference_bounds :
    floor < AnalyticTotalThreshold.target-JointHMotherPayment.unroundedCoefficient ∧
    AnalyticTotalThreshold.target-JointHMotherPayment.unroundedCoefficient < ceiling := by
  have he := JointSharedTightEnclosure.target_exact_difference
  have hq := ActualQTotalEnclosure.actual_error_interval
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
end Wu2008DoubleSieve.RefinedActualQComparison
