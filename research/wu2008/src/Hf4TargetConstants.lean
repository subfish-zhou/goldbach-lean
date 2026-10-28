import Hf4RadicalBounds
import Hf4FullProfile

noncomputable section
namespace Hf4Target
open Real

theorem original_threshold : NineFeedbackStrength.originalH 8 = (72943/10000000 : ℝ) := by
  change (0.0072943 : ℝ) = 72943/10000000
  norm_num

theorem log_two_bounds : (6931/10000 : ℝ) < log 2 ∧ log 2 < 6932/10000 := by
  have hL := RemainingHf.splitLower_le (by norm_num : (1 : ℝ) ≤ 2)
  have hU := (Wu04WholeCollection.bounds (x := 2) (by norm_num)).2
  norm_num [RemainingHf.splitLower, RemainingHf.basicLower,
    Wu04FactorEnvelopes.leftFactor, Wu04FactorEnvelopes.rightFactor,
    Wu2008DoubleSieve.SharpLogRecurrence.lowerLog,
    Wu2008DoubleSieve.SharpLogRecurrence.upperLog,
    F1FullRecoveryPayment.lowerGapPayment, F1LowerResidual.payment,
    F1LowerResidual.denom] at hL
  norm_num [Wu04WholeCollection.up, Wu04FactorEnvelopes.upper,
    Wu04FactorEnvelopes.leftFactor, Wu04FactorEnvelopes.rightFactor,
    Wu2008DoubleSieve.SharpLogRecurrence.lowerLog,
    Wu2008DoubleSieve.SharpLogRecurrence.upperLog,
    Wu2008DoubleSieve.JointLogTotalComparison.V] at hU
  constructor <;> linarith only [hL,hU]

end Hf4Target
