import Hf4DEDensity
noncomputable section
namespace Hf4DE
open Real
theorem old_d0Paid_lt : SigmaRemaining.d0Paid < (858467/5000000:ℝ) := by
  norm_num [SigmaRemaining.d0Paid, SigmaExistingLogError.aCoeff,SigmaExistingLogError.bCoeff,SigmaExistingLogError.cCoeff,SigmaExistingLogError.rationalPart,SigmaExistingLogError.ua,SigmaExistingLogError.ub,SigmaExistingLogError.uc,OriginalSigmaCubicRestoration.ca,OriginalSigmaCubicRestoration.cb,OriginalSigmaCubicRestoration.cc,OriginalSigmaCubicRestoration.cd, RemainingHf.splitLower,RemainingHf.splitUpper,Wu04FactorEnvelopes.leftFactor,Wu04FactorEnvelopes.rightFactor,RemainingHf.basicLower, RemainingHf.basicUpper, Wu2008DoubleSieve.JointLogTotalComparison.V, Wu2008DoubleSieve.SharpLogRecurrence.lowerLog, Wu2008DoubleSieve.SharpLogRecurrence.upperLog, F1FullRecoveryPayment.lowerGapPayment, F1FullRecoveryPayment.upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom]

theorem dPaid_eq_fullMass : D0FullDensity.dPaid = D0FullDensity.fullMass := by
  exact max_eq_right (old_d0Paid_lt.le.trans fullMass_bounds.1)

theorem dPaid_bounds : (858467/5000000 : ℝ) ≤ D0FullDensity.dPaid ∧
    D0FullDensity.dPaid ≤ 17169341/100000000 := by
  rw [dPaid_eq_fullMass]
  exact fullMass_bounds

end Hf4DE
