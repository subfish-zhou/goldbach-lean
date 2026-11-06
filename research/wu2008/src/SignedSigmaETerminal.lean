import SigmaSignedCoupledForm
import TerminalESignedLedger
namespace SignedSigmaETerminal
open Real FirstFeedbackIntegrals ActualNineFeedback
noncomputable section

theorem logPayment_nonneg : 0 ≤ RemainingHf.splitLower 2 := by
  norm_num [RemainingHf.splitLower,RemainingHf.basicLower,
    Wu04FactorEnvelopes.leftFactor,Wu04FactorEnvelopes.rightFactor,
    Wu2008DoubleSieve.SharpLogRecurrence.lowerLog,Wu2008DoubleSieve.SharpLogRecurrence.upperLog,
    F1FullRecoveryPayment.lowerGapPayment,F1LowerResidual.payment,F1LowerResidual.denom]

def lower : ℝ := RemainingHf.splitLower 2*SigmaSignedCells.profileLower+
  TerminalESigned.massPaid NineFeedbackStrength.originalH

theorem lower_le_actual : lower ≤ firstFeedback NineFeedbackStrength.originalH 3 3 := by
  have hs := mul_le_mul_of_nonneg_left SigmaSignedCells.profileLower_le_primitive logPayment_nonneg
  have he := le_max_right (RemainingHf.paidCells NineFeedbackStrength.originalH 3)
    (TerminalESigned.massPaid NineFeedbackStrength.originalH)
  have h := TerminalESigned.jointFiniteLower_le_actual
  unfold lower TerminalESigned.jointFiniteLower at *
  linarith only [hs,he,h]

/-- The new rational sigma remainder is still an actual integral, not a paid constant. -/
def correctedLower : ℝ := RemainingHf.splitLower 2*SigmaSignedCells.correctedProfile+
  TerminalESigned.massPaid NineFeedbackStrength.originalH


end
end SignedSigmaETerminal
