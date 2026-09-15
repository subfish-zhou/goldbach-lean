import SigmaVariationFiniteTerminal

noncomputable section
namespace SigmaEndpointPayment
open Real NodeExtension FirstFeedbackIntegrals

/-- The finite amount is debited from the actual original unpaid hf4 ledger. -/
theorem finite_payment_le_original_unpaid :
    RemainingHf.splitLower 2 * finiteVariation NineFeedbackStrength.originalH /
      (1-D0FullDensity.finiteD) ≤ CorrectionD0Joint.allUnpaid := by
  have h := finiteTerminal_le_actual
  rw [finiteTerminal_balance,CorrectionD0Joint.actual_terminal_balance] at h
  linarith only [h]

end SigmaEndpointPayment
