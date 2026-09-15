import FreshRemainingFactors

noncomputable section
open Real Wu2008DoubleSieve SharpLogRecurrence Wu08OriginalFirstSteps FirstCRationalPayment
namespace FreshCommonLog

def logLoss : ℝ := collected-lower
def eLoss : ℝ := E (1327/200)-EJoint.payment
def unpaid : ℝ := logLoss+FreshRemainingFactors.mass+eLoss

theorem logLoss_nonneg : 0 ≤ logLoss := sub_nonneg.mpr lower_le_collected
theorem eLoss_nonneg : 0 ≤ eLoss := sub_nonneg.mpr EJoint.payment_le
theorem unpaid_nonneg : 0 ≤ unpaid :=
  add_nonneg (add_nonneg logLoss_nonneg FreshRemainingFactors.mass_nonneg) eLoss_nonneg

theorem collected_budget : collected = signedMainLogs+F1BFullFTC.cPayment+
    FreshFTCJoint.exactMass+EJoint.payment := by
  rw [← collected_exact]
  unfold FreshFTCJoint.joint
  rw [← F1BFullFTC.collectedJoint_exact,F1BFullFTC.jointMass_exact]
  ring

/-- Exact original coefficient: the E payment and all eight C kernels are used once. -/
theorem firstMain_exact : Wu08TerminalAlignment.firstMain = 8*(lower+unpaid) := by
  rw [FirstActualRecovery.actual_first_recoveries,← finiteMainPayment_exact,
    FreshFTCJoint.recovery_exact]
  unfold unpaid logLoss eLoss
  rw [FreshRemainingFactors.mass_exact,collected_budget]
  unfold logRecovery
  ring

def publicationDebit : ℝ := (14900897:ℝ)/8000000-lower

/-- This is the remaining obligation, not a proof that the debit has been paid. -/
theorem publication_iff : (14900897:ℝ)/1000000 ≤ Wu08TerminalAlignment.firstMain ↔
    publicationDebit ≤ unpaid := by
  rw [firstMain_exact]
  unfold publicationDebit
  constructor <;> intro h <;> linarith only [h]
end FreshCommonLog
