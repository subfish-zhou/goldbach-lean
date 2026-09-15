import EJointMoments
noncomputable section
open Real Wu2008DoubleSieve SharpLogRecurrence FirstCRationalPayment
open F1FullRecoveryPayment F1RemainingRecovery F1UnpaidRecovery F1FixedSquareRecovery
namespace EJoint

/-- The joint E payment replaces the coarse E, and is not added to an E-bearing coefficient. -/
def remainingDebit : ℝ := F1SecondLogRecovery.remainingDebit-payment

def coefficient : ℝ := (14900897:ℝ)/1000000-8*remainingDebit

theorem coefficient_le_actual : coefficient ≤ Wu08TerminalAlignment.firstMain := by
  have hgap := F1SecondLogRecovery.actual_gap
  have hk := F1SecondLogRecovery.remaining_kernel_nonneg
  have hl := F1LowerResidual.logPaymentExtra_le
  have he := payment_le
  unfold coefficient remainingDebit F1SecondLogRecovery.remainingDebit
  linarith only [hgap,hk,hl,he]

theorem coefficient_stronger : F1OriginalEPayment.coefficient < coefficient := by
  have h := payment_stronger
  unfold F1OriginalEPayment.coefficient coefficient remainingDebit
  linarith only [h]

/-- The remaining burden is shared by the actual log, C, and E residuals. -/
def commonResidual : ℝ :=
    (logRecovery-F1KernelUpperAssembly.logPayment-F1LowerResidual.logPaymentExtra)+
    (FirstActualRecovery.kernelRecovery-momentPayment-unpaidFactorPayment-
      combinedSquarePayment-F1SecondLogRecovery.secondPayment)+
    (Wu08OriginalFirstSteps.E (1327/200)-payment)

theorem commonResidual_nonneg : 0 ≤ commonResidual := by
  have hk := F1SecondLogRecovery.remaining_kernel_nonneg
  have hl := F1LowerResidual.logPaymentExtra_le
  have he := payment_le
  unfold commonResidual
  linarith only [hk,hl,he]

theorem actual_joint_gap : (14900897:ℝ)/1000000-Wu08TerminalAlignment.firstMain =
    8*(remainingDebit-commonResidual) := by
  have h := F1SecondLogRecovery.actual_gap
  unfold remainingDebit commonResidual F1SecondLogRecovery.remainingDebit
  linarith only [h]

theorem original_target_iff : (14900897:ℝ)/1000000 ≤ Wu08TerminalAlignment.firstMain ↔
    remainingDebit ≤ commonResidual := by
  have h := actual_joint_gap
  constructor <;> intro hh <;> linarith only [h,hh]

theorem actual_count {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (coefficient-ε)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
        (sieveCount N 1 N ((N : ℝ)^truncatedSixthLowerAlpha) : ℝ) := by
  have he : 0 < Wu08TerminalAlignment.firstMain-coefficient+ε := by
    linarith only [coefficient_le_actual,hε]
  obtain ⟨T,hT,h⟩ := Wu08TerminalAlignment.first_actual_count he
  refine ⟨T,hT,?_⟩
  intro N hN hEven
  have hid : Wu08TerminalAlignment.firstMain-
      (Wu08TerminalAlignment.firstMain-coefficient+ε)=coefficient-ε := by ring
  simpa only [hid] using h N hN hEven

end EJoint
