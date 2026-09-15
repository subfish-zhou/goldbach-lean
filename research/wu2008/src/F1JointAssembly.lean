import F1JointConsumption

noncomputable section
open Real Wu2008DoubleSieve SharpLogRecurrence FirstCRationalPayment
open F1RemainingRecovery F1UnpaidRecovery F1FixedSquareRecovery F1SecondLogRecovery
namespace F1JointFTC

/-- The entire first rational FTC replaces, rather than duplicates, all its old payments. -/
def recovered : ℝ := (1+secondFactorRatio)*exactMass-
  (momentPayment+unpaidFactorPayment+combinedSquarePayment)

theorem recovered_nonneg : 0 ≤ recovered := sub_nonneg.mpr exactMass_covers_old

theorem recovered_le_commonResidual : recovered ≤ EJoint.commonResidual := by
  have hc := cPayment_le_actual
  have hl := F1LowerResidual.logPaymentExtra_le
  have he := EJoint.payment_le
  unfold cPayment at hc
  unfold recovered EJoint.commonResidual
  linarith only [hc,hl,he]

def coefficient : ℝ := EJoint.coefficient+8*recovered

theorem coefficient_le_actual : coefficient ≤ Wu08TerminalAlignment.firstMain := by
  have h := EJoint.actual_joint_gap
  have hr := recovered_le_commonResidual
  unfold coefficient EJoint.coefficient
  linarith only [h,hr]

theorem coefficient_ge_previous : EJoint.coefficient ≤ coefficient := by
  unfold coefficient
  linarith only [recovered_nonneg]

/-- The original log, C, and E residuals remain present with their actual signs. -/
theorem actual_joint_gap : (14900897:ℝ)/1000000-Wu08TerminalAlignment.firstMain =
    8*((EJoint.remainingDebit-recovered)-(EJoint.commonResidual-recovered)) := by
  rw [EJoint.actual_joint_gap]
  ring

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

end F1JointFTC
