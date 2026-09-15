import F1OriginalEPayment

noncomputable section
open Real Wu2008DoubleSieve SharpLogRecurrence FirstCRationalPayment
open F1FullRecoveryPayment F1RemainingRecovery F1UnpaidRecovery F1FixedSquareRecovery
namespace F1OriginalEPayment

def payment : ℝ := ((1327/200)-6)^5/
  (60*((1327/200)-4)^2*((1327/200)-3)*((1327/200)-2)*((1327/200)-1))
theorem payment_pos : 0 < payment := by norm_num [payment]
theorem payment_le : payment ≤ Wu08OriginalFirstSteps.E (1327/200) :=
  E_lower (by norm_num)

/-- Fully explicit coefficient: replace the old symbolic E, do not add a second E. -/
def coefficient : ℝ := (14900897:ℝ)/1000000-
  8*(F1SecondLogRecovery.remainingDebit-payment)

theorem coefficient_le_actual : coefficient ≤ Wu08TerminalAlignment.firstMain := by
  have hgap := F1SecondLogRecovery.actual_gap
  have hk := F1SecondLogRecovery.remaining_kernel_nonneg
  have hl := F1LowerResidual.logPaymentExtra_le
  have he := payment_le
  unfold coefficient F1SecondLogRecovery.remainingDebit
  linarith only [hgap,hk,hl,he]

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

end F1OriginalEPayment
