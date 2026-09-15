import F1SecondLogConsumption

noncomputable section
open Real Wu2008DoubleSieve SharpLogRecurrence FirstCRationalPayment
open F1RemainingRecovery F1UnpaidRecovery F1FixedSquareRecovery
namespace F1SecondLogRecovery

/-- Parent's true log residual and E stay present exactly once. -/
def coefficient : ℝ := F1LowerResidual.coefficient+8*secondPayment

theorem coefficient_stronger : F1LowerResidual.coefficient < coefficient := by
  unfold coefficient
  linarith only [secondPayment_pos]

theorem coefficient_le_actual : coefficient ≤ Wu08TerminalAlignment.firstMain := by
  rw [FirstActualRecovery.actual_first_recoveries]
  unfold coefficient F1LowerResidual.coefficient F1FixedSquareRecovery.coefficient
    F1UnpaidRecovery.coefficient F1KernelUpperAssembly.coefficient
  linarith only [F1LowerResidual.logPaymentExtra_le,secondPayment_le_actual_residual]

/-- All remaining original errors remain in a single balance, not individually required to pay. -/
theorem actual_gap : (14900897:ℝ)/1000000-Wu08TerminalAlignment.firstMain =
    8*((F1KernelUpperAssembly.debit-unpaidFactorPayment-combinedSquarePayment-
          F1LowerResidual.logPaymentExtra-secondPayment)-
      (logRecovery-F1KernelUpperAssembly.logPayment-F1LowerResidual.logPaymentExtra)-
      (FirstActualRecovery.kernelRecovery-momentPayment-unpaidFactorPayment-
        combinedSquarePayment-secondPayment)-Wu08OriginalFirstSteps.E (1327/200)) := by
  rw [F1LowerResidual.actual_gap]
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

end F1SecondLogRecovery
