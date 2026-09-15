import F1FixedSquareConsumption

noncomputable section
open Real Wu2008DoubleSieve SharpLogRecurrence FirstCRationalPayment
open F1RemainingRecovery F1UnpaidRecovery
namespace F1FixedSquareRecovery

/-- Original log payment, two kernel factors and E are inherited, each exactly once. -/
def coefficient : ℝ := F1UnpaidRecovery.coefficient+8*combinedSquarePayment

theorem coefficient_stronger : F1UnpaidRecovery.coefficient < coefficient := by
  unfold coefficient
  linarith only [combinedSquarePayment_pos]

theorem coefficient_le_actual : coefficient ≤ Wu08TerminalAlignment.firstMain := by
  rw [FirstActualRecovery.actual_first_recoveries]
  unfold coefficient F1UnpaidRecovery.coefficient F1KernelUpperAssembly.coefficient
  linarith only [F1KernelUpperAssembly.logPayment_le,square_le_unpaid_kernel_residual]

/-- True log residual and the original E stay in the same joint balance. -/
theorem recovered_joint_balance :
    combinedSquarePayment+(logRecovery-F1KernelUpperAssembly.logPayment)+
      Wu08OriginalFirstSteps.E (1327/200) ≤
    (logRecovery-F1KernelUpperAssembly.logPayment)+
      (FirstActualRecovery.kernelRecovery-momentPayment-unpaidFactorPayment)+
      Wu08OriginalFirstSteps.E (1327/200) := by
  linarith only [square_le_unpaid_kernel_residual]

/-- No residual is identified with a lower bound or paid twice. -/
theorem actual_gap : (14900897:ℝ)/1000000-Wu08TerminalAlignment.firstMain =
    8*((F1KernelUpperAssembly.debit-unpaidFactorPayment-combinedSquarePayment)-
      (logRecovery-F1KernelUpperAssembly.logPayment)-
      (FirstActualRecovery.kernelRecovery-momentPayment-unpaidFactorPayment-
        combinedSquarePayment)-Wu08OriginalFirstSteps.E (1327/200)) := by
  rw [F1UnpaidRecovery.actual_gap]
  ring

/-- Unconditional improved count, still with the same actual E. -/
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
      (Wu08TerminalAlignment.firstMain-coefficient+ε) = coefficient-ε := by ring
  simpa only [hid] using h N hN hEven

end F1FixedSquareRecovery
