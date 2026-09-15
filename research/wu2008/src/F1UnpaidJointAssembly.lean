import F1UnpaidMomentConsumption

noncomputable section
open Real Wu2008DoubleSieve SharpLogRecurrence FirstCRationalPayment
open F1RemainingRecovery
namespace F1UnpaidRecovery

/-- Exact fixed algebra of the new original-kernel recovery. -/
theorem unpaidFactorPayment_exact : unpaidFactorPayment =
    (30071900433102871455920998624051995806:ℝ)/
      11515701215675088882459300338015727272549021 := by
  unfold unpaidFactorPayment
  rw [momentPayment_exact]
  norm_num [secondFactorRatio]

/-- Both old payments and the new unpaid-factor payment; original E is retained once. -/
def coefficient : ℝ := F1KernelUpperAssembly.coefficient+8*unpaidFactorPayment

theorem coefficient_stronger : F1KernelUpperAssembly.coefficient < coefficient := by
  unfold coefficient
  linarith only [unpaidFactorPayment_pos]

theorem coefficient_le_actual : coefficient ≤ Wu08TerminalAlignment.firstMain := by
  rw [FirstActualRecovery.actual_first_recoveries]
  unfold coefficient F1KernelUpperAssembly.coefficient
  linarith only [F1KernelUpperAssembly.logPayment_le,unpaid_factor_le_kernel_residual]

/-- The new payment leaves the actual log residual and E untouched, not replaced. -/
theorem joint_balance_lower :
    unpaidFactorPayment+(logRecovery-F1KernelUpperAssembly.logPayment)+
      Wu08OriginalFirstSteps.E (1327/200) ≤
    (logRecovery-F1KernelUpperAssembly.logPayment)+
      (FirstActualRecovery.kernelRecovery-momentPayment)+
      Wu08OriginalFirstSteps.E (1327/200) := by
  linarith only [unpaid_factor_le_kernel_residual]

/-- The remaining original joint balance, after an actual new payment exactly once. -/
theorem actual_gap : (14900897:ℝ)/1000000-Wu08TerminalAlignment.firstMain =
    8*((F1KernelUpperAssembly.debit-unpaidFactorPayment)-
      (logRecovery-F1KernelUpperAssembly.logPayment)-
      (FirstActualRecovery.kernelRecovery-momentPayment-unpaidFactorPayment)-
      Wu08OriginalFirstSteps.E (1327/200)) := by
  rw [F1KernelUpperAssembly.actual_gap]
  ring

/-- Unconditional improved count on the same original sieve-count carrier. -/
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

end F1UnpaidRecovery
