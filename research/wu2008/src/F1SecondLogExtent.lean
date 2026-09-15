import F1SecondLogAssembly

noncomputable section
open Real Wu2008DoubleSieve SharpLogRecurrence FirstCRationalPayment
open F1FullRecoveryPayment F1RemainingRecovery F1UnpaidRecovery F1FixedSquareRecovery
namespace F1SecondLogRecovery

/-- Literal unpaid rational certificate; not an assertion about the sign of actual F1. -/
def remainingDebit : ℝ := F1KernelUpperAssembly.debit-unpaidFactorPayment-
  combinedSquarePayment-F1LowerResidual.logPaymentExtra-secondPayment

theorem remainingDebit_pos : 0 < remainingDebit := by
  unfold remainingDebit
  rw [show F1KernelUpperAssembly.debit = rationalPublicationDebit-
    F1KernelUpperAssembly.logPayment-momentPayment by rfl]
  rw [momentPayment_exact,unpaidFactorPayment_exact]
  unfold combinedSquarePayment
  rw [squarePayment_exact]
  norm_num [F1KernelUpperAssembly.logPayment,fourLowerRecoveryPayment,
    upperTwoPayment,upperGapPayment,lowerGapPayment,upperLog,lowerLog,
    residueA,residueB,residueC,residueD,rationalPublicationDebit,secondFactorRatio,
    F1LowerResidual.logPaymentExtra,F1LowerResidual.payment,F1LowerResidual.denom,
    secondPayment,massW,massQOne,massQTwo]

/-- The new mass is paid from the same original C; all old charges have been removed once. -/
theorem remaining_kernel_nonneg : 0 ≤ FirstActualRecovery.kernelRecovery-
    momentPayment-unpaidFactorPayment-combinedSquarePayment-secondPayment := by
  linarith only [secondPayment_le_actual_residual]

end F1SecondLogRecovery
