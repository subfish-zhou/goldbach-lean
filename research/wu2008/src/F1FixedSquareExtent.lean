import F1FixedSquareAssembly

noncomputable section
open Real Wu2008DoubleSieve SharpLogRecurrence FirstCRationalPayment
open F1FullRecoveryPayment F1RemainingRecovery F1UnpaidRecovery F1FixedSquareRecovery
namespace F1FixedSquareRecovery

/-- The fixed paid rational terms do not suffice alone. This says nothing negative about
    the original target: the actual log residual, kernel residual and E remain unpaid. -/
theorem remaining_rational_debit_pos :
    0 < F1KernelUpperAssembly.debit-unpaidFactorPayment-combinedSquarePayment := by
  rw [show F1KernelUpperAssembly.debit = rationalPublicationDebit-
    F1KernelUpperAssembly.logPayment-momentPayment by rfl]
  rw [momentPayment_exact,unpaidFactorPayment_exact]
  unfold combinedSquarePayment
  rw [squarePayment_exact]
  norm_num [F1KernelUpperAssembly.logPayment,fourLowerRecoveryPayment,
    upperTwoPayment,upperGapPayment,lowerGapPayment,upperLog,lowerLog,
    residueA,residueB,residueC,residueD,rationalPublicationDebit,secondFactorRatio]

end F1FixedSquareRecovery
