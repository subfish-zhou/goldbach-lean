import F1FullLogPayment

noncomputable section
open Wu2008DoubleSieve SharpLogRecurrence FirstCRationalPayment
namespace F1FullRecoveryPayment

/-- Exact size statement for the fixed original debit, not a new target. -/
theorem payment_covers_nine_tenths :
    9*rationalPublicationDebit ≤ 10*fullLogRecoveryPayment := by
  norm_num [fullLogRecoveryPayment,fourLowerRecoveryPayment,
    lowerGapPayment,upperGapPayment,upperLog,lowerLog,
    residueA,residueB,residueC,residueD,rationalPublicationDebit]

/-- At least nine tenths of the original rational debit is now actually paid. -/
theorem actual_logRecovery_covers_nine_tenths :
    (9/10:ℝ)*rationalPublicationDebit ≤ logRecovery := by
  linarith only [payment_covers_nine_tenths,fullLogRecoveryPayment_le_logRecovery]

/-- The unpaid certificate is strictly positive but at most one tenth of the old debit. -/
theorem unpaid_debit_extent :
    0 < unpaidPublicationDebit ∧ unpaidPublicationDebit ≤ rationalPublicationDebit/10 := by
  refine ⟨unpaidPublicationDebit_positive,?_⟩
  unfold unpaidPublicationDebit
  linarith only [payment_covers_nine_tenths]

end F1FullRecoveryPayment
