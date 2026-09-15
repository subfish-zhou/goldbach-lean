import F1UpperGapPayment

noncomputable section
open Real Wu2008DoubleSieve SharpLogRecurrence FirstCRationalPayment
namespace F1FullRecoveryPayment

/-- All seven original logarithmic errors contribute with their actual paying signs. -/
def fullLogRecoveryPayment : ℝ := fourLowerRecoveryPayment+
  (-1-residueB)*(upperGapPayment 2+upperGapPayment (3/2))-
  residueD*upperGapPayment (4508/3981)

/-- Quantitative, unconditional payment from the literal original logRecovery. -/
theorem fullLogRecoveryPayment_le_logRecovery :
    fullLogRecoveryPayment ≤ logRecovery := by
  obtain ⟨ha,hac,hb,hb1,hd⟩ := residue_signs
  have h2 := mul_le_mul_of_nonpos_left
    (add_le_add (upperGapPayment_le (by norm_num : (1:ℝ) ≤ 2))
      (upperGapPayment_le (by norm_num : (1:ℝ) ≤ 3/2))) hb1
  have hbase := lowerGapPayment_le (by norm_num : (1:ℝ) ≤ 1127/600)
  have hcommon := mul_le_mul_of_nonneg_left
    (lowerGapPayment_le (by norm_num : (1:ℝ) ≤ 3884129/3606400)) ha
  have haclog := mul_le_mul_of_nonneg_left
    (lowerGapPayment_le (by norm_num : (1:ℝ) ≤ 4508/2927)) hac
  have hnear := mul_le_mul_of_nonpos_left
    (lowerGapPayment_le (by norm_num : (1:ℝ) ≤ 2400/2381)) hb
  have hdlog := mul_le_mul_of_nonpos_left
    (upperGapPayment_le (by norm_num : (1:ℝ) ≤ 4508/3981)) hd
  unfold fullLogRecoveryPayment fourLowerRecoveryPayment logRecovery signedMainLogs finiteMainPayment
  linarith only [h2,hbase,hcommon,haclog,hnear,hdlog]

theorem fourLowerRecoveryPayment_lt_fullLogRecoveryPayment :
    fourLowerRecoveryPayment < fullLogRecoveryPayment := by
  unfold fullLogRecoveryPayment
  have h : 0 < (-1-residueB)*(upperGapPayment 2+upperGapPayment (3/2))-
      residueD*upperGapPayment (4508/3981) := by
    norm_num [residueB,residueD,upperGapPayment]
  linarith only [h]

/-- Publication debit after this actual payment, not a necessary lower-kernel condition. -/
def unpaidPublicationDebit : ℝ := rationalPublicationDebit-fullLogRecoveryPayment

theorem unpaidPublicationDebit_positive : 0 < unpaidPublicationDebit := by
  norm_num [unpaidPublicationDebit,fullLogRecoveryPayment,fourLowerRecoveryPayment,
    lowerGapPayment,upperGapPayment,upperLog,lowerLog,
    residueA,residueB,residueC,residueD,rationalPublicationDebit]

/-- Original first coefficient, retaining both actual integral recoveries exactly once. -/
theorem actual_first_full_log_payment :
    8*(rationalMainPayment+fullLogRecoveryPayment+
      FirstActualRecovery.kernelRecovery+Wu08OriginalFirstSteps.E (1327/200)) ≤
      Wu08TerminalAlignment.firstMain := by
  rw [FirstActualRecovery.actual_first_recoveries]
  linarith only [fullLogRecoveryPayment_le_logRecovery]

/-- A quantitative bound on the original gap, not on a newly chosen lower kernel. -/
theorem actual_publication_gap_upper :
    (14900897:ℝ)/1000000-Wu08TerminalAlignment.firstMain ≤
      8*(unpaidPublicationDebit-FirstActualRecovery.kernelRecovery-
        Wu08OriginalFirstSteps.E (1327/200)) := by
  rw [FirstActualRecovery.actual_publication_gap]
  unfold unpaidPublicationDebit
  linarith only [fullLogRecoveryPayment_le_logRecovery]

end F1FullRecoveryPayment
