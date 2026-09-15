import F1LowerGapPayment

noncomputable section
open Real Wu2008DoubleSieve SharpLogRecurrence FirstCRationalPayment
namespace F1FullRecoveryPayment

/-- Paid part of the original logRecovery, not a replacement main term. -/
def fourLowerRecoveryPayment : ℝ :=
  lowerGapPayment (1127/600)+residueA*lowerGapPayment (3884129/3606400)+
  (residueA+residueC)*lowerGapPayment (4508/2927)-
  residueB*lowerGapPayment (2400/2381)

theorem fourLowerRecoveryPayment_le_logRecovery :
    fourLowerRecoveryPayment ≤ logRecovery := by
  obtain ⟨ha,hac,hb,hb1,hd⟩ := residue_signs
  have h2 := mul_le_mul_of_nonpos_left
    (add_le_add (JointLogTotalComparison.log_le_V (by norm_num : (1:ℝ) ≤ 2))
      (JointLogTotalComparison.log_le_V (by norm_num : (1:ℝ) ≤ 3/2))) hb1
  have hbase := lowerGapPayment_le (by norm_num : (1:ℝ) ≤ 1127/600)
  have hcommon := mul_le_mul_of_nonneg_left
    (lowerGapPayment_le (by norm_num : (1:ℝ) ≤ 3884129/3606400)) ha
  have haclog := mul_le_mul_of_nonneg_left
    (lowerGapPayment_le (by norm_num : (1:ℝ) ≤ 4508/2927)) hac
  have hnear := mul_le_mul_of_nonpos_left
    (lowerGapPayment_le (by norm_num : (1:ℝ) ≤ 2400/2381)) hb
  have hdlog := mul_le_mul_of_nonpos_left
    (JointLogTotalComparison.log_le_V (by norm_num : (1:ℝ) ≤ 4508/3981)) hd
  unfold fourLowerRecoveryPayment logRecovery signedMainLogs finiteMainPayment
  linarith only [h2,hbase,hcommon,haclog,hnear,hdlog]

/-- The paid amount is unconditional and strictly positive. -/
theorem fourLowerRecoveryPayment_pos : 0 < fourLowerRecoveryPayment := by
  norm_num [fourLowerRecoveryPayment,lowerGapPayment,upperLog,lowerLog,
    residueA,residueB,residueC]

/-- Actual firstMain receives this quantitative payment; C and E remain literal once. -/
theorem actual_first_quantitative_payment :
    8*(rationalMainPayment+fourLowerRecoveryPayment+
      FirstActualRecovery.kernelRecovery+Wu08OriginalFirstSteps.E (1327/200)) ≤
      Wu08TerminalAlignment.firstMain := by
  rw [FirstActualRecovery.actual_first_recoveries]
  linarith only [fourLowerRecoveryPayment_le_logRecovery]

/-- This payment does not exhaust the publication debit. It says nothing against actual F1. -/
theorem fourLowerRecoveryPayment_lt_debit :
    fourLowerRecoveryPayment < rationalPublicationDebit := by
  norm_num [fourLowerRecoveryPayment,lowerGapPayment,upperLog,lowerLog,
    residueA,residueB,residueC,rationalPublicationDebit]

end F1FullRecoveryPayment
