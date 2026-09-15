import F1UpperTwoRemainingPayment

namespace F1KernelUpperAssembly
open Real Wu2008DoubleSieve SharpLogRecurrence FirstCRationalPayment
open F1FullRecoveryPayment F1RemainingRecovery
noncomputable section

/-- Replace the old log(2) error payment; all other original log terms are unchanged. -/
def logPayment : ℝ := fourLowerRecoveryPayment+
  (-1-residueB)*(upperTwoPayment+upperGapPayment (3/2))-
  residueD*upperGapPayment (4508/3981)

theorem logPayment_le : logPayment ≤ logRecovery := by
  obtain ⟨ha,hac,hb,hb1,hd⟩ := residue_signs
  have h2 := mul_le_mul_of_nonpos_left
    (add_le_add upperTwoPayment_le (upperGapPayment_le (by norm_num : (1:ℝ) ≤ 3/2))) hb1
  have hbase := lowerGapPayment_le (by norm_num : (1:ℝ) ≤ 1127/600)
  have hcommon := mul_le_mul_of_nonneg_left
    (lowerGapPayment_le (by norm_num : (1:ℝ) ≤ 3884129/3606400)) ha
  have haclog := mul_le_mul_of_nonneg_left
    (lowerGapPayment_le (by norm_num : (1:ℝ) ≤ 4508/2927)) hac
  have hnear := mul_le_mul_of_nonpos_left
    (lowerGapPayment_le (by norm_num : (1:ℝ) ≤ 2400/2381)) hb
  have hdlog := mul_le_mul_of_nonpos_left
    (upperGapPayment_le (by norm_num : (1:ℝ) ≤ 4508/3981)) hd
  unfold logPayment fourLowerRecoveryPayment logRecovery signedMainLogs finiteMainPayment
  linarith only [h2,hbase,hcommon,haclog,hnear,hdlog]

theorem logPayment_stronger : fullLogRecoveryPayment < logPayment := by
  have hb : 0 < -1-residueB := by norm_num [residueB]
  have h := mul_lt_mul_of_pos_left upperTwoPayment_improves hb
  unfold logPayment fullLogRecoveryPayment
  linarith only [h]

/-- The literal unpaid certificate after both actual recoveries, not the actual F1 gap. -/
def debit : ℝ := rationalPublicationDebit-logPayment-momentPayment

def coefficient : ℝ := 8*(rationalMainPayment+logPayment+momentPayment+
  Wu08OriginalFirstSteps.E (1327/200))

theorem coefficient_le_actual : coefficient ≤ Wu08TerminalAlignment.firstMain := by
  rw [FirstActualRecovery.actual_first_recoveries]
  unfold coefficient
  linarith only [logPayment_le,momentPayment_le_kernelRecovery]

/-- Retain both true residuals and E, with each paid term removed only once. -/
theorem actual_gap : (14900897:ℝ)/1000000-Wu08TerminalAlignment.firstMain =
    8*(debit-(logRecovery-logPayment)-
      (FirstActualRecovery.kernelRecovery-momentPayment)-Wu08OriginalFirstSteps.E (1327/200)) := by
  rw [FirstActualRecovery.actual_publication_gap]
  unfold debit
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
  have hcancel : Wu08TerminalAlignment.firstMain-
      (Wu08TerminalAlignment.firstMain-coefficient+ε)=coefficient-ε := by ring
  simpa only [hcancel] using h N hN hEven

end
end F1KernelUpperAssembly
