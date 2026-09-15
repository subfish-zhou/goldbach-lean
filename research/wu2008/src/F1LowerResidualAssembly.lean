import F1LowerResidual

noncomputable section
open Real Wu2008DoubleSieve SharpLogRecurrence FirstCRationalPayment
open F1FullRecoveryPayment F1RemainingRecovery F1UnpaidRecovery F1FixedSquareRecovery
namespace F1LowerResidual

def logPaymentExtra : ℝ := payment (1127/600)+residueA*payment (3884129/3606400)+
  (residueA+residueC)*payment (4508/2927)-residueB*payment (2400/2381)

theorem logPaymentExtra_pos : 0 < logPaymentExtra := by
  obtain ⟨ha,hac,hb,_,_⟩ := residue_signs
  have h0 := payment_pos (by norm_num : (1:ℝ) < 1127/600)
  have h1 := mul_nonneg ha (payment_pos (by norm_num : (1:ℝ) < 3884129/3606400)).le
  have h2 := mul_nonneg hac (payment_pos (by norm_num : (1:ℝ) < 4508/2927)).le
  have h3 := mul_nonpos_of_nonpos_of_nonneg hb (payment_pos (by norm_num : (1:ℝ) < 2400/2381)).le
  unfold logPaymentExtra
  linarith only [h0,h1,h2,h3]

/-- Recombine all original signed terms; the older aggregate inequality is not subtracted. -/
theorem logPaymentExtra_le : logPaymentExtra ≤ logRecovery-F1KernelUpperAssembly.logPayment := by
  obtain ⟨ha,hac,hb,hb1,hd⟩ := residue_signs
  have h2 := mul_le_mul_of_nonpos_left
    (add_le_add upperTwoPayment_le (upperGapPayment_le (by norm_num : (1:ℝ) ≤ 3/2))) hb1
  have hbase := payment_le (by norm_num : (1:ℝ) ≤ 1127/600)
  have hcommon := mul_le_mul_of_nonneg_left
    (payment_le (by norm_num : (1:ℝ) ≤ 3884129/3606400)) ha
  have haclog := mul_le_mul_of_nonneg_left
    (payment_le (by norm_num : (1:ℝ) ≤ 4508/2927)) hac
  have hnear := mul_le_mul_of_nonpos_left
    (payment_le (by norm_num : (1:ℝ) ≤ 2400/2381)) hb
  have hdlog := mul_le_mul_of_nonpos_left
    (upperGapPayment_le (by norm_num : (1:ℝ) ≤ 4508/3981)) hd
  unfold logPaymentExtra F1KernelUpperAssembly.logPayment fourLowerRecoveryPayment
    logRecovery signedMainLogs finiteMainPayment
  linarith only [h2,hbase,hcommon,haclog,hnear,hdlog]

def coefficient : ℝ := F1FixedSquareRecovery.coefficient+8*logPaymentExtra

theorem coefficient_stronger : F1FixedSquareRecovery.coefficient < coefficient := by
  unfold coefficient
  linarith only [logPaymentExtra_pos]

theorem coefficient_le_actual : coefficient ≤ Wu08TerminalAlignment.firstMain := by
  rw [FirstActualRecovery.actual_first_recoveries]
  unfold coefficient F1FixedSquareRecovery.coefficient F1UnpaidRecovery.coefficient
    F1KernelUpperAssembly.coefficient
  linarith only [logPaymentExtra_le,square_le_unpaid_kernel_residual]

theorem actual_gap : (14900897:ℝ)/1000000-Wu08TerminalAlignment.firstMain =
    8*((F1KernelUpperAssembly.debit-unpaidFactorPayment-combinedSquarePayment-logPaymentExtra)-
      (logRecovery-F1KernelUpperAssembly.logPayment-logPaymentExtra)-
      (FirstActualRecovery.kernelRecovery-momentPayment-unpaidFactorPayment-
        combinedSquarePayment)-Wu08OriginalFirstSteps.E (1327/200)) := by
  rw [F1FixedSquareRecovery.actual_gap]
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

end F1LowerResidual
