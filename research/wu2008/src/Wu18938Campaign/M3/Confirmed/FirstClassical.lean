import W10Collected
import Wu18938Campaign.M3.Confirmed.AnalyticAssembly

noncomputable section

namespace Wu18938Campaign.M3.Confirmed.FirstClassical

open Real Wu2008DoubleSieve Wu08TerminalAlignment WuTarget.W10

theorem log_two_product :
    (442333856992762/1000000000000:ℝ) ≤ TailWholeCommonLog.coeffTwo*log 2 := by
  have h := mul_le_mul
    (show (25526114476033728323/40000000000000000:ℝ) ≤
      TailWholeCommonLog.coeffTwo from coeffTwo_bounds.1)
    (TableBounds.logLower_le (x := 2) (by norm_num))
    (show 0 ≤ TableBounds.logLower 2 by norm_num [TableBounds.logLower])
    (show 0 ≤ TailWholeCommonLog.coeffTwo by linarith only [coeffTwo_bounds.1])
  exact (show (442333856992762/1000000000000:ℝ) ≤
      (25526114476033728323/40000000000000000)*TableBounds.logLower 2 by
    norm_num [TableBounds.logLower]).trans h

theorem log_ac_product :
    (-475905282611060/1000000000000:ℝ) ≤
      TailWholeCommonLog.coeffAC*log (4508/2927) := by
  have hl := LogMoments.log_upper (x := 4508/2927) (by norm_num) 12
  have h1 := mul_le_mul_of_nonpos_left hl
    (show (-220389989765102527713/200000000000000000:ℝ) ≤ 0 by norm_num)
  have h2 := mul_le_mul_of_nonneg_right coeffAC_bounds.1
    (log_nonneg (show (1:ℝ) ≤ 4508/2927 by norm_num))
  exact (show (-475905282611060/1000000000000:ℝ) ≤
      (-220389989765102527713/200000000000000000)*LogMoments.logUpper 12 (4508/2927) by
    norm_num [LogMoments.logUpper]).trans (h1.trans h2)

theorem log_ap_product :
    (191118410598640/1000000000000:ℝ) ≤
      TailWholeCommonLog.coeffAP*log F1ActualSecondFTC.crossOnePlus := by
  have hb : (1444294703744269429/1000000000000000000:ℝ) ≤
      F1ActualSecondFTC.crossOnePlus := W10Log11_b1.1
  have hl := (TableBounds.logLower_le
    (show (1:ℝ) ≤ 1444294703744269429/1000000000000000000 by norm_num)).trans
    (log_le_log (by norm_num) hb)
  have hn : 0 ≤ TableBounds.logLower (1444294703744269429/1000000000000000000) := by
    norm_num [TableBounds.logLower]
  have h := mul_le_mul coeffAP_bounds.1 hl hn
    (show 0 ≤ TailWholeCommonLog.coeffAP by linarith only [coeffAP_bounds.1])
  exact (show (191118410598640/1000000000000:ℝ) ≤
      (25993938647819149759/50000000000000000)*
        TableBounds.logLower (1444294703744269429/1000000000000000000) by
    norm_num [TableBounds.logLower]).trans h

theorem log_plain_lower :
    (630384858823/1000000000000:ℝ) ≤ log (1127/600) :=
  (show (630384858823/1000000000000:ℝ) ≤ TableBounds.logLower (1127/600) by
    norm_num [TableBounds.logLower]).trans (TableBounds.logLower_le (by norm_num))

theorem collected_lower :
    (14900896/8000000:ℝ) ≤ TailWholeCommonLog.collected := by
  unfold TailWholeCommonLog.collected
  have h0 := log_two_product
  have h1 := W10Collected_b21.1
  have h2 := log_plain_lower
  have h3 := W10Collected_b24.1
  have h4 := log_ac_product
  have h5 := W10Collected_b26.1
  have h6 := W10Collected_b28.1
  have h7 := W10Collected_b29.1
  have h8 := W10Collected_b30.1
  have h9 := W10Collected_b31.1
  have h10 := W10Collected_b32.1
  have h11 := log_ap_product
  have h12 := W10Collected_b34.1
  have h13 := W10Collected_b35.1
  have h14 := W10Collected_b36.1
  have h15 := W10Collected_b37.1
  have h16 := W10Collected_b38.1
  have h17 := W10Collected_b39.1
  have h18 := constant0_bounds.1
  have h19 := constant1_bounds.1
  ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 ⊢
  linarith only [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19]

theorem first_main_lower : (14900896/1000000:ℝ) ≤ firstMain := by
  have h := TailWholeCommonLog.collected_le_actual
  linarith only [h,collected_lower]

theorem first_actual_lower {ε : ℝ} (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ((14900896/1000000:ℝ)-ε)*truncatedSixthMassScale N ≤
        (sieveCount N 1 N ((N:ℝ)^truncatedSixthLowerAlpha) : ℝ) := by
  obtain ⟨T,hT,h⟩ := first_actual_count he
  refine ⟨T,hT,fun N hN hEven => ?_⟩
  have hp := mul_le_mul_of_nonneg_right (sub_le_sub_right first_main_lower ε)
    (truncatedSixthClosure_scale_nonneg (hT.trans hN))
  exact hp.trans (by
    convert h N hN hEven using 1 <;> unfold truncatedSixthMassScale <;> ring)

end Wu18938Campaign.M3.Confirmed.FirstClassical
