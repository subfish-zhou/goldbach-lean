import WholeCoefficientSigns

noncomputable section
open Real Wu2008DoubleSieve SharpLogRecurrence
open F1JointFTC F1ActualSecondFTC F1BFullFTC F1JointSplit
namespace WholeCommonLog

def lower : ℝ := (coeffTwo)*twoUpper+
  (coeffThreeHalf)*splitHigh (3/2)+
  (1)*splitLow (1127/600)+
  (coeffA)*splitLow (3884129/3606400)+
  (coeffAC)*splitLow (4508/2927)+
  (-coeffB)*splitLow (2400/2381)+
  (coeffD)*splitHigh (4508/3981)+
  (coeffS)*splitLow (2254/1727)+
  (poleZero)*splitHigh (927/800)+
  (poleOne)*splitLow (727/600)+
  (coeffAM)*splitLow (crossOneMinus)+
  (coeffAP)*splitHigh (crossOnePlus)+
  (coeffTM)*splitHigh (crossTwoMinus)+
  (coeffTP)*splitLow (crossTwoPlus)+
  (coeffBM)*splitHigh (bCrossOneMinus)+
  (coeffBP)*splitLow (bCrossOnePlus)+
  (coeffDM)*splitLow (bCrossTwoMinus)+
  (coeffDP)*splitLow (bCrossTwoPlus)+rational+EJoint.payment

theorem lower_le_collected : lower ≤ collected := by
  obtain ⟨hxm,hxp,hym,hyp⟩ := cross_arguments
  obtain ⟨hbxm,hbxp,hbym,hbyp⟩ := b_cross_arguments
  have h0 := mul_le_mul_of_nonpos_left log_two_le coeffTwo_sign
  have h1 := mul_le_mul_of_nonpos_left (le_splitHigh (by norm_num : (1:ℝ)≤3/2)) coeffThreeHalf_sign
  have h2 := (splitLow_le (by norm_num : (1:ℝ)≤1127/600))
  have h3 := mul_le_mul_of_nonneg_left (splitLow_le (by norm_num : (1:ℝ)≤3884129/3606400)) coeffA_sign
  have h4 := mul_le_mul_of_nonneg_left (splitLow_le (by norm_num : (1:ℝ)≤4508/2927)) coeffAC_sign
  have h5 := mul_le_mul_of_nonneg_left (splitLow_le (by norm_num : (1:ℝ)≤2400/2381)) (neg_nonneg.mpr coeffB_sign)
  have h6 := mul_le_mul_of_nonpos_left (le_splitHigh (by norm_num : (1:ℝ)≤4508/3981)) coeffD_sign
  have h7 := mul_le_mul_of_nonneg_left (splitLow_le (by norm_num : (1:ℝ)≤2254/1727)) coeffS_sign
  have h8 := mul_le_mul_of_nonpos_left (le_splitHigh (by norm_num : (1:ℝ)≤927/800)) poleZero_sign
  have h9 := mul_le_mul_of_nonneg_left (splitLow_le (by norm_num : (1:ℝ)≤727/600)) poleOne_sign
  have h10 := mul_le_mul_of_nonneg_left (splitLow_le hxm) coeffAM_sign
  have h11 := mul_le_mul_of_nonpos_left (le_splitHigh hxp) coeffAP_sign
  have h12 := mul_le_mul_of_nonpos_left (le_splitHigh hym) coeffTM_sign
  have h13 := mul_le_mul_of_nonneg_left (splitLow_le hyp) coeffTP_sign
  have h14 := mul_le_mul_of_nonpos_left (le_splitHigh hbxm) coeffBM_sign
  have h15 := mul_le_mul_of_nonneg_left (splitLow_le hbxp) coeffBP_sign
  have h16 := mul_le_mul_of_nonneg_left (splitLow_le hbym) coeffDM_sign
  have h17 := mul_le_mul_of_nonneg_left (splitLow_le hbyp) coeffDP_sign
  unfold lower collected
  linarith only [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17]

theorem lower_le_actual : 8*lower ≤ Wu08TerminalAlignment.firstMain := by
  linarith only [lower_le_collected,collected_le_actual]

theorem actual_count {ε : ℝ} (hε : 0<ε) :
    ∃ T : ℕ, 4≤T ∧ ∀ N : ℕ, T≤N → Even N →
      (8*lower-ε)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
        (sieveCount N 1 N ((N : ℝ)^truncatedSixthLowerAlpha) : ℝ) := by
  have he : 0<Wu08TerminalAlignment.firstMain-8*lower+ε := by
    linarith only [lower_le_actual,hε]
  obtain ⟨T,hT,h⟩ := Wu08TerminalAlignment.first_actual_count he
  refine ⟨T,hT,?_⟩
  intro N hN hEven
  have hid : Wu08TerminalAlignment.firstMain-(Wu08TerminalAlignment.firstMain-8*lower+ε)=
      8*lower-ε := by ring
  simpa only [hid] using h N hN hEven
end WholeCommonLog
