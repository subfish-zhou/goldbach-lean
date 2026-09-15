import TailWholeCoefficientSigns

noncomputable section
open Real Wu2008DoubleSieve
open F1JointFTC F1ActualSecondFTC F1BFullFTC F1JointSplit
namespace TailWholeCommonLog

def lower : ℝ := (coeffTwo)*splitLow (2)+
  (coeffThreeHalf)*splitHigh (3/2)+
  (1)*splitLow (1127/600)+
  (coeffA)*splitHigh (3884129/3606400)+
  (coeffAC)*splitHigh (4508/2927)+
  (-coeffB)*splitHigh (2400/2381)+
  (coeffD)*splitLow (4508/3981)+
  (coeffS)*splitHigh (2254/1727)+
  (poleZero)*splitLow (927/800)+
  (poleOne)*splitHigh (727/600)+
  (coeffAM)*splitHigh (crossOneMinus)+
  (coeffAP)*splitLow (crossOnePlus)+
  (coeffTM)*splitLow (crossTwoMinus)+
  (coeffTP)*splitLow (crossTwoPlus)+
  (coeffBM)*splitLow (bCrossOneMinus)+
  (coeffBP)*splitHigh (bCrossOnePlus)+
  (coeffDM)*splitLow (bCrossTwoMinus)+
  (coeffDP)*splitHigh (bCrossTwoPlus)+rational+EJoint.payment

def recovery : ℝ := (coeffTwo)*ActualTailConsumption.splitFloor (2)+
  (1)*ActualTailConsumption.splitFloor (1127/600)+
  (coeffD)*ActualTailConsumption.splitFloor (4508/3981)+
  (poleZero)*ActualTailConsumption.splitFloor (927/800)+
  (coeffAP)*ActualTailConsumption.splitFloor (crossOnePlus)+
  (coeffTM)*ActualTailConsumption.splitFloor (crossTwoMinus)+
  (coeffTP)*ActualTailConsumption.splitFloor (crossTwoPlus)+
  (coeffBM)*ActualTailConsumption.splitFloor (bCrossOneMinus)+
  (coeffDM)*ActualTailConsumption.splitFloor (bCrossTwoMinus)

theorem lower_le_collected : lower ≤ collected := by
  obtain ⟨hxm,hxp,hym,hyp⟩ := cross_arguments
  obtain ⟨hbxm,hbxp,hbym,hbyp⟩ := b_cross_arguments
  have h0 := mul_le_mul_of_nonneg_left (splitLow_le (by norm_num : (1:ℝ)≤2)) coeffTwo_sign
  have h1 := mul_le_mul_of_nonpos_left (le_splitHigh (by norm_num : (1:ℝ)≤3/2)) coeffThreeHalf_sign
  have h2 := (splitLow_le (by norm_num : (1:ℝ)≤1127/600))
  have h3 := mul_le_mul_of_nonpos_left (le_splitHigh (by norm_num : (1:ℝ)≤3884129/3606400)) coeffA_sign
  have h4 := mul_le_mul_of_nonpos_left (le_splitHigh (by norm_num : (1:ℝ)≤4508/2927)) coeffAC_sign
  have h5 := mul_le_mul_of_nonpos_left (le_splitHigh (by norm_num : (1:ℝ)≤2400/2381)) (neg_nonpos.mpr coeffB_sign)
  have h6 := mul_le_mul_of_nonneg_left (splitLow_le (by norm_num : (1:ℝ)≤4508/3981)) coeffD_sign
  have h7 := mul_le_mul_of_nonpos_left (le_splitHigh (by norm_num : (1:ℝ)≤2254/1727)) coeffS_sign
  have h8 := mul_le_mul_of_nonneg_left (splitLow_le (by norm_num : (1:ℝ)≤927/800)) poleZero_sign
  have h9 := mul_le_mul_of_nonpos_left (le_splitHigh (by norm_num : (1:ℝ)≤727/600)) poleOne_sign
  have h10 := mul_le_mul_of_nonpos_left (le_splitHigh hxm) coeffAM_sign
  have h11 := mul_le_mul_of_nonneg_left (splitLow_le hxp) coeffAP_sign
  have h12 := mul_le_mul_of_nonneg_left (splitLow_le hym) coeffTM_sign
  have h13 := mul_le_mul_of_nonneg_left (splitLow_le hyp) coeffTP_sign
  have h14 := mul_le_mul_of_nonneg_left (splitLow_le hbxm) coeffBM_sign
  have h15 := mul_le_mul_of_nonpos_left (le_splitHigh hbxp) coeffBP_sign
  have h16 := mul_le_mul_of_nonneg_left (splitLow_le hbym) coeffDM_sign
  have h17 := mul_le_mul_of_nonpos_left (le_splitHigh hbyp) coeffDP_sign
  unfold collected lower
  linarith only [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17]

theorem recovery_le_loss : recovery ≤ collected-lower := by
  obtain ⟨hxm,hxp,hym,hyp⟩ := cross_arguments
  obtain ⟨hbxm,hbxp,hbym,hbyp⟩ := b_cross_arguments
  have h0 := mul_le_mul_of_nonneg_left (ActualTailConsumption.splitFloor_le_endpoint (by norm_num : (1:ℝ)≤2)) coeffTwo_sign
  have h1 := mul_le_mul_of_nonpos_left (le_splitHigh (by norm_num : (1:ℝ)≤3/2)) coeffThreeHalf_sign
  have h2 := (ActualTailConsumption.splitFloor_le_endpoint (by norm_num : (1:ℝ)≤1127/600))
  have h3 := mul_le_mul_of_nonpos_left (le_splitHigh (by norm_num : (1:ℝ)≤3884129/3606400)) coeffA_sign
  have h4 := mul_le_mul_of_nonpos_left (le_splitHigh (by norm_num : (1:ℝ)≤4508/2927)) coeffAC_sign
  have h5 := mul_le_mul_of_nonpos_left (le_splitHigh (by norm_num : (1:ℝ)≤2400/2381)) (neg_nonpos.mpr coeffB_sign)
  have h6 := mul_le_mul_of_nonneg_left (ActualTailConsumption.splitFloor_le_endpoint (by norm_num : (1:ℝ)≤4508/3981)) coeffD_sign
  have h7 := mul_le_mul_of_nonpos_left (le_splitHigh (by norm_num : (1:ℝ)≤2254/1727)) coeffS_sign
  have h8 := mul_le_mul_of_nonneg_left (ActualTailConsumption.splitFloor_le_endpoint (by norm_num : (1:ℝ)≤927/800)) poleZero_sign
  have h9 := mul_le_mul_of_nonpos_left (le_splitHigh (by norm_num : (1:ℝ)≤727/600)) poleOne_sign
  have h10 := mul_le_mul_of_nonpos_left (le_splitHigh hxm) coeffAM_sign
  have h11 := mul_le_mul_of_nonneg_left (ActualTailConsumption.splitFloor_le_endpoint hxp) coeffAP_sign
  have h12 := mul_le_mul_of_nonneg_left (ActualTailConsumption.splitFloor_le_endpoint hym) coeffTM_sign
  have h13 := mul_le_mul_of_nonneg_left (ActualTailConsumption.splitFloor_le_endpoint hyp) coeffTP_sign
  have h14 := mul_le_mul_of_nonneg_left (ActualTailConsumption.splitFloor_le_endpoint hbxm) coeffBM_sign
  have h15 := mul_le_mul_of_nonpos_left (le_splitHigh hbxp) coeffBP_sign
  have h16 := mul_le_mul_of_nonneg_left (ActualTailConsumption.splitFloor_le_endpoint hbym) coeffDM_sign
  have h17 := mul_le_mul_of_nonpos_left (le_splitHigh hbyp) coeffDP_sign
  unfold recovery collected lower
  linarith only [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17]

theorem recovered_le_collected : lower+recovery ≤ collected := by
  linarith only [recovery_le_loss]

/-- Fixed before any target comparison; both branches pay the same full mother. -/
def finite : ℝ := max (WholeCommonLog.lower+TailEndpointPayment.recovery) (lower+recovery)

theorem baseline_le_collected : WholeCommonLog.lower+TailEndpointPayment.recovery ≤ collected := by
  rw [←collected_exact]
  have hm : 0 ≤ ActualTailFinite.mass := by
    rw [←ActualTailFinite.mass_exact]
    exact ActualTailConsumption.mass_bounds.1
  linarith only [TailEndpointPayment.recovery_le_loss,hm]

theorem finite_le_collected : finite ≤ collected :=
  max_le baseline_le_collected recovered_le_collected

def endpointRemainder : ℝ := collected-finite

theorem endpointRemainder_nonneg : 0 ≤ endpointRemainder :=
  sub_nonneg.mpr finite_le_collected

/-- The branch loss, original tail balance and original E loss each occur once. -/
theorem finite_firstMain_exact : Wu08TerminalAlignment.firstMain =
    8*(finite+endpointRemainder+TailEndpointPayment.tailRemainder+FreshCommonLog.eLoss) := by
  rw [firstMain_exact]
  unfold endpointRemainder
  ring

theorem finite_le_actual : 8*finite ≤ Wu08TerminalAlignment.firstMain := by
  rw [finite_firstMain_exact]
  linarith only [endpointRemainder_nonneg,TailEndpointPayment.tailRemainder_nonneg,
    FreshCommonLog.eLoss_nonneg]

theorem finite_ge_baseline : WholeCommonLog.lower+TailEndpointPayment.recovery ≤ finite :=
  le_max_left _ _

theorem actual_count {ε : ℝ} (hε : 0<ε) :
    ∃ T : ℕ, 4≤T ∧ ∀ N : ℕ, T≤N → Even N →
      (8*finite-ε)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
        (sieveCount N 1 N ((N : ℝ)^truncatedSixthLowerAlpha) : ℝ) := by
  have he : 0<Wu08TerminalAlignment.firstMain-8*finite+ε := by
    linarith only [finite_le_actual,hε]
  obtain ⟨T,hT,h⟩ := Wu08TerminalAlignment.first_actual_count he
  refine ⟨T,hT,?_⟩
  intro N hN hEven
  have hid : Wu08TerminalAlignment.firstMain-(Wu08TerminalAlignment.firstMain-8*finite+ε)=
      8*finite-ε := by ring
  simpa only [hid] using h N hN hEven
end TailWholeCommonLog
