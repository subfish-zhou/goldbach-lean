import ActualTailConsumption

noncomputable section
open Real Wu2008DoubleSieve SharpLogRecurrence
open F1JointFTC F1ActualSecondFTC F1BFullFTC F1JointSplit WholeCommonLog
open WholeCommonLog (coeffA coeffB)
namespace TailEndpointPayment

/-- Only the positive coefficients of the already collected logarithms are recovered. -/
def recovery : ℝ := ActualTailConsumption.splitFloor (1127/600)+
  WholeCommonLog.coeffA*ActualTailConsumption.splitFloor (3884129/3606400)+
  coeffAC*ActualTailConsumption.splitFloor (4508/2927)+
  (-WholeCommonLog.coeffB)*ActualTailConsumption.splitFloor (2400/2381)+
  coeffS*ActualTailConsumption.splitFloor (2254/1727)+
  poleOne*ActualTailConsumption.splitFloor (727/600)+
  coeffAM*ActualTailConsumption.splitFloor crossOneMinus+
  coeffTP*ActualTailConsumption.splitFloor crossTwoPlus+
  coeffBP*ActualTailConsumption.splitFloor bCrossOnePlus+
  coeffDM*ActualTailConsumption.splitFloor bCrossTwoMinus+
  coeffDP*ActualTailConsumption.splitFloor bCrossTwoPlus

theorem recovery_le_loss : recovery ≤ collected-lower := by
  obtain ⟨hxm,hxp,hym,hyp⟩ := cross_arguments
  obtain ⟨hbxm,hbxp,hbym,hbyp⟩ := b_cross_arguments
  have h0 := mul_le_mul_of_nonpos_left log_two_le coeffTwo_sign
  have h1 := mul_le_mul_of_nonpos_left (le_splitHigh (by norm_num : (1:ℝ)≤3/2)) coeffThreeHalf_sign
  have h2 := ActualTailConsumption.splitFloor_le_endpoint (by norm_num : (1:ℝ)≤1127/600)
  have h3 := mul_le_mul_of_nonneg_left (ActualTailConsumption.splitFloor_le_endpoint
    (by norm_num : (1:ℝ)≤3884129/3606400)) coeffA_sign
  have h4 := mul_le_mul_of_nonneg_left (ActualTailConsumption.splitFloor_le_endpoint
    (by norm_num : (1:ℝ)≤4508/2927)) coeffAC_sign
  have h5 := mul_le_mul_of_nonneg_left (ActualTailConsumption.splitFloor_le_endpoint
    (by norm_num : (1:ℝ)≤2400/2381)) (neg_nonneg.mpr coeffB_sign)
  have h6 := mul_le_mul_of_nonpos_left (le_splitHigh (by norm_num : (1:ℝ)≤4508/3981)) coeffD_sign
  have h7 := mul_le_mul_of_nonneg_left (ActualTailConsumption.splitFloor_le_endpoint
    (by norm_num : (1:ℝ)≤2254/1727)) coeffS_sign
  have h8 := mul_le_mul_of_nonpos_left (le_splitHigh (by norm_num : (1:ℝ)≤927/800)) poleZero_sign
  have h9 := mul_le_mul_of_nonneg_left (ActualTailConsumption.splitFloor_le_endpoint
    (by norm_num : (1:ℝ)≤727/600)) poleOne_sign
  have h10 := mul_le_mul_of_nonneg_left (ActualTailConsumption.splitFloor_le_endpoint hxm) coeffAM_sign
  have h11 := mul_le_mul_of_nonpos_left (le_splitHigh hxp) coeffAP_sign
  have h12 := mul_le_mul_of_nonpos_left (le_splitHigh hym) coeffTM_sign
  have h13 := mul_le_mul_of_nonneg_left (ActualTailConsumption.splitFloor_le_endpoint hyp) coeffTP_sign
  have h14 := mul_le_mul_of_nonpos_left (le_splitHigh hbxm) coeffBM_sign
  have h15 := mul_le_mul_of_nonneg_left (ActualTailConsumption.splitFloor_le_endpoint hbxp) coeffBP_sign
  have h16 := mul_le_mul_of_nonneg_left (ActualTailConsumption.splitFloor_le_endpoint hbym) coeffDM_sign
  have h17 := mul_le_mul_of_nonneg_left (ActualTailConsumption.splitFloor_le_endpoint hbyp) coeffDP_sign
  unfold recovery collected lower
  linarith only [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17]

theorem recovery_pos : 0 < recovery := by
  obtain ⟨hxm,_,_,hyp⟩ := cross_arguments
  obtain ⟨_,hbxp,hbym,hbyp⟩ := b_cross_arguments
  have hf (x : ℝ) (hx : 1 ≤ x) := ActualTailConsumption.splitFloor_nonneg hx
  have hfirst : 0 < ActualTailConsumption.splitFloor (1127/600) := by
    exact add_pos_of_pos_of_nonneg (ActualTailVariation.floor_pos (by norm_num))
      (ActualTailVariation.floor_nonneg (by norm_num))
  have h3 := mul_nonneg coeffA_sign (hf _ (by norm_num : (1:ℝ)≤3884129/3606400))
  have h4 := mul_nonneg coeffAC_sign (hf _ (by norm_num : (1:ℝ)≤4508/2927))
  have h5 := mul_nonneg (neg_nonneg.mpr coeffB_sign) (hf _ (by norm_num : (1:ℝ)≤2400/2381))
  have h7 := mul_nonneg coeffS_sign (hf _ (by norm_num : (1:ℝ)≤2254/1727))
  have h9 := mul_nonneg poleOne_sign (hf _ (by norm_num : (1:ℝ)≤727/600))
  have h10 := mul_nonneg coeffAM_sign (hf _ hxm)
  have h13 := mul_nonneg coeffTP_sign (hf _ hyp)
  have h15 := mul_nonneg coeffBP_sign (hf _ hbxp)
  have h16 := mul_nonneg coeffDM_sign (hf _ hbym)
  have h17 := mul_nonneg coeffDP_sign (hf _ hbyp)
  unfold recovery
  linarith only [hfirst,h3,h4,h5,h7,h9,h10,h13,h15,h16,h17]

/-- The tail mass is the full original integral, not a pointwise endpoint payment. -/
def paid : ℝ := lower+recovery+ActualTailConsumption.mass

def endpointRemainder : ℝ := collected-lower-recovery
def tailRemainder : ℝ := F1CrossMass.tailMass-ActualTailConsumption.mass

theorem endpointRemainder_nonneg : 0 ≤ endpointRemainder := sub_nonneg.mpr recovery_le_loss

theorem tailRemainder_nonneg : 0 ≤ tailRemainder := sub_nonneg.mpr ActualTailConsumption.mass_bounds.2

/-- Each of the three genuine remaining balances occurs exactly once. -/
theorem firstMain_exact : Wu08TerminalAlignment.firstMain =
    8*(paid+endpointRemainder+tailRemainder+FreshCommonLog.eLoss) := by
  rw [WholeCommonLog.firstMain_exact]
  unfold paid endpointRemainder tailRemainder
  ring

theorem paid_le_actual : 8*paid ≤ Wu08TerminalAlignment.firstMain := by
  rw [firstMain_exact]
  linarith only [endpointRemainder_nonneg,tailRemainder_nonneg,FreshCommonLog.eLoss_nonneg]

theorem strict_improvement : lower < paid := by
  unfold paid
  linarith only [recovery_pos,ActualTailConsumption.mass_bounds.1]

theorem actual_count {ε : ℝ} (hε : 0<ε) :
    ∃ T : ℕ, 4≤T ∧ ∀ N : ℕ, T≤N → Even N →
      (8*paid-ε)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
        (sieveCount N 1 N ((N : ℝ)^truncatedSixthLowerAlpha) : ℝ) := by
  have he : 0<Wu08TerminalAlignment.firstMain-8*paid+ε := by
    linarith only [paid_le_actual,hε]
  obtain ⟨T,hT,h⟩ := Wu08TerminalAlignment.first_actual_count he
  refine ⟨T,hT,?_⟩
  intro N hN hEven
  have hid : Wu08TerminalAlignment.firstMain-(Wu08TerminalAlignment.firstMain-8*paid+ε)=
      8*paid-ε := by ring
  simpa only [hid] using h N hN hEven
end TailEndpointPayment
