import F1SignedUpperFTC

noncomputable section
open Real Wu2008DoubleSieve
open F1JointFTC F1ActualSecondFTC F1BFullFTC F1JointSplit
namespace F1SignedUpperLedger
open F1SignedUpperFTC

def oldPayment : ℝ := (-(WholeCommonLog.coeffThreeHalf))*splitPayment (3/2)+
  (-(WholeCommonLog.coeffD))*splitPayment (4508/3981)+
  (-(WholeCommonLog.poleZero))*splitPayment (927/800)+
  (-(WholeCommonLog.coeffAP))*splitPayment (crossOnePlus)+
  (-(WholeCommonLog.coeffTM))*splitPayment (crossTwoMinus)+
  (-(WholeCommonLog.coeffBM))*splitPayment (bCrossOneMinus)

theorem oldPayment_le_balance : oldPayment ≤ WholeCommonLog.collected-WholeCommonLog.lower-TailEndpointPayment.recovery := by
  obtain ⟨hxm,hxp,hym,hyp⟩ := cross_arguments
  obtain ⟨hbxm,hbxp,hbym,hbyp⟩ := b_cross_arguments
  have h0 := mul_le_mul_of_nonpos_left log_two_le WholeCommonLog.coeffTwo_sign
  have h1 := negative_payment WholeCommonLog.coeffThreeHalf_sign (by norm_num : (1:ℝ) ≤ 3/2)
  have h2 := ActualTailConsumption.splitFloor_le_endpoint (by norm_num : (1:ℝ) ≤ 1127/600)
  have h3 := mul_le_mul_of_nonneg_left (ActualTailConsumption.splitFloor_le_endpoint (by norm_num : (1:ℝ) ≤ 3884129/3606400)) WholeCommonLog.coeffA_sign
  have h4 := mul_le_mul_of_nonneg_left (ActualTailConsumption.splitFloor_le_endpoint (by norm_num : (1:ℝ) ≤ 4508/2927)) WholeCommonLog.coeffAC_sign
  have h5 := mul_le_mul_of_nonneg_left (ActualTailConsumption.splitFloor_le_endpoint (by norm_num : (1:ℝ) ≤ 2400/2381)) (neg_nonneg.mpr WholeCommonLog.coeffB_sign)
  have h6 := negative_payment WholeCommonLog.coeffD_sign (by norm_num : (1:ℝ) ≤ 4508/3981)
  have h7 := mul_le_mul_of_nonneg_left (ActualTailConsumption.splitFloor_le_endpoint (by norm_num : (1:ℝ) ≤ 2254/1727)) WholeCommonLog.coeffS_sign
  have h8 := negative_payment WholeCommonLog.poleZero_sign (by norm_num : (1:ℝ) ≤ 927/800)
  have h9 := mul_le_mul_of_nonneg_left (ActualTailConsumption.splitFloor_le_endpoint (by norm_num : (1:ℝ) ≤ 727/600)) WholeCommonLog.poleOne_sign
  have h10 := mul_le_mul_of_nonneg_left (ActualTailConsumption.splitFloor_le_endpoint hxm) WholeCommonLog.coeffAM_sign
  have h11 := negative_payment WholeCommonLog.coeffAP_sign hxp
  have h12 := negative_payment WholeCommonLog.coeffTM_sign hym
  have h13 := mul_le_mul_of_nonneg_left (ActualTailConsumption.splitFloor_le_endpoint hyp) WholeCommonLog.coeffTP_sign
  have h14 := negative_payment WholeCommonLog.coeffBM_sign hbxm
  have h15 := mul_le_mul_of_nonneg_left (ActualTailConsumption.splitFloor_le_endpoint hbxp) WholeCommonLog.coeffBP_sign
  have h16 := mul_le_mul_of_nonneg_left (ActualTailConsumption.splitFloor_le_endpoint hbym) WholeCommonLog.coeffDM_sign
  have h17 := mul_le_mul_of_nonneg_left (ActualTailConsumption.splitFloor_le_endpoint hbyp) WholeCommonLog.coeffDP_sign
  unfold oldPayment WholeCommonLog.collected WholeCommonLog.lower TailEndpointPayment.recovery
  linarith only [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17]

theorem oldPayment_pos : 0 < oldPayment := by
  obtain ⟨hxm,hxp,hym,hyp⟩ := cross_arguments
  obtain ⟨hbxm,hbxp,hbym,hbyp⟩ := b_cross_arguments
  have hc : WholeCommonLog.coeffThreeHalf < 0 := by
    rw [WholeCommonLog.coeffThreeHalf_exact]
    norm_num
  have hp := mul_pos (neg_pos.mpr hc) (splitPayment_pos (by norm_num : (1:ℝ) < 3/2))
  have h6 := mul_nonneg (neg_nonneg.mpr WholeCommonLog.coeffD_sign) (splitPayment_nonneg (by norm_num : (1:ℝ) ≤ 4508/3981))
  have h8 := mul_nonneg (neg_nonneg.mpr WholeCommonLog.poleZero_sign) (splitPayment_nonneg (by norm_num : (1:ℝ) ≤ 927/800))
  have h11 := mul_nonneg (neg_nonneg.mpr WholeCommonLog.coeffAP_sign) (splitPayment_nonneg hxp)
  have h12 := mul_nonneg (neg_nonneg.mpr WholeCommonLog.coeffTM_sign) (splitPayment_nonneg hym)
  have h14 := mul_nonneg (neg_nonneg.mpr WholeCommonLog.coeffBM_sign) (splitPayment_nonneg hbxm)
  unfold oldPayment
  linarith only [hp,h6,h8,h11,h12,h14]

def newPayment : ℝ := (-(TailWholeCommonLog.coeffThreeHalf))*splitPayment (3/2)+
  (-(TailWholeCommonLog.coeffA))*splitPayment (3884129/3606400)+
  (-(TailWholeCommonLog.coeffAC))*splitPayment (4508/2927)+
  (-(-TailWholeCommonLog.coeffB))*splitPayment (2400/2381)+
  (-(TailWholeCommonLog.coeffS))*splitPayment (2254/1727)+
  (-(TailWholeCommonLog.poleOne))*splitPayment (727/600)+
  (-(TailWholeCommonLog.coeffAM))*splitPayment (crossOneMinus)+
  (-(TailWholeCommonLog.coeffBP))*splitPayment (bCrossOnePlus)+
  (-(TailWholeCommonLog.coeffDP))*splitPayment (bCrossTwoPlus)

theorem newPayment_le_balance : newPayment ≤ TailWholeCommonLog.collected-TailWholeCommonLog.lower-TailWholeCommonLog.recovery := by
  obtain ⟨hxm,hxp,hym,hyp⟩ := cross_arguments
  obtain ⟨hbxm,hbxp,hbym,hbyp⟩ := b_cross_arguments
  have h0 := mul_le_mul_of_nonneg_left (ActualTailConsumption.splitFloor_le_endpoint (by norm_num : (1:ℝ) ≤ 2)) TailWholeCommonLog.coeffTwo_sign
  have h1 := negative_payment TailWholeCommonLog.coeffThreeHalf_sign (by norm_num : (1:ℝ) ≤ 3/2)
  have h2 := ActualTailConsumption.splitFloor_le_endpoint (by norm_num : (1:ℝ) ≤ 1127/600)
  have h3 := negative_payment TailWholeCommonLog.coeffA_sign (by norm_num : (1:ℝ) ≤ 3884129/3606400)
  have h4 := negative_payment TailWholeCommonLog.coeffAC_sign (by norm_num : (1:ℝ) ≤ 4508/2927)
  have h5 := negative_payment (neg_nonpos.mpr TailWholeCommonLog.coeffB_sign) (by norm_num : (1:ℝ) ≤ 2400/2381)
  have h6 := mul_le_mul_of_nonneg_left (ActualTailConsumption.splitFloor_le_endpoint (by norm_num : (1:ℝ) ≤ 4508/3981)) TailWholeCommonLog.coeffD_sign
  have h7 := negative_payment TailWholeCommonLog.coeffS_sign (by norm_num : (1:ℝ) ≤ 2254/1727)
  have h8 := mul_le_mul_of_nonneg_left (ActualTailConsumption.splitFloor_le_endpoint (by norm_num : (1:ℝ) ≤ 927/800)) TailWholeCommonLog.poleZero_sign
  have h9 := negative_payment TailWholeCommonLog.poleOne_sign (by norm_num : (1:ℝ) ≤ 727/600)
  have h10 := negative_payment TailWholeCommonLog.coeffAM_sign hxm
  have h11 := mul_le_mul_of_nonneg_left (ActualTailConsumption.splitFloor_le_endpoint hxp) TailWholeCommonLog.coeffAP_sign
  have h12 := mul_le_mul_of_nonneg_left (ActualTailConsumption.splitFloor_le_endpoint hym) TailWholeCommonLog.coeffTM_sign
  have h13 := mul_le_mul_of_nonneg_left (ActualTailConsumption.splitFloor_le_endpoint hyp) TailWholeCommonLog.coeffTP_sign
  have h14 := mul_le_mul_of_nonneg_left (ActualTailConsumption.splitFloor_le_endpoint hbxm) TailWholeCommonLog.coeffBM_sign
  have h15 := negative_payment TailWholeCommonLog.coeffBP_sign hbxp
  have h16 := mul_le_mul_of_nonneg_left (ActualTailConsumption.splitFloor_le_endpoint hbym) TailWholeCommonLog.coeffDM_sign
  have h17 := negative_payment TailWholeCommonLog.coeffDP_sign hbyp
  unfold newPayment TailWholeCommonLog.collected TailWholeCommonLog.lower TailWholeCommonLog.recovery
  linarith only [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17]

theorem newPayment_pos : 0 < newPayment := by
  obtain ⟨hxm,hxp,hym,hyp⟩ := cross_arguments
  obtain ⟨hbxm,hbxp,hbym,hbyp⟩ := b_cross_arguments
  have hc : TailWholeCommonLog.coeffThreeHalf < 0 := by
    rw [TailWholeCommonLog.coeffThreeHalf_exact]
    norm_num
  have hp := mul_pos (neg_pos.mpr hc) (splitPayment_pos (by norm_num : (1:ℝ) < 3/2))
  have h3 := mul_nonneg (neg_nonneg.mpr TailWholeCommonLog.coeffA_sign) (splitPayment_nonneg (by norm_num : (1:ℝ) ≤ 3884129/3606400))
  have h4 := mul_nonneg (neg_nonneg.mpr TailWholeCommonLog.coeffAC_sign) (splitPayment_nonneg (by norm_num : (1:ℝ) ≤ 4508/2927))
  have h5 := mul_nonneg (neg_nonneg.mpr (neg_nonpos.mpr TailWholeCommonLog.coeffB_sign)) (splitPayment_nonneg (by norm_num : (1:ℝ) ≤ 2400/2381))
  have h7 := mul_nonneg (neg_nonneg.mpr TailWholeCommonLog.coeffS_sign) (splitPayment_nonneg (by norm_num : (1:ℝ) ≤ 2254/1727))
  have h9 := mul_nonneg (neg_nonneg.mpr TailWholeCommonLog.poleOne_sign) (splitPayment_nonneg (by norm_num : (1:ℝ) ≤ 727/600))
  have h10 := mul_nonneg (neg_nonneg.mpr TailWholeCommonLog.coeffAM_sign) (splitPayment_nonneg hxm)
  have h15 := mul_nonneg (neg_nonneg.mpr TailWholeCommonLog.coeffBP_sign) (splitPayment_nonneg hbxp)
  have h17 := mul_nonneg (neg_nonneg.mpr TailWholeCommonLog.coeffDP_sign) (splitPayment_nonneg hbyp)
  unfold newPayment
  linarith only [hp,h3,h4,h5,h7,h9,h10,h15,h17]

theorem oldPayment_le_endpointRemainder :
    oldPayment ≤ TailEndpointPayment.endpointRemainder := oldPayment_le_balance

/-- Old and new collected ledgers stay separate; no recovery is mixed across them. -/
theorem newPayment_le_recovered_gap :
    newPayment ≤ TailWholeCommonLog.collected-
      (TailWholeCommonLog.lower+TailWholeCommonLog.recovery) := by
  linarith only [newPayment_le_balance]

end F1SignedUpperLedger
