import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints472
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_472 (j : Fin 16) (hj : 16*472+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*472+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*472+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7552) ≤ val WuPaper.ClassicalFourthData.Bq 7552
    have hp : val WuPaper.ClassicalFourthData.Bq 7552 = (272778863434038:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7552 = 272778863434038 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7552 = (486:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7552
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7553) ≤ val WuPaper.ClassicalFourthData.Bq 7553
    have hp : val WuPaper.ClassicalFourthData.Bq 7553 = (272783587058948:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7553 = 272783587058948 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7553 = (15553:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7553
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7554) ≤ val WuPaper.ClassicalFourthData.Bq 7554
    have hp : val WuPaper.ClassicalFourthData.Bq 7554 = (272788308149710:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7554 = 272788308149710 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7554 = (7777:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7554
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7555) ≤ val WuPaper.ClassicalFourthData.Bq 7555
    have hp : val WuPaper.ClassicalFourthData.Bq 7555 = (272793026707148:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7555 = 272793026707148 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7555 = (3111:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7555
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7556) ≤ val WuPaper.ClassicalFourthData.Bq 7556
    have hp : val WuPaper.ClassicalFourthData.Bq 7556 = (272797742732082:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7556 = 272797742732082 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7556 = (3889:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7556
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7557) ≤ val WuPaper.ClassicalFourthData.Bq 7557
    have hp : val WuPaper.ClassicalFourthData.Bq 7557 = (272802456225335:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7557 = 272802456225335 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7557 = (15557:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7557
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7558) ≤ val WuPaper.ClassicalFourthData.Bq 7558
    have hp : val WuPaper.ClassicalFourthData.Bq 7558 = (272807167187728:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7558 = 272807167187728 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7558 = (7779:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7558
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7559) ≤ val WuPaper.ClassicalFourthData.Bq 7559
    have hp : val WuPaper.ClassicalFourthData.Bq 7559 = (272811875620082:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7559 = 272811875620082 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7559 = (15559:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7559
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7560) ≤ val WuPaper.ClassicalFourthData.Bq 7560
    have hp : val WuPaper.ClassicalFourthData.Bq 7560 = (272816581523218:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7560 = 272816581523218 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7560 = (389:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7560
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7561) ≤ val WuPaper.ClassicalFourthData.Bq 7561
    have hp : val WuPaper.ClassicalFourthData.Bq 7561 = (272821284897956:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7561 = 272821284897956 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7561 = (15561:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7561
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7562) ≤ val WuPaper.ClassicalFourthData.Bq 7562
    have hp : val WuPaper.ClassicalFourthData.Bq 7562 = (272825985745117:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7562 = 272825985745117 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7562 = (7781:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7562
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7563) ≤ val WuPaper.ClassicalFourthData.Bq 7563
    have hp : val WuPaper.ClassicalFourthData.Bq 7563 = (272830684065519:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7563 = 272830684065519 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7563 = (15563:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7563
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7564) ≤ val WuPaper.ClassicalFourthData.Bq 7564
    have hp : val WuPaper.ClassicalFourthData.Bq 7564 = (272835379859983:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7564 = 272835379859983 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7564 = (3891:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7564
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7565) ≤ val WuPaper.ClassicalFourthData.Bq 7565
    have hp : val WuPaper.ClassicalFourthData.Bq 7565 = (272840073129329:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7565 = 272840073129329 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7565 = (3113:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7565
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7566) ≤ val WuPaper.ClassicalFourthData.Bq 7566
    have hp : val WuPaper.ClassicalFourthData.Bq 7566 = (272844763874374:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7566 = 272844763874374 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7566 = (7783:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7566
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7567) ≤ val WuPaper.ClassicalFourthData.Bq 7567
    have hp : val WuPaper.ClassicalFourthData.Bq 7567 = (272849452095938:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7567 = 272849452095938 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7567 = (15567:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7567
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_472
