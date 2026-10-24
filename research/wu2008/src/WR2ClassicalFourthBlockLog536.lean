import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints536
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_536 (j : Fin 16) (hj : 16*536+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*536+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*536+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8576) ≤ val WuPaper.ClassicalFourthData.Bq 8576
    have hp : val WuPaper.ClassicalFourthData.Bq 8576 = (276422749656148:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8576 = 276422749656148 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8576 = (518:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8576
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8577) ≤ val WuPaper.ClassicalFourthData.Bq 8577
    have hp : val WuPaper.ClassicalFourthData.Bq 8577 = (276425261013032:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8577 = 276425261013032 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8577 = (16577:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8577
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8578) ≤ val WuPaper.ClassicalFourthData.Bq 8578
    have hp : val WuPaper.ClassicalFourthData.Bq 8578 = (276427770541577:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8578 = 276427770541577 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8578 = (8289:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8578
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8579) ≤ val WuPaper.ClassicalFourthData.Bq 8579
    have hp : val WuPaper.ClassicalFourthData.Bq 8579 = (276430278242357:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8579 = 276430278242357 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8579 = (16579:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8579
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8580) ≤ val WuPaper.ClassicalFourthData.Bq 8580
    have hp : val WuPaper.ClassicalFourthData.Bq 8580 = (276432784115943:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8580 = 276432784115943 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8580 = (829:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8580
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8581) ≤ val WuPaper.ClassicalFourthData.Bq 8581
    have hp : val WuPaper.ClassicalFourthData.Bq 8581 = (276435288162909:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8581 = 276435288162909 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8581 = (16581:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8581
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8582) ≤ val WuPaper.ClassicalFourthData.Bq 8582
    have hp : val WuPaper.ClassicalFourthData.Bq 8582 = (276437790383828:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8582 = 276437790383828 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8582 = (8291:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8582
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8583) ≤ val WuPaper.ClassicalFourthData.Bq 8583
    have hp : val WuPaper.ClassicalFourthData.Bq 8583 = (276440290779272:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8583 = 276440290779272 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8583 = (16583:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8583
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8584) ≤ val WuPaper.ClassicalFourthData.Bq 8584
    have hp : val WuPaper.ClassicalFourthData.Bq 8584 = (276442789349814:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8584 = 276442789349814 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8584 = (2073:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8584
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8585) ≤ val WuPaper.ClassicalFourthData.Bq 8585
    have hp : val WuPaper.ClassicalFourthData.Bq 8585 = (276445286096025:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8585 = 276445286096025 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8585 = (3317:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8585
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8586) ≤ val WuPaper.ClassicalFourthData.Bq 8586
    have hp : val WuPaper.ClassicalFourthData.Bq 8586 = (276447781018479:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8586 = 276447781018479 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8586 = (8293:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8586
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8587) ≤ val WuPaper.ClassicalFourthData.Bq 8587
    have hp : val WuPaper.ClassicalFourthData.Bq 8587 = (276450274117747:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8587 = 276450274117747 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8587 = (16587:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8587
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8588) ≤ val WuPaper.ClassicalFourthData.Bq 8588
    have hp : val WuPaper.ClassicalFourthData.Bq 8588 = (276452765394399:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8588 = 276452765394399 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8588 = (4147:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8588
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8589) ≤ val WuPaper.ClassicalFourthData.Bq 8589
    have hp : val WuPaper.ClassicalFourthData.Bq 8589 = (276455254849009:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8589 = 276455254849009 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8589 = (16589:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8589
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8590) ≤ val WuPaper.ClassicalFourthData.Bq 8590
    have hp : val WuPaper.ClassicalFourthData.Bq 8590 = (276457742482146:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8590 = 276457742482146 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8590 = (1659:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8590
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8591) ≤ val WuPaper.ClassicalFourthData.Bq 8591
    have hp : val WuPaper.ClassicalFourthData.Bq 8591 = (276460228294383:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8591 = 276460228294383 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8591 = (16591:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8591
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_536
