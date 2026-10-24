import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints349
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_349 (j : Fin 16) (hj : 16*349+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*349+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*349+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5584) ≤ val WuPaper.ClassicalFourthData.Bq 5584
    have hp : val WuPaper.ClassicalFourthData.Bq 5584 = (257302909379626:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5584 = 257302909379626 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5584 = (849:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5584
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5585) ≤ val WuPaper.ClassicalFourthData.Bq 5585
    have hp : val WuPaper.ClassicalFourthData.Bq 5585 = (257314689842539:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5585 = 257314689842539 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5585 = (2717:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5585
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5586) ≤ val WuPaper.ClassicalFourthData.Bq 5586
    have hp : val WuPaper.ClassicalFourthData.Bq 5586 = (257326465366570:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5586 = 257326465366570 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5586 = (6793:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5586
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5587) ≤ val WuPaper.ClassicalFourthData.Bq 5587
    have hp : val WuPaper.ClassicalFourthData.Bq 5587 = (257338235953478:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5587 = 257338235953478 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5587 = (13587:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5587
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5588) ≤ val WuPaper.ClassicalFourthData.Bq 5588
    have hp : val WuPaper.ClassicalFourthData.Bq 5588 = (257350001605020:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5588 = 257350001605020 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5588 = (3397:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5588
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5589) ≤ val WuPaper.ClassicalFourthData.Bq 5589
    have hp : val WuPaper.ClassicalFourthData.Bq 5589 = (257361762322955:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5589 = 257361762322955 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5589 = (13589:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5589
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5590) ≤ val WuPaper.ClassicalFourthData.Bq 5590
    have hp : val WuPaper.ClassicalFourthData.Bq 5590 = (257373518109040:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5590 = 257373518109040 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5590 = (1359:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5590
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5591) ≤ val WuPaper.ClassicalFourthData.Bq 5591
    have hp : val WuPaper.ClassicalFourthData.Bq 5591 = (257385268965030:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5591 = 257385268965030 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5591 = (13591:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5591
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5592) ≤ val WuPaper.ClassicalFourthData.Bq 5592
    have hp : val WuPaper.ClassicalFourthData.Bq 5592 = (257397014892681:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5592 = 257397014892681 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5592 = (1699:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5592
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5593) ≤ val WuPaper.ClassicalFourthData.Bq 5593
    have hp : val WuPaper.ClassicalFourthData.Bq 5593 = (257408755893747:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5593 = 257408755893747 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5593 = (13593:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5593
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5594) ≤ val WuPaper.ClassicalFourthData.Bq 5594
    have hp : val WuPaper.ClassicalFourthData.Bq 5594 = (257420491969983:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5594 = 257420491969983 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5594 = (6797:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5594
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5595) ≤ val WuPaper.ClassicalFourthData.Bq 5595
    have hp : val WuPaper.ClassicalFourthData.Bq 5595 = (257432223123142:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5595 = 257432223123142 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5595 = (2719:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5595
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5596) ≤ val WuPaper.ClassicalFourthData.Bq 5596
    have hp : val WuPaper.ClassicalFourthData.Bq 5596 = (257443949354976:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5596 = 257443949354976 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5596 = (3399:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5596
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5597) ≤ val WuPaper.ClassicalFourthData.Bq 5597
    have hp : val WuPaper.ClassicalFourthData.Bq 5597 = (257455670667237:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5597 = 257455670667237 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5597 = (13597:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5597
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5598) ≤ val WuPaper.ClassicalFourthData.Bq 5598
    have hp : val WuPaper.ClassicalFourthData.Bq 5598 = (257467387061677:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5598 = 257467387061677 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5598 = (6799:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5598
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5599) ≤ val WuPaper.ClassicalFourthData.Bq 5599
    have hp : val WuPaper.ClassicalFourthData.Bq 5599 = (257479098540044:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5599 = 257479098540044 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5599 = (13599:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5599
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_349
