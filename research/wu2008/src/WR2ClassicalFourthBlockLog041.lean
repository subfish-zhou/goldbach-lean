import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints041
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_041 (j : Fin 16) (hj : 16*41+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*41+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*41+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 656) ≤ val WuPaper.ClassicalFourthData.Bq 656
    have hp : val WuPaper.ClassicalFourthData.Bq 656 = (70176686372111:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 656 = 70176686372111 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 656 = (541:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_656
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 657) ≤ val WuPaper.ClassicalFourthData.Bq 657
    have hp : val WuPaper.ClassicalFourthData.Bq 657 = (70267807730323:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 657 = 70267807730323 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 657 = (8657:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_657
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 658) ≤ val WuPaper.ClassicalFourthData.Bq 658
    have hp : val WuPaper.ClassicalFourthData.Bq 658 = (70358886737011:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 658 = 70358886737011 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 658 = (4329:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_658
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 659) ≤ val WuPaper.ClassicalFourthData.Bq 659
    have hp : val WuPaper.ClassicalFourthData.Bq 659 = (70449923415993:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 659 = 70449923415993 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 659 = (8659:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_659
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 660) ≤ val WuPaper.ClassicalFourthData.Bq 660
    have hp : val WuPaper.ClassicalFourthData.Bq 660 = (70540917791069:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 660 = 70540917791069 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 660 = (433:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_660
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 661) ≤ val WuPaper.ClassicalFourthData.Bq 661
    have hp : val WuPaper.ClassicalFourthData.Bq 661 = (70631869886024:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 661 = 70631869886024 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 661 = (8661:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_661
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 662) ≤ val WuPaper.ClassicalFourthData.Bq 662
    have hp : val WuPaper.ClassicalFourthData.Bq 662 = (70722779724625:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 662 = 70722779724625 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 662 = (4331:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_662
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 663) ≤ val WuPaper.ClassicalFourthData.Bq 663
    have hp : val WuPaper.ClassicalFourthData.Bq 663 = (70813647330622:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 663 = 70813647330622 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 663 = (8663:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_663
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 664) ≤ val WuPaper.ClassicalFourthData.Bq 664
    have hp : val WuPaper.ClassicalFourthData.Bq 664 = (70904472727748:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 664 = 70904472727748 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 664 = (1083:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_664
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 665) ≤ val WuPaper.ClassicalFourthData.Bq 665
    have hp : val WuPaper.ClassicalFourthData.Bq 665 = (70995255939720:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 665 = 70995255939720 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 665 = (1733:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_665
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 666) ≤ val WuPaper.ClassicalFourthData.Bq 666
    have hp : val WuPaper.ClassicalFourthData.Bq 666 = (71085996990237:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 666 = 71085996990237 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 666 = (4333:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_666
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 667) ≤ val WuPaper.ClassicalFourthData.Bq 667
    have hp : val WuPaper.ClassicalFourthData.Bq 667 = (71176695902983:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 667 = 71176695902983 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 667 = (8667:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_667
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 668) ≤ val WuPaper.ClassicalFourthData.Bq 668
    have hp : val WuPaper.ClassicalFourthData.Bq 668 = (71267352701624:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 668 = 71267352701624 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 668 = (2167:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_668
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 669) ≤ val WuPaper.ClassicalFourthData.Bq 669
    have hp : val WuPaper.ClassicalFourthData.Bq 669 = (71357967409810:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 669 = 71357967409810 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 669 = (8669:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_669
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 670) ≤ val WuPaper.ClassicalFourthData.Bq 670
    have hp : val WuPaper.ClassicalFourthData.Bq 670 = (71448540051173:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 670 = 71448540051173 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 670 = (867:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_670
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 671) ≤ val WuPaper.ClassicalFourthData.Bq 671
    have hp : val WuPaper.ClassicalFourthData.Bq 671 = (71539070649328:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 671 = 71539070649328 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 671 = (8671:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_671
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_041
