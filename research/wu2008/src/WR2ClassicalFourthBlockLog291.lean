import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints291
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_291 (j : Fin 16) (hj : 16*291+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*291+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*291+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4656) ≤ val WuPaper.ClassicalFourthData.Bq 4656
    have hp : val WuPaper.ClassicalFourthData.Bq 4656 = (243981782864803:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4656 = 243981782864803 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4656 = (791:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4656
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4657) ≤ val WuPaper.ClassicalFourthData.Bq 4657
    have hp : val WuPaper.ClassicalFourthData.Bq 4657 = (243999014336335:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4657 = 243999014336335 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4657 = (12657:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4657
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4658) ≤ val WuPaper.ClassicalFourthData.Bq 4658
    have hp : val WuPaper.ClassicalFourthData.Bq 4658 = (244016238868668:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4658 = 244016238868668 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4658 = (6329:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4658
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4659) ≤ val WuPaper.ClassicalFourthData.Bq 4659
    have hp : val WuPaper.ClassicalFourthData.Bq 4659 = (244033456464421:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4659 = 244033456464421 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4659 = (12659:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4659
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4660) ≤ val WuPaper.ClassicalFourthData.Bq 4660
    have hp : val WuPaper.ClassicalFourthData.Bq 4660 = (244050667126210:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4660 = 244050667126210 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4660 = (633:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4660
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4661) ≤ val WuPaper.ClassicalFourthData.Bq 4661
    have hp : val WuPaper.ClassicalFourthData.Bq 4661 = (244067870856652:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4661 = 244067870856652 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4661 = (12661:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4661
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4662) ≤ val WuPaper.ClassicalFourthData.Bq 4662
    have hp : val WuPaper.ClassicalFourthData.Bq 4662 = (244085067658362:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4662 = 244085067658362 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4662 = (6331:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4662
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4663) ≤ val WuPaper.ClassicalFourthData.Bq 4663
    have hp : val WuPaper.ClassicalFourthData.Bq 4663 = (244102257533954:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4663 = 244102257533954 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4663 = (12663:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4663
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4664) ≤ val WuPaper.ClassicalFourthData.Bq 4664
    have hp : val WuPaper.ClassicalFourthData.Bq 4664 = (244119440486039:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4664 = 244119440486039 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4664 = (1583:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4664
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4665) ≤ val WuPaper.ClassicalFourthData.Bq 4665
    have hp : val WuPaper.ClassicalFourthData.Bq 4665 = (244136616517230:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4665 = 244136616517230 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4665 = (2533:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4665
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4666) ≤ val WuPaper.ClassicalFourthData.Bq 4666
    have hp : val WuPaper.ClassicalFourthData.Bq 4666 = (244153785630137:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4666 = 244153785630137 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4666 = (6333:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4666
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4667) ≤ val WuPaper.ClassicalFourthData.Bq 4667
    have hp : val WuPaper.ClassicalFourthData.Bq 4667 = (244170947827368:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4667 = 244170947827368 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4667 = (12667:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4667
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4668) ≤ val WuPaper.ClassicalFourthData.Bq 4668
    have hp : val WuPaper.ClassicalFourthData.Bq 4668 = (244188103111533:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4668 = 244188103111533 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4668 = (3167:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4668
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4669) ≤ val WuPaper.ClassicalFourthData.Bq 4669
    have hp : val WuPaper.ClassicalFourthData.Bq 4669 = (244205251485236:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4669 = 244205251485236 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4669 = (12669:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4669
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4670) ≤ val WuPaper.ClassicalFourthData.Bq 4670
    have hp : val WuPaper.ClassicalFourthData.Bq 4670 = (244222392951085:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4670 = 244222392951085 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4670 = (1267:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4670
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4671) ≤ val WuPaper.ClassicalFourthData.Bq 4671
    have hp : val WuPaper.ClassicalFourthData.Bq 4671 = (244239527511683:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4671 = 244239527511683 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4671 = (12671:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4671
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_291
