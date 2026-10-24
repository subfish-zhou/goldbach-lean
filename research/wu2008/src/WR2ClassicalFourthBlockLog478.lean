import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints478
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_478 (j : Fin 16) (hj : 16*478+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*478+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*478+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7648) ≤ val WuPaper.ClassicalFourthData.Bq 7648
    have hp : val WuPaper.ClassicalFourthData.Bq 7648 = (273220892212585:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7648 = 273220892212585 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7648 = (489:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7648
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7649) ≤ val WuPaper.ClassicalFourthData.Bq 7649
    have hp : val WuPaper.ClassicalFourthData.Bq 7649 = (273225376266584:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7649 = 273225376266584 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7649 = (15649:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7649
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7650) ≤ val WuPaper.ClassicalFourthData.Bq 7650
    have hp : val WuPaper.ClassicalFourthData.Bq 7650 = (273229857864030:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7650 = 273229857864030 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7650 = (313:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7650
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7651) ≤ val WuPaper.ClassicalFourthData.Bq 7651
    have hp : val WuPaper.ClassicalFourthData.Bq 7651 = (273234337005715:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7651 = 273234337005715 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7651 = (15651:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7651
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7652) ≤ val WuPaper.ClassicalFourthData.Bq 7652
    have hp : val WuPaper.ClassicalFourthData.Bq 7652 = (273238813692435:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7652 = 273238813692435 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7652 = (3913:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7652
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7653) ≤ val WuPaper.ClassicalFourthData.Bq 7653
    have hp : val WuPaper.ClassicalFourthData.Bq 7653 = (273243287924983:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7653 = 273243287924983 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7653 = (15653:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7653
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7654) ≤ val WuPaper.ClassicalFourthData.Bq 7654
    have hp : val WuPaper.ClassicalFourthData.Bq 7654 = (273247759704152:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7654 = 273247759704152 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7654 = (7827:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7654
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7655) ≤ val WuPaper.ClassicalFourthData.Bq 7655
    have hp : val WuPaper.ClassicalFourthData.Bq 7655 = (273252229030735:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7655 = 273252229030735 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7655 = (3131:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7655
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7656) ≤ val WuPaper.ClassicalFourthData.Bq 7656
    have hp : val WuPaper.ClassicalFourthData.Bq 7656 = (273256695905525:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7656 = 273256695905525 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7656 = (1957:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7656
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7657) ≤ val WuPaper.ClassicalFourthData.Bq 7657
    have hp : val WuPaper.ClassicalFourthData.Bq 7657 = (273261160329315:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7657 = 273261160329315 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7657 = (15657:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7657
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7658) ≤ val WuPaper.ClassicalFourthData.Bq 7658
    have hp : val WuPaper.ClassicalFourthData.Bq 7658 = (273265622302896:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7658 = 273265622302896 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7658 = (7829:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7658
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7659) ≤ val WuPaper.ClassicalFourthData.Bq 7659
    have hp : val WuPaper.ClassicalFourthData.Bq 7659 = (273270081827060:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7659 = 273270081827060 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7659 = (15659:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7659
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7660) ≤ val WuPaper.ClassicalFourthData.Bq 7660
    have hp : val WuPaper.ClassicalFourthData.Bq 7660 = (273274538902600:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7660 = 273274538902600 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7660 = (783:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7660
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7661) ≤ val WuPaper.ClassicalFourthData.Bq 7661
    have hp : val WuPaper.ClassicalFourthData.Bq 7661 = (273278993530306:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7661 = 273278993530306 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7661 = (15661:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7661
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7662) ≤ val WuPaper.ClassicalFourthData.Bq 7662
    have hp : val WuPaper.ClassicalFourthData.Bq 7662 = (273283445710970:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7662 = 273283445710970 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7662 = (7831:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7662
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7663) ≤ val WuPaper.ClassicalFourthData.Bq 7663
    have hp : val WuPaper.ClassicalFourthData.Bq 7663 = (273287895445382:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7663 = 273287895445382 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7663 = (15663:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7663
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_478
