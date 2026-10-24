import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints297
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_297 (j : Fin 16) (hj : 16*297+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*297+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*297+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4752) ≤ val WuPaper.ClassicalFourthData.Bq 4752
    have hp : val WuPaper.ClassicalFourthData.Bq 4752 = (245604731668675:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4752 = 245604731668675 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4752 = (797:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4752
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4753) ≤ val WuPaper.ClassicalFourthData.Bq 4753
    have hp : val WuPaper.ClassicalFourthData.Bq 4753 = (245621308752580:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4753 = 245621308752580 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4753 = (12753:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4753
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4754) ≤ val WuPaper.ClassicalFourthData.Bq 4754
    have hp : val WuPaper.ClassicalFourthData.Bq 4754 = (245637879143426:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4754 = 245637879143426 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4754 = (6377:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4754
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4755) ≤ val WuPaper.ClassicalFourthData.Bq 4755
    have hp : val WuPaper.ClassicalFourthData.Bq 4755 = (245654442843724:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4755 = 245654442843724 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4755 = (2551:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4755
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4756) ≤ val WuPaper.ClassicalFourthData.Bq 4756
    have hp : val WuPaper.ClassicalFourthData.Bq 4756 = (245670999855982:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4756 = 245670999855982 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4756 = (3189:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4756
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4757) ≤ val WuPaper.ClassicalFourthData.Bq 4757
    have hp : val WuPaper.ClassicalFourthData.Bq 4757 = (245687550182707:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4757 = 245687550182707 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4757 = (12757:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4757
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4758) ≤ val WuPaper.ClassicalFourthData.Bq 4758
    have hp : val WuPaper.ClassicalFourthData.Bq 4758 = (245704093826405:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4758 = 245704093826405 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4758 = (6379:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4758
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4759) ≤ val WuPaper.ClassicalFourthData.Bq 4759
    have hp : val WuPaper.ClassicalFourthData.Bq 4759 = (245720630789580:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4759 = 245720630789580 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4759 = (12759:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4759
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4760) ≤ val WuPaper.ClassicalFourthData.Bq 4760
    have hp : val WuPaper.ClassicalFourthData.Bq 4760 = (245737161074737:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4760 = 245737161074737 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4760 = (319:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4760
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4761) ≤ val WuPaper.ClassicalFourthData.Bq 4761
    have hp : val WuPaper.ClassicalFourthData.Bq 4761 = (245753684684378:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4761 = 245753684684378 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4761 = (12761:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4761
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4762) ≤ val WuPaper.ClassicalFourthData.Bq 4762
    have hp : val WuPaper.ClassicalFourthData.Bq 4762 = (245770201621005:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4762 = 245770201621005 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4762 = (6381:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4762
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4763) ≤ val WuPaper.ClassicalFourthData.Bq 4763
    have hp : val WuPaper.ClassicalFourthData.Bq 4763 = (245786711887119:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4763 = 245786711887119 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4763 = (12763:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4763
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4764) ≤ val WuPaper.ClassicalFourthData.Bq 4764
    have hp : val WuPaper.ClassicalFourthData.Bq 4764 = (245803215485218:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4764 = 245803215485218 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4764 = (3191:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4764
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4765) ≤ val WuPaper.ClassicalFourthData.Bq 4765
    have hp : val WuPaper.ClassicalFourthData.Bq 4765 = (245819712417801:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4765 = 245819712417801 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4765 = (2553:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4765
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4766) ≤ val WuPaper.ClassicalFourthData.Bq 4766
    have hp : val WuPaper.ClassicalFourthData.Bq 4766 = (245836202687366:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4766 = 245836202687366 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4766 = (6383:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4766
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4767) ≤ val WuPaper.ClassicalFourthData.Bq 4767
    have hp : val WuPaper.ClassicalFourthData.Bq 4767 = (245852686296408:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4767 = 245852686296408 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4767 = (12767:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4767
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_297
