import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints547
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_547 (j : Fin 16) (hj : 16*547+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*547+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*547+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8752) ≤ val WuPaper.ClassicalFourthData.Bq 8752
    have hp : val WuPaper.ClassicalFourthData.Bq 8752 = (276837096690375:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8752 = 276837096690375 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8752 = (1047:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8752
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8753) ≤ val WuPaper.ClassicalFourthData.Bq 8753
    have hp : val WuPaper.ClassicalFourthData.Bq 8753 = (276839294917022:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8753 = 276839294917022 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8753 = (16753:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8753
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8754) ≤ val WuPaper.ClassicalFourthData.Bq 8754
    have hp : val WuPaper.ClassicalFourthData.Bq 8754 = (276841491413288:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8754 = 276841491413288 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8754 = (8377:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8754
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8755) ≤ val WuPaper.ClassicalFourthData.Bq 8755
    have hp : val WuPaper.ClassicalFourthData.Bq 8755 = (276843686179713:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8755 = 276843686179713 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8755 = (3351:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8755
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8756) ≤ val WuPaper.ClassicalFourthData.Bq 8756
    have hp : val WuPaper.ClassicalFourthData.Bq 8756 = (276845879216837:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8756 = 276845879216837 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8756 = (4189:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8756
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8757) ≤ val WuPaper.ClassicalFourthData.Bq 8757
    have hp : val WuPaper.ClassicalFourthData.Bq 8757 = (276848070525200:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8757 = 276848070525200 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8757 = (16757:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8757
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8758) ≤ val WuPaper.ClassicalFourthData.Bq 8758
    have hp : val WuPaper.ClassicalFourthData.Bq 8758 = (276850260105341:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8758 = 276850260105341 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8758 = (8379:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8758
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8759) ≤ val WuPaper.ClassicalFourthData.Bq 8759
    have hp : val WuPaper.ClassicalFourthData.Bq 8759 = (276852447957799:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8759 = 276852447957799 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8759 = (16759:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8759
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8760) ≤ val WuPaper.ClassicalFourthData.Bq 8760
    have hp : val WuPaper.ClassicalFourthData.Bq 8760 = (276854634083114:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8760 = 276854634083114 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8760 = (419:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8760
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8761) ≤ val WuPaper.ClassicalFourthData.Bq 8761
    have hp : val WuPaper.ClassicalFourthData.Bq 8761 = (276856818481824:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8761 = 276856818481824 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8761 = (16761:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8761
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8762) ≤ val WuPaper.ClassicalFourthData.Bq 8762
    have hp : val WuPaper.ClassicalFourthData.Bq 8762 = (276859001154469:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8762 = 276859001154469 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8762 = (8381:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8762
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8763) ≤ val WuPaper.ClassicalFourthData.Bq 8763
    have hp : val WuPaper.ClassicalFourthData.Bq 8763 = (276861182101586:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8763 = 276861182101586 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8763 = (16763:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8763
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8764) ≤ val WuPaper.ClassicalFourthData.Bq 8764
    have hp : val WuPaper.ClassicalFourthData.Bq 8764 = (276863361323714:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8764 = 276863361323714 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8764 = (4191:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8764
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8765) ≤ val WuPaper.ClassicalFourthData.Bq 8765
    have hp : val WuPaper.ClassicalFourthData.Bq 8765 = (276865538821392:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8765 = 276865538821392 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8765 = (3353:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8765
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8766) ≤ val WuPaper.ClassicalFourthData.Bq 8766
    have hp : val WuPaper.ClassicalFourthData.Bq 8766 = (276867714595157:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8766 = 276867714595157 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8766 = (8383:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8766
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8767) ≤ val WuPaper.ClassicalFourthData.Bq 8767
    have hp : val WuPaper.ClassicalFourthData.Bq 8767 = (276869888645546:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8767 = 276869888645546 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8767 = (16767:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8767
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_547
