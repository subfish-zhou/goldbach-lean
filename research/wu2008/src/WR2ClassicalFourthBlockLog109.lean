import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints109
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_109 (j : Fin 16) (hj : 16*109+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*109+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*109+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1744) ≤ val WuPaper.ClassicalFourthData.Bq 1744
    have hp : val WuPaper.ClassicalFourthData.Bq 1744 = (148547401734825:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1744 = 148547401734825 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1744 = (609:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1744
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1745) ≤ val WuPaper.ClassicalFourthData.Bq 1745
    have hp : val WuPaper.ClassicalFourthData.Bq 1745 = (148603612182998:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1745 = 148603612182998 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1745 = (1949:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1745
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1746) ≤ val WuPaper.ClassicalFourthData.Bq 1746
    have hp : val WuPaper.ClassicalFourthData.Bq 1746 = (148659798660869:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1746 = 148659798660869 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1746 = (4873:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1746
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1747) ≤ val WuPaper.ClassicalFourthData.Bq 1747
    have hp : val WuPaper.ClassicalFourthData.Bq 1747 = (148715961180144:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1747 = 148715961180144 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1747 = (9747:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1747
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1748) ≤ val WuPaper.ClassicalFourthData.Bq 1748
    have hp : val WuPaper.ClassicalFourthData.Bq 1748 = (148772099752519:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1748 = 148772099752519 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1748 = (2437:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1748
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1749) ≤ val WuPaper.ClassicalFourthData.Bq 1749
    have hp : val WuPaper.ClassicalFourthData.Bq 1749 = (148828214389687:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1749 = 148828214389687 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1749 = (9749:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1749
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1750) ≤ val WuPaper.ClassicalFourthData.Bq 1750
    have hp : val WuPaper.ClassicalFourthData.Bq 1750 = (148884305103331:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1750 = 148884305103331 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1750 = (39:ℝ)/16 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1750
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1751) ≤ val WuPaper.ClassicalFourthData.Bq 1751
    have hp : val WuPaper.ClassicalFourthData.Bq 1751 = (148940371905129:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1751 = 148940371905129 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1751 = (9751:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1751
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1752) ≤ val WuPaper.ClassicalFourthData.Bq 1752
    have hp : val WuPaper.ClassicalFourthData.Bq 1752 = (148996414806750:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1752 = 148996414806750 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1752 = (1219:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1752
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1753) ≤ val WuPaper.ClassicalFourthData.Bq 1753
    have hp : val WuPaper.ClassicalFourthData.Bq 1753 = (149052433819857:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1753 = 149052433819857 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1753 = (9753:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1753
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1754) ≤ val WuPaper.ClassicalFourthData.Bq 1754
    have hp : val WuPaper.ClassicalFourthData.Bq 1754 = (149108428956107:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1754 = 149108428956107 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1754 = (4877:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1754
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1755) ≤ val WuPaper.ClassicalFourthData.Bq 1755
    have hp : val WuPaper.ClassicalFourthData.Bq 1755 = (149164400227148:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1755 = 149164400227148 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1755 = (1951:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1755
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1756) ≤ val WuPaper.ClassicalFourthData.Bq 1756
    have hp : val WuPaper.ClassicalFourthData.Bq 1756 = (149220347644622:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1756 = 149220347644622 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1756 = (2439:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1756
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1757) ≤ val WuPaper.ClassicalFourthData.Bq 1757
    have hp : val WuPaper.ClassicalFourthData.Bq 1757 = (149276271220163:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1757 = 149276271220163 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1757 = (9757:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1757
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1758) ≤ val WuPaper.ClassicalFourthData.Bq 1758
    have hp : val WuPaper.ClassicalFourthData.Bq 1758 = (149332170965401:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1758 = 149332170965401 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1758 = (4879:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1758
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1759) ≤ val WuPaper.ClassicalFourthData.Bq 1759
    have hp : val WuPaper.ClassicalFourthData.Bq 1759 = (149388046891954:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1759 = 149388046891954 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1759 = (9759:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1759
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_109
