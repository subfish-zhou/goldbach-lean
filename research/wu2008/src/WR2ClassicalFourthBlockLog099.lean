import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints099
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_099 (j : Fin 16) (hj : 16*99+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*99+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*99+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1584) ≤ val WuPaper.ClassicalFourthData.Bq 1584
    have hp : val WuPaper.ClassicalFourthData.Bq 1584 = (139236646218774:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1584 = 139236646218774 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1584 = (599:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1584
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1585) ≤ val WuPaper.ClassicalFourthData.Bq 1585
    have hp : val WuPaper.ClassicalFourthData.Bq 1585 = (139296847741794:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1585 = 139296847741794 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1585 = (1917:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1585
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1586) ≤ val WuPaper.ClassicalFourthData.Bq 1586
    have hp : val WuPaper.ClassicalFourthData.Bq 1586 = (139357023326975:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1586 = 139357023326975 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1586 = (4793:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1586
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1587) ≤ val WuPaper.ClassicalFourthData.Bq 1587
    have hp : val WuPaper.ClassicalFourthData.Bq 1587 = (139417172987221:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1587 = 139417172987221 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1587 = (9587:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1587
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1588) ≤ val WuPaper.ClassicalFourthData.Bq 1588
    have hp : val WuPaper.ClassicalFourthData.Bq 1588 = (139477296735430:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1588 = 139477296735430 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1588 = (2397:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1588
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1589) ≤ val WuPaper.ClassicalFourthData.Bq 1589
    have hp : val WuPaper.ClassicalFourthData.Bq 1589 = (139537394584491:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1589 = 139537394584491 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1589 = (9589:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1589
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1590) ≤ val WuPaper.ClassicalFourthData.Bq 1590
    have hp : val WuPaper.ClassicalFourthData.Bq 1590 = (139597466547286:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1590 = 139597466547286 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1590 = (959:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1590
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1591) ≤ val WuPaper.ClassicalFourthData.Bq 1591
    have hp : val WuPaper.ClassicalFourthData.Bq 1591 = (139657512636688:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1591 = 139657512636688 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1591 = (9591:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1591
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1592) ≤ val WuPaper.ClassicalFourthData.Bq 1592
    have hp : val WuPaper.ClassicalFourthData.Bq 1592 = (139717532865563:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1592 = 139717532865563 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1592 = (1199:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1592
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1593) ≤ val WuPaper.ClassicalFourthData.Bq 1593
    have hp : val WuPaper.ClassicalFourthData.Bq 1593 = (139777527246768:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1593 = 139777527246768 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1593 = (9593:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1593
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1594) ≤ val WuPaper.ClassicalFourthData.Bq 1594
    have hp : val WuPaper.ClassicalFourthData.Bq 1594 = (139837495793153:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1594 = 139837495793153 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1594 = (4797:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1594
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1595) ≤ val WuPaper.ClassicalFourthData.Bq 1595
    have hp : val WuPaper.ClassicalFourthData.Bq 1595 = (139897438517561:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1595 = 139897438517561 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1595 = (1919:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1595
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1596) ≤ val WuPaper.ClassicalFourthData.Bq 1596
    have hp : val WuPaper.ClassicalFourthData.Bq 1596 = (139957355432824:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1596 = 139957355432824 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1596 = (2399:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1596
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1597) ≤ val WuPaper.ClassicalFourthData.Bq 1597
    have hp : val WuPaper.ClassicalFourthData.Bq 1597 = (140017246551770:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1597 = 140017246551770 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1597 = (9597:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1597
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1598) ≤ val WuPaper.ClassicalFourthData.Bq 1598
    have hp : val WuPaper.ClassicalFourthData.Bq 1598 = (140077111887215:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1598 = 140077111887215 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1598 = (4799:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1598
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1599) ≤ val WuPaper.ClassicalFourthData.Bq 1599
    have hp : val WuPaper.ClassicalFourthData.Bq 1599 = (140136951451971:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1599 = 140136951451971 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1599 = (9599:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1599
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_099
