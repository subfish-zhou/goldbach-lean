import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints104
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_104 (j : Fin 16) (hj : 16*104+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*104+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*104+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1664) ≤ val WuPaper.ClassicalFourthData.Bq 1664
    have hp : val WuPaper.ClassicalFourthData.Bq 1664 = (143971852347487:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1664 = 143971852347487 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1664 = (302:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1664
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1665) ≤ val WuPaper.ClassicalFourthData.Bq 1665
    have hp : val WuPaper.ClassicalFourthData.Bq 1665 = (144030018979857:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1665 = 144030018979857 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1665 = (1933:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1665
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1666) ≤ val WuPaper.ClassicalFourthData.Bq 1666
    have hp : val WuPaper.ClassicalFourthData.Bq 1666 = (144088160682158:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1666 = 144088160682158 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1666 = (4833:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1666
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1667) ≤ val WuPaper.ClassicalFourthData.Bq 1667
    have hp : val WuPaper.ClassicalFourthData.Bq 1667 = (144146277466677:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1667 = 144146277466677 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1667 = (9667:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1667
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1668) ≤ val WuPaper.ClassicalFourthData.Bq 1668
    have hp : val WuPaper.ClassicalFourthData.Bq 1668 = (144204369345695:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1668 = 144204369345695 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1668 = (2417:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1668
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1669) ≤ val WuPaper.ClassicalFourthData.Bq 1669
    have hp : val WuPaper.ClassicalFourthData.Bq 1669 = (144262436331483:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1669 = 144262436331483 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1669 = (9669:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1669
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1670) ≤ val WuPaper.ClassicalFourthData.Bq 1670
    have hp : val WuPaper.ClassicalFourthData.Bq 1670 = (144320478436307:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1670 = 144320478436307 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1670 = (967:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1670
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1671) ≤ val WuPaper.ClassicalFourthData.Bq 1671
    have hp : val WuPaper.ClassicalFourthData.Bq 1671 = (144378495672423:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1671 = 144378495672423 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1671 = (9671:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1671
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1672) ≤ val WuPaper.ClassicalFourthData.Bq 1672
    have hp : val WuPaper.ClassicalFourthData.Bq 1672 = (144436488052083:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1672 = 144436488052083 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1672 = (1209:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1672
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1673) ≤ val WuPaper.ClassicalFourthData.Bq 1673
    have hp : val WuPaper.ClassicalFourthData.Bq 1673 = (144494455587528:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1673 = 144494455587528 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1673 = (9673:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1673
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1674) ≤ val WuPaper.ClassicalFourthData.Bq 1674
    have hp : val WuPaper.ClassicalFourthData.Bq 1674 = (144552398290994:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1674 = 144552398290994 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1674 = (4837:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1674
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1675) ≤ val WuPaper.ClassicalFourthData.Bq 1675
    have hp : val WuPaper.ClassicalFourthData.Bq 1675 = (144610316174709:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1675 = 144610316174709 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1675 = (387:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1675
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1676) ≤ val WuPaper.ClassicalFourthData.Bq 1676
    have hp : val WuPaper.ClassicalFourthData.Bq 1676 = (144668209250892:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1676 = 144668209250892 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1676 = (2419:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1676
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1677) ≤ val WuPaper.ClassicalFourthData.Bq 1677
    have hp : val WuPaper.ClassicalFourthData.Bq 1677 = (144726077531756:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1677 = 144726077531756 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1677 = (9677:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1677
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1678) ≤ val WuPaper.ClassicalFourthData.Bq 1678
    have hp : val WuPaper.ClassicalFourthData.Bq 1678 = (144783921029506:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1678 = 144783921029506 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1678 = (4839:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1678
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1679) ≤ val WuPaper.ClassicalFourthData.Bq 1679
    have hp : val WuPaper.ClassicalFourthData.Bq 1679 = (144841739756341:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1679 = 144841739756341 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1679 = (9679:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1679
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_104
