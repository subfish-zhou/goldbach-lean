import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints422
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_422 (j : Fin 16) (hj : 16*422+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*422+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*422+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6752) ≤ val WuPaper.ClassicalFourthData.Bq 6752
    have hp : val WuPaper.ClassicalFourthData.Bq 6752 = (268112099420022:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6752 = 268112099420022 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6752 = (461:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6752
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6753) ≤ val WuPaper.ClassicalFourthData.Bq 6753
    have hp : val WuPaper.ClassicalFourthData.Bq 6753 = (268119141676577:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6753 = 268119141676577 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6753 = (14753:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6753
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6754) ≤ val WuPaper.ClassicalFourthData.Bq 6754
    have hp : val WuPaper.ClassicalFourthData.Bq 6754 = (268126180633790:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6754 = 268126180633790 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6754 = (7377:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6754
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6755) ≤ val WuPaper.ClassicalFourthData.Bq 6755
    have hp : val WuPaper.ClassicalFourthData.Bq 6755 = (268133216292766:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6755 = 268133216292766 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6755 = (2951:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6755
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6756) ≤ val WuPaper.ClassicalFourthData.Bq 6756
    have hp : val WuPaper.ClassicalFourthData.Bq 6756 = (268140248654613:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6756 = 268140248654613 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6756 = (3689:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6756
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6757) ≤ val WuPaper.ClassicalFourthData.Bq 6757
    have hp : val WuPaper.ClassicalFourthData.Bq 6757 = (268147277720436:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6757 = 268147277720436 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6757 = (14757:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6757
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6758) ≤ val WuPaper.ClassicalFourthData.Bq 6758
    have hp : val WuPaper.ClassicalFourthData.Bq 6758 = (268154303491340:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6758 = 268154303491340 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6758 = (7379:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6758
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6759) ≤ val WuPaper.ClassicalFourthData.Bq 6759
    have hp : val WuPaper.ClassicalFourthData.Bq 6759 = (268161325968432:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6759 = 268161325968432 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6759 = (14759:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6759
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6760) ≤ val WuPaper.ClassicalFourthData.Bq 6760
    have hp : val WuPaper.ClassicalFourthData.Bq 6760 = (268168345152815:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6760 = 268168345152815 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6760 = (369:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6760
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6761) ≤ val WuPaper.ClassicalFourthData.Bq 6761
    have hp : val WuPaper.ClassicalFourthData.Bq 6761 = (268175361045595:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6761 = 268175361045595 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6761 = (14761:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6761
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6762) ≤ val WuPaper.ClassicalFourthData.Bq 6762
    have hp : val WuPaper.ClassicalFourthData.Bq 6762 = (268182373647874:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6762 = 268182373647874 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6762 = (7381:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6762
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6763) ≤ val WuPaper.ClassicalFourthData.Bq 6763
    have hp : val WuPaper.ClassicalFourthData.Bq 6763 = (268189382960757:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6763 = 268189382960757 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6763 = (14763:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6763
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6764) ≤ val WuPaper.ClassicalFourthData.Bq 6764
    have hp : val WuPaper.ClassicalFourthData.Bq 6764 = (268196388985346:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6764 = 268196388985346 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6764 = (3691:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6764
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6765) ≤ val WuPaper.ClassicalFourthData.Bq 6765
    have hp : val WuPaper.ClassicalFourthData.Bq 6765 = (268203391722744:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6765 = 268203391722744 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6765 = (2953:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6765
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6766) ≤ val WuPaper.ClassicalFourthData.Bq 6766
    have hp : val WuPaper.ClassicalFourthData.Bq 6766 = (268210391174053:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6766 = 268210391174053 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6766 = (7383:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6766
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6767) ≤ val WuPaper.ClassicalFourthData.Bq 6767
    have hp : val WuPaper.ClassicalFourthData.Bq 6767 = (268217387340376:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6767 = 268217387340376 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6767 = (14767:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6767
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_422
