import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints047
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_047 (j : Fin 16) (hj : 16*47+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*47+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*47+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 752) ≤ val WuPaper.ClassicalFourthData.Bq 752
    have hp : val WuPaper.ClassicalFourthData.Bq 752 = (78734561672968:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 752 = 78734561672968 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 752 = (547:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_752
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 753) ≤ val WuPaper.ClassicalFourthData.Bq 753
    have hp : val WuPaper.ClassicalFourthData.Bq 753 = (78821723528839:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 753 = 78821723528839 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 753 = (8753:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_753
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 754) ≤ val WuPaper.ClassicalFourthData.Bq 754
    have hp : val WuPaper.ClassicalFourthData.Bq 754 = (78908845244740:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 754 = 78908845244740 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 754 = (4377:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_754
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 755) ≤ val WuPaper.ClassicalFourthData.Bq 755
    have hp : val WuPaper.ClassicalFourthData.Bq 755 = (78995926842930:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 755 = 78995926842930 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 755 = (1751:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_755
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 756) ≤ val WuPaper.ClassicalFourthData.Bq 756
    have hp : val WuPaper.ClassicalFourthData.Bq 756 = (79082968345658:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 756 = 79082968345658 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 756 = (2189:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_756
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 757) ≤ val WuPaper.ClassicalFourthData.Bq 757
    have hp : val WuPaper.ClassicalFourthData.Bq 757 = (79169969775154:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 757 = 79169969775154 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 757 = (8757:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_757
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 758) ≤ val WuPaper.ClassicalFourthData.Bq 758
    have hp : val WuPaper.ClassicalFourthData.Bq 758 = (79256931153632:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 758 = 79256931153632 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 758 = (4379:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_758
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 759) ≤ val WuPaper.ClassicalFourthData.Bq 759
    have hp : val WuPaper.ClassicalFourthData.Bq 759 = (79343852503292:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 759 = 79343852503292 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 759 = (8759:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_759
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 760) ≤ val WuPaper.ClassicalFourthData.Bq 760
    have hp : val WuPaper.ClassicalFourthData.Bq 760 = (79430733846319:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 760 = 79430733846319 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 760 = (219:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_760
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 761) ≤ val WuPaper.ClassicalFourthData.Bq 761
    have hp : val WuPaper.ClassicalFourthData.Bq 761 = (79517575204882:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 761 = 79517575204882 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 761 = (8761:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_761
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 762) ≤ val WuPaper.ClassicalFourthData.Bq 762
    have hp : val WuPaper.ClassicalFourthData.Bq 762 = (79604376601133:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 762 = 79604376601133 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 762 = (4381:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_762
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 763) ≤ val WuPaper.ClassicalFourthData.Bq 763
    have hp : val WuPaper.ClassicalFourthData.Bq 763 = (79691138057210:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 763 = 79691138057210 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 763 = (8763:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_763
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 764) ≤ val WuPaper.ClassicalFourthData.Bq 764
    have hp : val WuPaper.ClassicalFourthData.Bq 764 = (79777859595237:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 764 = 79777859595237 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 764 = (2191:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_764
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 765) ≤ val WuPaper.ClassicalFourthData.Bq 765
    have hp : val WuPaper.ClassicalFourthData.Bq 765 = (79864541237319:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 765 = 79864541237319 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 765 = (1753:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_765
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 766) ≤ val WuPaper.ClassicalFourthData.Bq 766
    have hp : val WuPaper.ClassicalFourthData.Bq 766 = (79951183005549:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 766 = 79951183005549 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 766 = (4383:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_766
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 767) ≤ val WuPaper.ClassicalFourthData.Bq 767
    have hp : val WuPaper.ClassicalFourthData.Bq 767 = (80037784922003:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 767 = 80037784922003 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 767 = (8767:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_767
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_047
