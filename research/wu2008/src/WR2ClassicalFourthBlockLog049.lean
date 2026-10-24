import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints049
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_049 (j : Fin 16) (hj : 16*49+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*49+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*49+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 784) ≤ val WuPaper.ClassicalFourthData.Bq 784
    have hp : val WuPaper.ClassicalFourthData.Bq 784 = (81503941497469:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 784 = 81503941497469 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 784 = (549:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_784
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 785) ≤ val WuPaper.ClassicalFourthData.Bq 785
    have hp : val WuPaper.ClassicalFourthData.Bq 785 = (81589829839512:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 785 = 81589829839512 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 785 = (1757:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_785
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 786) ≤ val WuPaper.ClassicalFourthData.Bq 786
    have hp : val WuPaper.ClassicalFourthData.Bq 786 = (81675678746320:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 786 = 81675678746320 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 786 = (4393:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_786
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 787) ≤ val WuPaper.ClassicalFourthData.Bq 787
    have hp : val WuPaper.ClassicalFourthData.Bq 787 = (81761488239664:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 787 = 81761488239664 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 787 = (8787:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_787
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 788) ≤ val WuPaper.ClassicalFourthData.Bq 788
    have hp : val WuPaper.ClassicalFourthData.Bq 788 = (81847258341300:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 788 = 81847258341300 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 788 = (2197:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_788
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 789) ≤ val WuPaper.ClassicalFourthData.Bq 789
    have hp : val WuPaper.ClassicalFourthData.Bq 789 = (81932989072970:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 789 = 81932989072970 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 789 = (8789:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_789
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 790) ≤ val WuPaper.ClassicalFourthData.Bq 790
    have hp : val WuPaper.ClassicalFourthData.Bq 790 = (82018680456398:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 790 = 82018680456398 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 790 = (879:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_790
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 791) ≤ val WuPaper.ClassicalFourthData.Bq 791
    have hp : val WuPaper.ClassicalFourthData.Bq 791 = (82104332513296:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 791 = 82104332513296 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 791 = (8791:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_791
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 792) ≤ val WuPaper.ClassicalFourthData.Bq 792
    have hp : val WuPaper.ClassicalFourthData.Bq 792 = (82189945265359:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 792 = 82189945265359 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 792 = (1099:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_792
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 793) ≤ val WuPaper.ClassicalFourthData.Bq 793
    have hp : val WuPaper.ClassicalFourthData.Bq 793 = (82275518734268:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 793 = 82275518734268 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 793 = (8793:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_793
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 794) ≤ val WuPaper.ClassicalFourthData.Bq 794
    have hp : val WuPaper.ClassicalFourthData.Bq 794 = (82361052941689:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 794 = 82361052941689 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 794 = (4397:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_794
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 795) ≤ val WuPaper.ClassicalFourthData.Bq 795
    have hp : val WuPaper.ClassicalFourthData.Bq 795 = (82446547909272:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 795 = 82446547909272 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 795 = (1759:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_795
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 796) ≤ val WuPaper.ClassicalFourthData.Bq 796
    have hp : val WuPaper.ClassicalFourthData.Bq 796 = (82532003658653:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 796 = 82532003658653 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 796 = (2199:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_796
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 797) ≤ val WuPaper.ClassicalFourthData.Bq 797
    have hp : val WuPaper.ClassicalFourthData.Bq 797 = (82617420211453:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 797 = 82617420211453 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 797 = (8797:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_797
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 798) ≤ val WuPaper.ClassicalFourthData.Bq 798
    have hp : val WuPaper.ClassicalFourthData.Bq 798 = (82702797589276:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 798 = 82702797589276 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 798 = (4399:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_798
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 799) ≤ val WuPaper.ClassicalFourthData.Bq 799
    have hp : val WuPaper.ClassicalFourthData.Bq 799 = (82788135813715:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 799 = 82788135813715 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 799 = (8799:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_799
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_049
