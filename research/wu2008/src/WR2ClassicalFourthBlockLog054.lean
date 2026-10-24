import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints054
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_054 (j : Fin 16) (hj : 16*54+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*54+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*54+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 864) ≤ val WuPaper.ClassicalFourthData.Bq 864
    have hp : val WuPaper.ClassicalFourthData.Bq 864 = (88252158638979:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 864 = 88252158638979 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 864 = (277:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_864
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 865) ≤ val WuPaper.ClassicalFourthData.Bq 865
    have hp : val WuPaper.ClassicalFourthData.Bq 865 = (88334959737430:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 865 = 88334959737430 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 865 = (1773:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_865
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 866) ≤ val WuPaper.ClassicalFourthData.Bq 866
    have hp : val WuPaper.ClassicalFourthData.Bq 866 = (88417723095620:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 866 = 88417723095620 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 866 = (4433:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_866
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 867) ≤ val WuPaper.ClassicalFourthData.Bq 867
    have hp : val WuPaper.ClassicalFourthData.Bq 867 = (88500448734150:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 867 = 88500448734150 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 867 = (8867:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_867
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 868) ≤ val WuPaper.ClassicalFourthData.Bq 868
    have hp : val WuPaper.ClassicalFourthData.Bq 868 = (88583136673609:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 868 = 88583136673609 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 868 = (2217:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_868
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 869) ≤ val WuPaper.ClassicalFourthData.Bq 869
    have hp : val WuPaper.ClassicalFourthData.Bq 869 = (88665786934570:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 869 = 88665786934570 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 869 = (8869:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_869
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 870) ≤ val WuPaper.ClassicalFourthData.Bq 870
    have hp : val WuPaper.ClassicalFourthData.Bq 870 = (88748399537591:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 870 = 88748399537591 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 870 = (887:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_870
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 871) ≤ val WuPaper.ClassicalFourthData.Bq 871
    have hp : val WuPaper.ClassicalFourthData.Bq 871 = (88830974503220:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 871 = 88830974503220 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 871 = (8871:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_871
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 872) ≤ val WuPaper.ClassicalFourthData.Bq 872
    have hp : val WuPaper.ClassicalFourthData.Bq 872 = (88913511851987:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 872 = 88913511851987 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 872 = (1109:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_872
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 873) ≤ val WuPaper.ClassicalFourthData.Bq 873
    have hp : val WuPaper.ClassicalFourthData.Bq 873 = (88996011604409:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 873 = 88996011604409 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 873 = (8873:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_873
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 874) ≤ val WuPaper.ClassicalFourthData.Bq 874
    have hp : val WuPaper.ClassicalFourthData.Bq 874 = (89078473780989:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 874 = 89078473780989 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 874 = (4437:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_874
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 875) ≤ val WuPaper.ClassicalFourthData.Bq 875
    have hp : val WuPaper.ClassicalFourthData.Bq 875 = (89160898402218:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 875 = 89160898402218 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 875 = (71:ℝ)/32 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_875
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 876) ≤ val WuPaper.ClassicalFourthData.Bq 876
    have hp : val WuPaper.ClassicalFourthData.Bq 876 = (89243285488569:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 876 = 89243285488569 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 876 = (2219:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_876
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 877) ≤ val WuPaper.ClassicalFourthData.Bq 877
    have hp : val WuPaper.ClassicalFourthData.Bq 877 = (89325635060505:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 877 = 89325635060505 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 877 = (8877:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_877
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 878) ≤ val WuPaper.ClassicalFourthData.Bq 878
    have hp : val WuPaper.ClassicalFourthData.Bq 878 = (89407947138472:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 878 = 89407947138472 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 878 = (4439:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_878
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 879) ≤ val WuPaper.ClassicalFourthData.Bq 879
    have hp : val WuPaper.ClassicalFourthData.Bq 879 = (89490221742904:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 879 = 89490221742904 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 879 = (8879:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_879
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_054
