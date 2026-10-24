import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints302
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_302 (j : Fin 16) (hj : 16*302+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*302+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*302+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4832) ≤ val WuPaper.ClassicalFourthData.Bq 4832
    have hp : val WuPaper.ClassicalFourthData.Bq 4832 = (246909952747771:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4832 = 246909952747771 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4832 = (401:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4832
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4833) ≤ val WuPaper.ClassicalFourthData.Bq 4833
    have hp : val WuPaper.ClassicalFourthData.Bq 4833 = (246926002226481:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4833 = 246926002226481 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4833 = (12833:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4833
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4834) ≤ val WuPaper.ClassicalFourthData.Bq 4834
    have hp : val WuPaper.ClassicalFourthData.Bq 4834 = (246942045209427:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4834 = 246942045209427 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4834 = (6417:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4834
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4835) ≤ val WuPaper.ClassicalFourthData.Bq 4835
    have hp : val WuPaper.ClassicalFourthData.Bq 4835 = (246958081699033:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4835 = 246958081699033 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4835 = (2567:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4835
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4836) ≤ val WuPaper.ClassicalFourthData.Bq 4836
    have hp : val WuPaper.ClassicalFourthData.Bq 4836 = (246974111697720:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4836 = 246974111697720 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4836 = (3209:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4836
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4837) ≤ val WuPaper.ClassicalFourthData.Bq 4837
    have hp : val WuPaper.ClassicalFourthData.Bq 4837 = (246990135207908:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4837 = 246990135207908 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4837 = (12837:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4837
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4838) ≤ val WuPaper.ClassicalFourthData.Bq 4838
    have hp : val WuPaper.ClassicalFourthData.Bq 4838 = (247006152232017:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4838 = 247006152232017 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4838 = (6419:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4838
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4839) ≤ val WuPaper.ClassicalFourthData.Bq 4839
    have hp : val WuPaper.ClassicalFourthData.Bq 4839 = (247022162772466:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4839 = 247022162772466 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4839 = (12839:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4839
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4840) ≤ val WuPaper.ClassicalFourthData.Bq 4840
    have hp : val WuPaper.ClassicalFourthData.Bq 4840 = (247038166831671:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4840 = 247038166831671 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4840 = (321:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4840
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4841) ≤ val WuPaper.ClassicalFourthData.Bq 4841
    have hp : val WuPaper.ClassicalFourthData.Bq 4841 = (247054164412048:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4841 = 247054164412048 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4841 = (12841:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4841
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4842) ≤ val WuPaper.ClassicalFourthData.Bq 4842
    have hp : val WuPaper.ClassicalFourthData.Bq 4842 = (247070155516014:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4842 = 247070155516014 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4842 = (6421:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4842
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4843) ≤ val WuPaper.ClassicalFourthData.Bq 4843
    have hp : val WuPaper.ClassicalFourthData.Bq 4843 = (247086140145981:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4843 = 247086140145981 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4843 = (12843:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4843
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4844) ≤ val WuPaper.ClassicalFourthData.Bq 4844
    have hp : val WuPaper.ClassicalFourthData.Bq 4844 = (247102118304363:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4844 = 247102118304363 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4844 = (3211:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4844
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4845) ≤ val WuPaper.ClassicalFourthData.Bq 4845
    have hp : val WuPaper.ClassicalFourthData.Bq 4845 = (247118089993573:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4845 = 247118089993573 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4845 = (2569:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4845
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4846) ≤ val WuPaper.ClassicalFourthData.Bq 4846
    have hp : val WuPaper.ClassicalFourthData.Bq 4846 = (247134055216019:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4846 = 247134055216019 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4846 = (6423:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4846
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4847) ≤ val WuPaper.ClassicalFourthData.Bq 4847
    have hp : val WuPaper.ClassicalFourthData.Bq 4847 = (247150013974114:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4847 = 247150013974114 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4847 = (12847:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4847
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_302
