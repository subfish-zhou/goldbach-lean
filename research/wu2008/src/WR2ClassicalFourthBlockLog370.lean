import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints370
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_370 (j : Fin 16) (hj : 16*370+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*370+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*370+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5920) ≤ val WuPaper.ClassicalFourthData.Bq 5920
    have hp : val WuPaper.ClassicalFourthData.Bq 5920 = (260993839131295:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5920 = 260993839131295 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5920 = (87:ℝ)/25 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5920
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5921) ≤ val WuPaper.ClassicalFourthData.Bq 5921
    have hp : val WuPaper.ClassicalFourthData.Bq 5921 = (261004054751207:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5921 = 261004054751207 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5921 = (13921:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5921
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5922) ≤ val WuPaper.ClassicalFourthData.Bq 5922
    have hp : val WuPaper.ClassicalFourthData.Bq 5922 = (261014265984480:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5922 = 261014265984480 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5922 = (6961:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5922
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5923) ≤ val WuPaper.ClassicalFourthData.Bq 5923
    have hp : val WuPaper.ClassicalFourthData.Bq 5923 = (261024472832645:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5923 = 261024472832645 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5923 = (13923:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5923
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5924) ≤ val WuPaper.ClassicalFourthData.Bq 5924
    have hp : val WuPaper.ClassicalFourthData.Bq 5924 = (261034675297236:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5924 = 261034675297236 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5924 = (3481:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5924
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5925) ≤ val WuPaper.ClassicalFourthData.Bq 5925
    have hp : val WuPaper.ClassicalFourthData.Bq 5925 = (261044873379785:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5925 = 261044873379785 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5925 = (557:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5925
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5926) ≤ val WuPaper.ClassicalFourthData.Bq 5926
    have hp : val WuPaper.ClassicalFourthData.Bq 5926 = (261055067081825:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5926 = 261055067081825 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5926 = (6963:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5926
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5927) ≤ val WuPaper.ClassicalFourthData.Bq 5927
    have hp : val WuPaper.ClassicalFourthData.Bq 5927 = (261065256404885:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5927 = 261065256404885 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5927 = (13927:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5927
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5928) ≤ val WuPaper.ClassicalFourthData.Bq 5928
    have hp : val WuPaper.ClassicalFourthData.Bq 5928 = (261075441350497:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5928 = 261075441350497 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5928 = (1741:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5928
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5929) ≤ val WuPaper.ClassicalFourthData.Bq 5929
    have hp : val WuPaper.ClassicalFourthData.Bq 5929 = (261085621920190:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5929 = 261085621920190 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5929 = (13929:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5929
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5930) ≤ val WuPaper.ClassicalFourthData.Bq 5930
    have hp : val WuPaper.ClassicalFourthData.Bq 5930 = (261095798115493:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5930 = 261095798115493 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5930 = (1393:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5930
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5931) ≤ val WuPaper.ClassicalFourthData.Bq 5931
    have hp : val WuPaper.ClassicalFourthData.Bq 5931 = (261105969937936:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5931 = 261105969937936 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5931 = (13931:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5931
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5932) ≤ val WuPaper.ClassicalFourthData.Bq 5932
    have hp : val WuPaper.ClassicalFourthData.Bq 5932 = (261116137389045:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5932 = 261116137389045 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5932 = (3483:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5932
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5933) ≤ val WuPaper.ClassicalFourthData.Bq 5933
    have hp : val WuPaper.ClassicalFourthData.Bq 5933 = (261126300470349:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5933 = 261126300470349 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5933 = (13933:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5933
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5934) ≤ val WuPaper.ClassicalFourthData.Bq 5934
    have hp : val WuPaper.ClassicalFourthData.Bq 5934 = (261136459183374:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5934 = 261136459183374 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5934 = (6967:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5934
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5935) ≤ val WuPaper.ClassicalFourthData.Bq 5935
    have hp : val WuPaper.ClassicalFourthData.Bq 5935 = (261146613529646:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5935 = 261146613529646 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5935 = (2787:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5935
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_370
