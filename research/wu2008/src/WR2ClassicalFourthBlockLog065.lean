import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints065
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_065 (j : Fin 16) (hj : 16*65+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*65+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*65+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1040) ≤ val WuPaper.ClassicalFourthData.Bq 1040
    have hp : val WuPaper.ClassicalFourthData.Bq 1040 = (102261823435127:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1040 = 102261823435127 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1040 = (113:ℝ)/50 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1040
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1041) ≤ val WuPaper.ClassicalFourthData.Bq 1041
    have hp : val WuPaper.ClassicalFourthData.Bq 1041 = (102338287349012:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1041 = 102338287349012 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1041 = (9041:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1041
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1042) ≤ val WuPaper.ClassicalFourthData.Bq 1042
    have hp : val WuPaper.ClassicalFourthData.Bq 1042 = (102414716941313:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1042 = 102414716941313 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1042 = (4521:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1042
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1043) ≤ val WuPaper.ClassicalFourthData.Bq 1043
    have hp : val WuPaper.ClassicalFourthData.Bq 1043 = (102491112230321:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1043 = 102491112230321 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1043 = (9043:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1043
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1044) ≤ val WuPaper.ClassicalFourthData.Bq 1044
    have hp : val WuPaper.ClassicalFourthData.Bq 1044 = (102567473234314:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1044 = 102567473234314 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1044 = (2261:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1044
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1045) ≤ val WuPaper.ClassicalFourthData.Bq 1045
    have hp : val WuPaper.ClassicalFourthData.Bq 1045 = (102643799971557:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1045 = 102643799971557 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1045 = (1809:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1045
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1046) ≤ val WuPaper.ClassicalFourthData.Bq 1046
    have hp : val WuPaper.ClassicalFourthData.Bq 1046 = (102720092460304:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1046 = 102720092460304 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1046 = (4523:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1046
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1047) ≤ val WuPaper.ClassicalFourthData.Bq 1047
    have hp : val WuPaper.ClassicalFourthData.Bq 1047 = (102796350718796:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1047 = 102796350718796 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1047 = (9047:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1047
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1048) ≤ val WuPaper.ClassicalFourthData.Bq 1048
    have hp : val WuPaper.ClassicalFourthData.Bq 1048 = (102872574765262:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1048 = 102872574765262 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1048 = (1131:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1048
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1049) ≤ val WuPaper.ClassicalFourthData.Bq 1049
    have hp : val WuPaper.ClassicalFourthData.Bq 1049 = (102948764617920:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1049 = 102948764617920 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1049 = (9049:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1049
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1050) ≤ val WuPaper.ClassicalFourthData.Bq 1050
    have hp : val WuPaper.ClassicalFourthData.Bq 1050 = (103024920294974:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1050 = 103024920294974 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1050 = (181:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1050
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1051) ≤ val WuPaper.ClassicalFourthData.Bq 1051
    have hp : val WuPaper.ClassicalFourthData.Bq 1051 = (103101041814618:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1051 = 103101041814618 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1051 = (9051:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1051
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1052) ≤ val WuPaper.ClassicalFourthData.Bq 1052
    have hp : val WuPaper.ClassicalFourthData.Bq 1052 = (103177129195031:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1052 = 103177129195031 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1052 = (2263:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1052
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1053) ≤ val WuPaper.ClassicalFourthData.Bq 1053
    have hp : val WuPaper.ClassicalFourthData.Bq 1053 = (103253182454383:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1053 = 103253182454383 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1053 = (9053:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1053
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1054) ≤ val WuPaper.ClassicalFourthData.Bq 1054
    have hp : val WuPaper.ClassicalFourthData.Bq 1054 = (103329201610830:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1054 = 103329201610830 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1054 = (4527:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1054
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1055) ≤ val WuPaper.ClassicalFourthData.Bq 1055
    have hp : val WuPaper.ClassicalFourthData.Bq 1055 = (103405186682516:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1055 = 103405186682516 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1055 = (1811:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1055
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_065
