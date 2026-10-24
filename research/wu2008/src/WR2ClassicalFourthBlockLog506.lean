import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints506
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_506 (j : Fin 16) (hj : 16*506+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*506+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*506+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8096) ≤ val WuPaper.ClassicalFourthData.Bq 8096
    have hp : val WuPaper.ClassicalFourthData.Bq 8096 = (274995143717794:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8096 = 274995143717794 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8096 = (503:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8096
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8097) ≤ val WuPaper.ClassicalFourthData.Bq 8097
    have hp : val WuPaper.ClassicalFourthData.Bq 8097 = (274998602686450:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8097 = 274998602686450 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8097 = (16097:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8097
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8098) ≤ val WuPaper.ClassicalFourthData.Bq 8098
    have hp : val WuPaper.ClassicalFourthData.Bq 8098 = (275002059527386:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8098 = 275002059527386 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8098 = (8049:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8098
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8099) ≤ val WuPaper.ClassicalFourthData.Bq 8099
    have hp : val WuPaper.ClassicalFourthData.Bq 8099 = (275005514241279:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8099 = 275005514241279 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8099 = (16099:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8099
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8100) ≤ val WuPaper.ClassicalFourthData.Bq 8100
    have hp : val WuPaper.ClassicalFourthData.Bq 8100 = (275008966828807:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8100 = 275008966828807 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8100 = (161:ℝ)/40 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8100
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8101) ≤ val WuPaper.ClassicalFourthData.Bq 8101
    have hp : val WuPaper.ClassicalFourthData.Bq 8101 = (275012417290647:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8101 = 275012417290647 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8101 = (16101:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8101
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8102) ≤ val WuPaper.ClassicalFourthData.Bq 8102
    have hp : val WuPaper.ClassicalFourthData.Bq 8102 = (275015865627474:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8102 = 275015865627474 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8102 = (8051:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8102
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8103) ≤ val WuPaper.ClassicalFourthData.Bq 8103
    have hp : val WuPaper.ClassicalFourthData.Bq 8103 = (275019311839965:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8103 = 275019311839965 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8103 = (16103:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8103
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8104) ≤ val WuPaper.ClassicalFourthData.Bq 8104
    have hp : val WuPaper.ClassicalFourthData.Bq 8104 = (275022755928796:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8104 = 275022755928796 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8104 = (2013:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8104
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8105) ≤ val WuPaper.ClassicalFourthData.Bq 8105
    have hp : val WuPaper.ClassicalFourthData.Bq 8105 = (275026197894643:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8105 = 275026197894643 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8105 = (3221:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8105
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8106) ≤ val WuPaper.ClassicalFourthData.Bq 8106
    have hp : val WuPaper.ClassicalFourthData.Bq 8106 = (275029637738182:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8106 = 275029637738182 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8106 = (8053:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8106
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8107) ≤ val WuPaper.ClassicalFourthData.Bq 8107
    have hp : val WuPaper.ClassicalFourthData.Bq 8107 = (275033075460086:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8107 = 275033075460086 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8107 = (16107:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8107
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8108) ≤ val WuPaper.ClassicalFourthData.Bq 8108
    have hp : val WuPaper.ClassicalFourthData.Bq 8108 = (275036511061033:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8108 = 275036511061033 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8108 = (4027:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8108
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8109) ≤ val WuPaper.ClassicalFourthData.Bq 8109
    have hp : val WuPaper.ClassicalFourthData.Bq 8109 = (275039944541695:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8109 = 275039944541695 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8109 = (16109:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8109
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8110) ≤ val WuPaper.ClassicalFourthData.Bq 8110
    have hp : val WuPaper.ClassicalFourthData.Bq 8110 = (275043375902749:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8110 = 275043375902749 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8110 = (1611:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8110
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8111) ≤ val WuPaper.ClassicalFourthData.Bq 8111
    have hp : val WuPaper.ClassicalFourthData.Bq 8111 = (275046805144867:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8111 = 275046805144867 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8111 = (16111:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8111
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_506
