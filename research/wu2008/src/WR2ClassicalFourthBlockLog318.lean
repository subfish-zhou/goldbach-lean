import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints318
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_318 (j : Fin 16) (hj : 16*318+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*318+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*318+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5088) ≤ val WuPaper.ClassicalFourthData.Bq 5088
    have hp : val WuPaper.ClassicalFourthData.Bq 5088 = (250813111509446:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5088 = 250813111509446 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5088 = (409:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5088
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5089) ≤ val WuPaper.ClassicalFourthData.Bq 5089
    have hp : val WuPaper.ClassicalFourthData.Bq 5089 = (250827574304147:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5089 = 250827574304147 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5089 = (13089:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5089
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5090) ≤ val WuPaper.ClassicalFourthData.Bq 5090
    have hp : val WuPaper.ClassicalFourthData.Bq 5090 = (250842031190069:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5090 = 250842031190069 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5090 = (1309:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5090
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5091) ≤ val WuPaper.ClassicalFourthData.Bq 5091
    have hp : val WuPaper.ClassicalFourthData.Bq 5091 = (250856482169378:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5091 = 250856482169378 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5091 = (13091:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5091
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5092) ≤ val WuPaper.ClassicalFourthData.Bq 5092
    have hp : val WuPaper.ClassicalFourthData.Bq 5092 = (250870927244243:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5092 = 250870927244243 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5092 = (3273:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5092
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5093) ≤ val WuPaper.ClassicalFourthData.Bq 5093
    have hp : val WuPaper.ClassicalFourthData.Bq 5093 = (250885366416830:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5093 = 250885366416830 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5093 = (13093:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5093
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5094) ≤ val WuPaper.ClassicalFourthData.Bq 5094
    have hp : val WuPaper.ClassicalFourthData.Bq 5094 = (250899799689302:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5094 = 250899799689302 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5094 = (6547:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5094
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5095) ≤ val WuPaper.ClassicalFourthData.Bq 5095
    have hp : val WuPaper.ClassicalFourthData.Bq 5095 = (250914227063825:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5095 = 250914227063825 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5095 = (2619:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5095
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5096) ≤ val WuPaper.ClassicalFourthData.Bq 5096
    have hp : val WuPaper.ClassicalFourthData.Bq 5096 = (250928648542562:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5096 = 250928648542562 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5096 = (1637:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5096
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5097) ≤ val WuPaper.ClassicalFourthData.Bq 5097
    have hp : val WuPaper.ClassicalFourthData.Bq 5097 = (250943064127674:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5097 = 250943064127674 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5097 = (13097:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5097
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5098) ≤ val WuPaper.ClassicalFourthData.Bq 5098
    have hp : val WuPaper.ClassicalFourthData.Bq 5098 = (250957473821324:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5098 = 250957473821324 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5098 = (6549:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5098
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5099) ≤ val WuPaper.ClassicalFourthData.Bq 5099
    have hp : val WuPaper.ClassicalFourthData.Bq 5099 = (250971877625671:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5099 = 250971877625671 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5099 = (13099:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5099
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5100) ≤ val WuPaper.ClassicalFourthData.Bq 5100
    have hp : val WuPaper.ClassicalFourthData.Bq 5100 = (250986275542875:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5100 = 250986275542875 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5100 = (131:ℝ)/40 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5100
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5101) ≤ val WuPaper.ClassicalFourthData.Bq 5101
    have hp : val WuPaper.ClassicalFourthData.Bq 5101 = (251000667575095:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5101 = 251000667575095 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5101 = (13101:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5101
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5102) ≤ val WuPaper.ClassicalFourthData.Bq 5102
    have hp : val WuPaper.ClassicalFourthData.Bq 5102 = (251015053724488:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5102 = 251015053724488 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5102 = (6551:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5102
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5103) ≤ val WuPaper.ClassicalFourthData.Bq 5103
    have hp : val WuPaper.ClassicalFourthData.Bq 5103 = (251029433993212:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5103 = 251029433993212 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5103 = (13103:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5103
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_318
