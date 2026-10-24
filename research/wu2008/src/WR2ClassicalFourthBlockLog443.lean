import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints443
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_443 (j : Fin 16) (hj : 16*443+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*443+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*443+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7088) ≤ val WuPaper.ClassicalFourthData.Bq 7088
    have hp : val WuPaper.ClassicalFourthData.Bq 7088 = (270299332271468:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7088 = 270299332271468 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7088 = (943:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7088
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7089) ≤ val WuPaper.ClassicalFourthData.Bq 7089
    have hp : val WuPaper.ClassicalFourthData.Bq 7089 = (270305325694615:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7089 = 270305325694615 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7089 = (15089:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7089
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7090) ≤ val WuPaper.ClassicalFourthData.Bq 7090
    have hp : val WuPaper.ClassicalFourthData.Bq 7090 = (270311316167716:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7090 = 270311316167716 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7090 = (1509:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7090
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7091) ≤ val WuPaper.ClassicalFourthData.Bq 7091
    have hp : val WuPaper.ClassicalFourthData.Bq 7091 = (270317303691747:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7091 = 270317303691747 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7091 = (15091:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7091
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7092) ≤ val WuPaper.ClassicalFourthData.Bq 7092
    have hp : val WuPaper.ClassicalFourthData.Bq 7092 = (270323288267682:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7092 = 270323288267682 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7092 = (3773:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7092
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7093) ≤ val WuPaper.ClassicalFourthData.Bq 7093
    have hp : val WuPaper.ClassicalFourthData.Bq 7093 = (270329269896497:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7093 = 270329269896497 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7093 = (15093:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7093
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7094) ≤ val WuPaper.ClassicalFourthData.Bq 7094
    have hp : val WuPaper.ClassicalFourthData.Bq 7094 = (270335248579165:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7094 = 270335248579165 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7094 = (7547:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7094
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7095) ≤ val WuPaper.ClassicalFourthData.Bq 7095
    have hp : val WuPaper.ClassicalFourthData.Bq 7095 = (270341224316660:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7095 = 270341224316660 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7095 = (3019:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7095
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7096) ≤ val WuPaper.ClassicalFourthData.Bq 7096
    have hp : val WuPaper.ClassicalFourthData.Bq 7096 = (270347197109954:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7096 = 270347197109954 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7096 = (1887:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7096
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7097) ≤ val WuPaper.ClassicalFourthData.Bq 7097
    have hp : val WuPaper.ClassicalFourthData.Bq 7097 = (270353166960022:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7097 = 270353166960022 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7097 = (15097:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7097
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7098) ≤ val WuPaper.ClassicalFourthData.Bq 7098
    have hp : val WuPaper.ClassicalFourthData.Bq 7098 = (270359133867836:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7098 = 270359133867836 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7098 = (7549:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7098
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7099) ≤ val WuPaper.ClassicalFourthData.Bq 7099
    have hp : val WuPaper.ClassicalFourthData.Bq 7099 = (270365097834368:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7099 = 270365097834368 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7099 = (15099:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7099
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7100) ≤ val WuPaper.ClassicalFourthData.Bq 7100
    have hp : val WuPaper.ClassicalFourthData.Bq 7100 = (270371058860590:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7100 = 270371058860590 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7100 = (151:ℝ)/40 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7100
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7101) ≤ val WuPaper.ClassicalFourthData.Bq 7101
    have hp : val WuPaper.ClassicalFourthData.Bq 7101 = (270377016947474:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7101 = 270377016947474 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7101 = (15101:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7101
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7102) ≤ val WuPaper.ClassicalFourthData.Bq 7102
    have hp : val WuPaper.ClassicalFourthData.Bq 7102 = (270382972095990:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7102 = 270382972095990 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7102 = (7551:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7102
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7103) ≤ val WuPaper.ClassicalFourthData.Bq 7103
    have hp : val WuPaper.ClassicalFourthData.Bq 7103 = (270388924307110:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7103 = 270388924307110 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7103 = (15103:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7103
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_443
