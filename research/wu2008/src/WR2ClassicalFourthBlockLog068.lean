import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints068
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_068 (j : Fin 16) (hj : 16*68+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*68+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*68+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1088) ≤ val WuPaper.ClassicalFourthData.Bq 1088
    have hp : val WuPaper.ClassicalFourthData.Bq 1088 = (105893690544864:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1088 = 105893690544864 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1088 = (284:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1088
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1089) ≤ val WuPaper.ClassicalFourthData.Bq 1089
    have hp : val WuPaper.ClassicalFourthData.Bq 1089 = (105968527444958:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1089 = 105968527444958 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1089 = (9089:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1089
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1090) ≤ val WuPaper.ClassicalFourthData.Bq 1090
    have hp : val WuPaper.ClassicalFourthData.Bq 1090 = (106043330887807:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1090 = 106043330887807 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1090 = (909:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1090
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1091) ≤ val WuPaper.ClassicalFourthData.Bq 1091
    have hp : val WuPaper.ClassicalFourthData.Bq 1091 = (106118100891127:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1091 = 106118100891127 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1091 = (9091:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1091
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1092) ≤ val WuPaper.ClassicalFourthData.Bq 1092
    have hp : val WuPaper.ClassicalFourthData.Bq 1092 = (106192837472622:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1092 = 106192837472622 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1092 = (2273:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1092
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1093) ≤ val WuPaper.ClassicalFourthData.Bq 1093
    have hp : val WuPaper.ClassicalFourthData.Bq 1093 = (106267540649985:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1093 = 106267540649985 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1093 = (9093:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1093
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1094) ≤ val WuPaper.ClassicalFourthData.Bq 1094
    have hp : val WuPaper.ClassicalFourthData.Bq 1094 = (106342210440895:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1094 = 106342210440895 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1094 = (4547:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1094
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1095) ≤ val WuPaper.ClassicalFourthData.Bq 1095
    have hp : val WuPaper.ClassicalFourthData.Bq 1095 = (106416846863023:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1095 = 106416846863023 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1095 = (1819:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1095
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1096) ≤ val WuPaper.ClassicalFourthData.Bq 1096
    have hp : val WuPaper.ClassicalFourthData.Bq 1096 = (106491449934025:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1096 = 106491449934025 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1096 = (1137:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1096
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1097) ≤ val WuPaper.ClassicalFourthData.Bq 1097
    have hp : val WuPaper.ClassicalFourthData.Bq 1097 = (106566019671547:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1097 = 106566019671547 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1097 = (9097:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1097
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1098) ≤ val WuPaper.ClassicalFourthData.Bq 1098
    have hp : val WuPaper.ClassicalFourthData.Bq 1098 = (106640556093222:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1098 = 106640556093222 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1098 = (4549:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1098
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1099) ≤ val WuPaper.ClassicalFourthData.Bq 1099
    have hp : val WuPaper.ClassicalFourthData.Bq 1099 = (106715059216674:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1099 = 106715059216674 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1099 = (9099:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1099
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1100) ≤ val WuPaper.ClassicalFourthData.Bq 1100
    have hp : val WuPaper.ClassicalFourthData.Bq 1100 = (106789529059512:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1100 = 106789529059512 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1100 = (91:ℝ)/40 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1100
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1101) ≤ val WuPaper.ClassicalFourthData.Bq 1101
    have hp : val WuPaper.ClassicalFourthData.Bq 1101 = (106863965639336:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1101 = 106863965639336 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1101 = (9101:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1101
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1102) ≤ val WuPaper.ClassicalFourthData.Bq 1102
    have hp : val WuPaper.ClassicalFourthData.Bq 1102 = (106938368973733:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1102 = 106938368973733 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1102 = (4551:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1102
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1103) ≤ val WuPaper.ClassicalFourthData.Bq 1103
    have hp : val WuPaper.ClassicalFourthData.Bq 1103 = (107012739080279:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1103 = 107012739080279 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1103 = (9103:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1103
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_068
